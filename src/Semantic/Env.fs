module Semantic.Env

open System.Collections.Generic
open System.Linq

open Util.MultiMap
open AST.AST
open Semantic

let internal primitive =
    [| TInt(true, I8)
       TInt(false, I8)
       TInt(true, I32)
       TInt(false, I32)
       TInt(true, I64)
       TInt(false, I64)
       TInt(true, ISize)
       TInt(false, ISize)
       TBool
       TFloat(F32)
       TFloat(F64)
       TChar
       TString |]

type internal FnScope = { Ret: Type }
type internal ClosureScope = { Closure: Closure; Ret: Type }

type internal ScopeData =
    | FnScope of FnScope
    | ClosureScope of ClosureScope
    | BlockScope
    | TypeScope
    | TopLevelScope

type internal VarInfo = { Def: Id; Mut: bool; Static: bool }

type internal Scope =
    { Ty: Dictionary<string, Type>
      Var: Dictionary<string, VarInfo>
      Field: MultiMap<string, Id>
      Data: ScopeData }

    static member Create data =
        { Ty = Dictionary()
          Var = Dictionary()
          Field = MultiMap()
          Data = data }

    static member Prelude =
        let scope = Scope.Create TopLevelScope

        for p in primitive do
            scope.Ty[p.Print()] <- p

        scope

type internal TypeEnvironment() =
    let unionFind = Dictionary<int, Type>()
    let traitImpl = Dictionary<Trait, ResizeArray<Scheme>>()

    member this.Impl trait_ scm =
        if traitImpl.ContainsKey trait_ then
            let value = traitImpl[trait_]

            for s in value do
                if s = scm then
                    OverlapIml(trait_, s, scm) |> ignore

            value.Add scm

        else
            let value = ResizeArray()
            value.Add scm
            traitImpl[trait_] <- value

    member this.NormalizeTy(ty: Type) =
        let onvar (tvar: Var) =
            if unionFind.ContainsKey tvar.Id then
                let p = this.NormalizeTy unionFind[tvar.Id]
                unionFind[tvar.Id] <- p
                p
            else
                TVar tvar

        ty.Walk onvar TGen

    member this.Unify expect actual span =
        let union = Dictionary<int, Type>()
        let error = ResizeArray()

        let normalize ty =
            let ty = this.NormalizeTy ty

            let rec calc ty =
                match ty with
                | TVar t -> if union.ContainsKey t.Id then calc union[t.Id] else ty
                | _ -> ty

            calc ty

        let rec unify expect actual =
            let expect = normalize expect
            let actual = normalize actual

            match expect, actual with
            | p1, p2 when p1 = p2 -> ()
            | TNever, _
            | _, TNever -> ()
            | TVar v1 as t1, (TVar v2 as t2) ->
                if v1.Level > v2.Level then
                    union.Add(v1.Id, t2)
                else if v1.Level = v2.Level then
                    if v1.Id > v2.Id then
                        union.Add(v1.Id, t2)
                    else
                        union.Add(v2.Id, t1)
                else
                    union.Add(v2.Id, t1)

            | TVar v, ty
            | ty, TVar v ->
                match ty.FindTVar() |> Seq.tryFind ((=) v) with
                | Some _ -> error.Add(FailToUnify(expect, actual, span))
                | None -> union.Add(v.Id, ty)

            | TFn f1, TFn f2 ->
                if f1.Param.Length <> f2.Param.Length then
                    error.Add(TypeMismatch(expect, actual, span))
                else
                    for (p1, p2) in (Array.zip f1.Param f2.Param) do
                        unify p1 p2

                    unify f1.Ret f2.Ret

            | TRef r1, TRef r2 -> unify r1 r2

            | TStruct a1, TStruct a2
            | TEnum a1, TEnum a2 when a1.Name = a2.Name ->
                for (v1, v2) in Array.zip a1.Generic a2.Generic do
                    unify v1 v2

            | TTuple t1, TTuple t2 ->
                if t1.Length <> t2.Length then
                    error.Add(LengthMismatch(span, t1.Length, t2.Length))
                else
                    for (t1, t2) in Array.zip t1 t2 do
                        unify t1 t2

            | _, _ -> error.Add(TypeMismatch(expect, actual, span))

        unify expect actual

        if error.Count > 0 then Error(error.ToArray()) else Ok union

    member _.AddUnion var ty = unionFind.Add(var, ty)

type internal Environment(error: ResizeArray<Error>) =
    let scope = Stack([| Scope.Prelude |])

    let tyEnv = TypeEnvironment()

    let sema =
        { Binding = Dictionary(HashIdentity.Reference)
          Expr = Dictionary(HashIdentity.Reference)
          Struct = Dictionary(HashIdentity.Reference)
          Enum = Dictionary(HashIdentity.Reference)
          Capture = MultiMap(HashIdentity.Reference)
          Module =
            { Ty = Map.empty
              Var = Map.empty
              Module = Map.empty } }

    let mutable varId = 0
    let mutable boundId = 0

    member _.NewTVar span =
        let tvar =
            { Level = scope.Count
              Id = varId
              Span = span }

        varId <- varId + 1

        tvar

    member _.NewGeneric sym =
        let bound = { Id = boundId; Sym = sym }

        boundId <- boundId + 1

        bound

    member _.EnterScope data =
        let s = Scope.Create data

        scope.Push s

    member _.Current = scope.Peek()

    member _.ExitScope() = scope.Pop() |> ignore

    member _.Pick picker =
        let rec loop (i: int) =
            match picker (scope.ElementAt i) with
            | None -> if i + 1 = scope.Count then None else loop (i + 1)
            | res -> res

        loop 0

    member _.RegisterTy (id: Id) (ty: Type) =
        let curr = scope.Peek()

        if curr.Ty.ContainsKey id.Sym then
            error.Add(DuplicateDefinition id)

        curr.Ty[id.Sym] <- ty

    member this.GetTy(id: Id) =
        let pickId scope =
            if scope.Ty.ContainsKey id.Sym then
                let id = scope.Ty[id.Sym]
                Some id
            else
                None

        this.Pick pickId

    member _.RegisterVar (mayShadow: bool) (info: VarInfo) (scm: Scheme) =
        let curr = scope.Peek()

        if not mayShadow && curr.Var.ContainsKey info.Def.Sym then
            error.Add(DuplicateDefinition info.Def)

        curr.Var[info.Def.Sym] <- info

        sema.Binding[info.Def] <- scm

    member _.RegisterStruct (decl: StructDecl) (ty: Struct) =
        for field in decl.Field do
            scope.Peek().Field.Add field.Name.Sym decl.Name

        sema.Struct[decl.Name] <- ty

    member this.RegisterEnum (decl: EnumDecl) (ty: Enum) =
        let gen = Array.map TGen ty.Generic

        for v in decl.Variant do
            let payload = ty.Variant[v.Name.Sym]

            let variant = TEnum { Name = decl.Name; Generic = gen }

            let variant =
                if payload.Length = 0 then
                    variant
                else
                    TFn { Param = payload; Ret = variant }

            this.RegisterVar
                true
                { Mut = false
                  Static = true
                  Def = v.Name }
                { Generic = ty.Generic; Ty = variant }

        sema.Enum[decl.Name] <- ty

    member this.GetVarInfo(id: Id) =
        let pickId scope =
            if scope.Var.ContainsKey id.Sym then
                let id = scope.Var[id.Sym]
                Some id
            else
                None

        this.Pick pickId

    member this.GetVarTy(id: Id) =
        let pickId scope =
            if scope.Var.ContainsKey id.Sym then
                let id = scope.Var[id.Sym]
                Some id
            else
                None

        match this.Pick pickId with
        | None -> None
        | Some { Def = def } ->
            let scm = sema.Binding[def]

            this.Instantiate scm id.Span |> Some

    member this.GetVarTyWithCapture(id: Id) =
        let rec resolveVar captured canCapture (i: int) =
            let curr = scope.ElementAt i

            if curr.Var.ContainsKey id.Sym then
                let info = curr.Var[id.Sym]

                let captured =
                    if canCapture && not info.Static then
                        captured
                    else
                        if not info.Static then
                            error.Add(CaptureDynamic id)

                        [||]

                Some(info.Def, captured)
            else if i + 1 = scope.Count then
                None
            else
                let captured =
                    match curr.Data with
                    | ClosureScope { Closure = cl } -> Array.append captured [| cl |]
                    | _ -> captured

                let canCapture =
                    match curr.Data with
                    | FnScope _ -> false
                    | _ -> canCapture

                resolveVar captured canCapture (i + 1)

        match resolveVar [||] true 0 with
        | None -> None
        | Some(def, captured) ->
            for c in captured do
                sema.Capture.Add c def

            let scm = sema.Binding[def]

            this.Instantiate scm id.Span |> Some

    member this.HasField ty field span =
        match ty with
        | TStruct s ->
            let stru = sema.Struct[s.Name]

            match Map.tryFind field stru.Field with
            | Some f -> f.Instantiate stru.Generic s.Generic |> Some
            | None -> None
        | _ ->
            let findStruct scope =
                match scope.Field.Get field with
                | None -> None
                | Some id -> Some sema.Struct[id]

            let stru = this.Pick findStruct

            match stru with
            | Some s ->
                let inst = Array.map (fun _ -> TVar(this.NewTVar span)) s.Generic
                this.Unify (TStruct { Name = s.Name; Generic = inst }) ty span
                s.Field[field].Instantiate s.Generic inst |> Some
            | None -> None

    member _.NormalizeTy ty = tyEnv.NormalizeTy ty

    member _.Unify expect actual span =
        let res = tyEnv.Unify expect actual span

        match res with
        | Ok union ->
            for KeyValue(var, ty) in union do
                tyEnv.AddUnion var ty
        | Error unionError ->
            for e in unionError do
                error.Add e

    member _.FinishScope() = scope.Pop() |> ignore

    member this.Generalize name generic fnTy =
        let inScope (v: Var) = v.Level > scope.Count

        let param = Array.map tyEnv.NormalizeTy fnTy.Param
        let ret = tyEnv.NormalizeTy fnTy.Ret

        let newTVar = param |> Seq.map _.FindTVar() |> Seq.concat

        let retTVar =
            match ret with
            | TFn f -> f.Param |> Array.map _.FindTVar() |> Seq.concat
            | _ -> Seq.empty

        let makeGen (var: Var) =
            let gen = this.NewGeneric None
            tyEnv.AddUnion var.Id (TGen gen)
            var, gen

        let map =
            Seq.append newTVar retTVar
            |> Seq.filter inScope
            |> Seq.distinct
            |> Seq.map makeGen
            |> Map.ofSeq

        let toBound t =
            match Map.tryFind t map with
            | Some t -> TGen t
            | None -> TVar t

        let param = Array.map (fun (ty: Type) -> ty.Walk toBound TGen) param
        let ret = ret.Walk toBound TGen

        let generic = map.Values.ToArray() |> Array.append generic
        let ty = { Param = param; Ret = ret }

        sema.Binding[name] <- { Generic = generic; Ty = TFn ty }

    member this.Instantiate scm span =
        if scm.Generic.Length = 0 then
            scm.Ty
        else
            let inst = Array.map (fun _ -> TVar(this.NewTVar span)) scm.Generic
            scm.Ty.Instantiate scm.Generic inst

    member _.ToNever(name: Id) =
        let toNever t =
            let t = tyEnv.NormalizeTy(TVar t)

            match t with
            | TVar t -> if t.Level > scope.Count then TNever else TVar t
            | _ -> t

        let scm = sema.Binding[name]

        let ty =
            match scm.Ty with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        let ret = ty.Ret.Walk toNever TGen

        let ty = { ty with Ret = ret }

        sema.Binding[name] <- { scm with Ty = TFn ty }

    member _.GetSema = sema
