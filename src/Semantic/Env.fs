module Semantic.Env

open System.Collections.Generic
open System.Linq

open Common.Span
open Util.MultiMap
open AST.AST
open Semantic
open Util

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

type internal FnScope =
    { Ty: Function
      Gen: Generic[]
      Name: Id }

type internal ClosureScope = { Closure: Closure; Ret: Type }

type internal ScopeData =
    | FnScope of FnScope
    | ClosureScope of ClosureScope
    | BlockScope
    | TypeScope
    | TopLevelScope

type internal TyInfo = { Def: Id; Ty: Type }

type internal VarInfo = { Def: Id; Mut: bool; Static: bool }

type internal Scope =
    { Ty: Dictionary<string, TyInfo>
      Var: Dictionary<string, VarInfo>
      Trait: Dictionary<string, Trait>
      Field: MultiMap<string, Id>
      Method: MultiMap<string, Id>
      Data: ScopeData }

    static member Create data =
        { Ty = Dictionary()
          Var = Dictionary()
          Trait = Dictionary()
          Field = MultiMap()
          Method = MultiMap()
          Data = data }

    static member Prelude =
        let scope = Scope.Create TopLevelScope

        for p in primitive do
            let name = p.Print()

            let info =
                { Ty = p
                  Def = { Sym = name; Span = Span.dummy } }

            scope.Ty[p.Print()] <- info

        scope

type internal Canonical =
    { Subst: Dictionary<int, Type>
      Pred: Dictionary<int, HashSet<Trait>> }

    static member New() =
        { Subst = Dictionary()
          Pred = Dictionary() }

type internal TypeEnvironment() =
    let unionFind = Dictionary<int, Type>()
    let traitImpl = Dictionary<Trait, ResizeArray<Scheme>>(HashIdentity.Reference)
    let predict = Dictionary<Type, HashSet<Trait>>()

    let mutable varId = 0
    let mutable genId = 0

    member _.NewTVar level span =
        let tvar =
            { Level = level
              Id = varId
              Span = span }

        varId <- varId + 1
        tvar

    member _.NewGenGroup() =
        let id = genId
        genId <- genId + 1
        id

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

        let addUnion (v: Var) t =
            union.Add(v.Id, t)

            if predict.ContainsKey(TVar v) then
                let tr = predict[TVar v]

                for tr in tr do
                    if not (this.HasTrait tr t) then
                        error.Add(TraitNotImpl(tr, t, span))

        let rec unify expect actual =
            let expect = normalize expect
            let actual = normalize actual

            match expect, actual with
            | p1, p2 when p1 = p2 -> ()
            | TNever, _
            | _, TNever -> ()
            | TVar v1 as t1, (TVar v2 as t2) ->
                if v1.Level > v2.Level then
                    addUnion v1 t2
                else if v1.Level = v2.Level then
                    if v1.Id > v2.Id then addUnion v1 t2 else addUnion v2 t1
                else
                    addUnion v2 t1

            | TVar v, ty
            | ty, TVar v ->
                match ty.FindTVar() |> Seq.tryFind ((=) v) with
                | Some _ -> error.Add(FailToUnify(expect, actual, span))
                | None -> addUnion v ty

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

            | TSlice t1, TSlice t2 -> unify t1 t2

            | _, _ -> error.Add(TypeMismatch(expect, actual, span))

        unify expect actual

        if error.Count > 0 then Error(error.ToArray()) else Ok union

    member _.AddUnion var ty = unionFind.Add(var, ty)

    member _.AddBound ty tr =
        if predict.ContainsKey ty then
            predict[ty].Add tr |> ignore
        else
            predict.Add(ty, HashSet([ tr ]))

    member _.ApplyCanon canon = 1

    member this.Instantiate scm level span =
        if scm.Generic.Length = 0 then
            scm.Type
        else
            let inst gen =
                let var = this.NewTVar level span |> TVar
                let gen = TGen gen

                if predict.ContainsKey gen then
                    let bound = HashSet(predict[gen])
                    predict.Add(var, bound)

                var

            let inst = Array.map inst scm.Generic
            scm.Type.Instantiate scm.Generic inst

    member this.Generalize fnTy level =
        let inScope (v: Var) = v.Level > level

        let param = Array.map this.NormalizeTy fnTy.Param
        let ret = this.NormalizeTy fnTy.Ret

        let newTVar = param |> Seq.map _.FindTVar() |> Seq.concat

        let retTVar =
            match ret with
            | TFn f -> f.Param |> Array.map _.FindTVar() |> Seq.concat
            | _ -> Seq.empty

        let group = this.NewGenGroup()

        let makeGen (idx, var: Var) =
            let gen = { Id = idx; GroupId = group; Sym = "" }
            this.AddUnion var.Id (TGen gen)
            var, gen

        let map =
            Seq.append newTVar retTVar
            |> Seq.filter inScope
            |> Seq.distinct
            |> Seq.indexed
            |> Seq.map makeGen
            |> Map.ofSeq

        let toGen t =
            match Map.tryFind t map with
            | Some t -> TGen t
            | None -> TVar t

        let param = Array.map (fun (ty: Type) -> ty.Walk toGen TGen) param
        let ret = ret.Walk toGen TGen

        let generic = map.Values.ToArray()
        let ty = { Param = param; Ret = ret }

        { Generic = generic
          Type = TFn ty
          Pred = [||] }

    member this.ImplTrait trait_ scm =
        if traitImpl.ContainsKey trait_ then
            let ty = this.Instantiate scm 0 Span.dummy
            let value = traitImpl[trait_]

            let rec overlap prev =
                let prevTy = this.Instantiate prev 0 Span.dummy

                match this.Unify prevTy ty Span.dummy with
                | Ok _ -> Some prev
                | Error _ -> None

            let res = Util.pick overlap value

            match res with
            | None ->
                value.Add scm
                Ok()
            | Some prev -> Error prev

        else
            let value = ResizeArray()
            value.Add scm
            traitImpl[trait_] <- value
            Ok()

    member this.HasTrait trait_ ty =
        let hasTy =
            if predict.ContainsKey ty then
                true
            else
                predict.Add(ty, HashSet())
                false

        if hasTy && predict[ty].Contains trait_ then
            true
        else if not (traitImpl.ContainsKey trait_) && ty.IsVar then
            predict[ty].Add trait_ |> ignore
            true
        else if not (traitImpl.ContainsKey trait_) then
            false
        else
            let value = traitImpl[trait_]

            let rec overlap prev =
                let prevTy = this.Instantiate prev 0 Span.dummy

                match this.Unify prevTy ty Span.dummy with
                | Ok _ -> Some prev
                | Error _ -> None

            let res = Util.pick overlap value

            match res with
            | None -> false
            | Some _ ->
                predict[ty].Add trait_ |> ignore
                true

type internal Environment(error: ResizeArray<Error>) =
    let scope = Stack([| Scope.Prelude |])

    let tyEnv = TypeEnvironment()

    let sema =
        { Binding = Dictionary(HashIdentity.Reference)
          DeclTy = Dictionary(HashIdentity.Reference)
          ExprTy = Dictionary(HashIdentity.Reference)
          Struct = Dictionary(HashIdentity.Reference)
          Enum = Dictionary(HashIdentity.Reference)
          Capture = MultiMap(HashIdentity.Reference)
          Trait = Dictionary(HashIdentity.Reference)
          Module =
            { Ty = Map.empty
              Var = Map.empty
              Module = Map.empty } }

    member _.NewTVar span = tyEnv.NewTVar scope.Count span

    member _.NewGenGroup = tyEnv.NewGenGroup

    member _.EnterScope data =
        let s = Scope.Create data

        scope.Push s

    member _.ExitScope() =
        let last = scope.Pop()

        match last.Data with
        | FnScope { Ty = ty; Gen = gen; Name = name } ->
            if gen.Length = 0 then
                let ty = tyEnv.Generalize ty scope.Count
                sema.DeclTy[name] <- ty
            else
                let ty = tyEnv.NormalizeTy(TFn ty)

                sema.DeclTy[name] <-
                    { Generic = gen
                      Type = ty
                      Pred = [||] }
        | _ -> ()

    member _.Pick picker =
        let rec loop (i: int) =
            match picker (scope.ElementAt i) with
            | None -> if i + 1 = scope.Count then None else loop (i + 1)
            | res -> res

        loop 0

    member _.RegisterTy (id: Id) (ty: Type) =
        let curr = scope.Peek()

        if curr.Ty.ContainsKey id.Sym then
            error.Add(DuplicateDefinition(id, curr.Ty[id.Sym].Def))

        curr.Ty[id.Sym] <- { Ty = ty; Def = id }

    member this.GetTy sym =
        let pickId scope =
            if scope.Ty.ContainsKey sym then
                let id = scope.Ty[sym]
                Some id
            else
                None

        this.Pick pickId

    member _.RegisterVar (mayShadow: bool) (info: VarInfo) (scm: Scheme) =
        let curr = scope.Peek()

        if not mayShadow && curr.Var.ContainsKey info.Def.Sym then
            error.Add(DuplicateDefinition(info.Def, curr.Var[info.Def.Sym].Def))

        curr.Var[info.Def.Sym] <- info

        sema.DeclTy[info.Def] <- scm

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
                { Generic = ty.Generic
                  Type = variant
                  Pred = [||] }

        sema.Enum[decl.Name] <- ty

    member _.RegisterTrait(trait_: Trait) =
        let curr = scope.Peek()
        let name = trait_.Name.Sym

        if curr.Trait.ContainsKey name then
            error.Add(DuplicateDefinition(trait_.Name, curr.Trait[name].Name))

        curr.Trait[name] <- trait_

        for KeyValue(name, _) in trait_.Method do
            curr.Method.Add name trait_.Name

        sema.Trait.Add(trait_.Name, trait_)

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
            let scm = sema.DeclTy[def]

            tyEnv.Instantiate scm scope.Count id.Span |> Some

    member _.GetVarTyWithCapture(id: Id) =
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

            sema.Binding.Add(id, def)

            let scm = sema.DeclTy[def]

            tyEnv.Instantiate scm scope.Count id.Span |> Some

    member _.GetStruct id = sema.Struct[id]

    member this.FindField ty field span =
        let ty = tyEnv.NormalizeTy ty

        let res =
            match ty with
            | TStruct s ->
                let stru = sema.Struct[s.Name]

                match Map.tryFind field stru.Field with
                | Some f -> f.Instantiate stru.Generic s.Generic |> Some
                | None -> None
            | TVar _ ->
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
            | _ -> None

        match res with
        | Some r -> r
        | None ->
            error.Add(UndefinedField(span, field))
            TNever

    member this.GetTrait name =
        let findTrait scope =
            if scope.Trait.ContainsKey name then
                Some scope.Trait[name]
            else
                None

        this.Pick findTrait

    member _.ImplTrait (t: Trait) scm span =
        let ty = tyEnv.Instantiate scm 0 Span.dummy

        let super = ResizeArray(t.Super)
        let mutable idx = 0

        while idx < super.Count do
            let t = super[idx]

            if not (tyEnv.HasTrait t ty) then
                error.Add(TraitNotImpl(t, ty, span))

            super.AddRange(t.Super)

            idx <- idx + 1

        match tyEnv.ImplTrait t scm with
        | Ok() -> ()
        | Error prev -> error.Add(OverlapImpl(t, scm, prev, span))

    member _.AddBound ty tr =
        let super = ResizeArray(tr.Super)
        let mutable idx = 0

        while idx < super.Count do
            let tr = super[idx]
            tyEnv.AddBound ty tr
            super.AddRange(tr.Super)
            idx <- idx + 1

        tyEnv.AddBound ty tr

    member this.FindMethod ty field span =
        let ty = tyEnv.NormalizeTy ty

        let findTrait scope =
            match scope.Method.Get field with
            | None -> None
            | Some id ->
                let tr = sema.Trait[id]

                if tyEnv.HasTrait tr ty then Some tr else None

        let trait_ = this.Pick findTrait

        match trait_ with
        | None -> None
        | Some t -> Some t.Method[field]

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

    member _.ToNever(name: Id) =
        let toNever t =
            let t = tyEnv.NormalizeTy(TVar t)

            match t with
            | TVar t -> if t.Level > scope.Count then TNever else TVar t
            | _ -> t

        let scm = sema.DeclTy[name]

        let ty =
            match scm.Type with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        let ret = ty.Ret.Walk toNever TGen

        let ty = { ty with Ret = ret }

        sema.DeclTy[name] <- { scm with Type = TFn ty }

    member _.GetSema = sema
