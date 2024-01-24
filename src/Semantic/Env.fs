module Semantic.Env

open System.Collections.Generic
open System.Linq

open Common.Span
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

type internal Environment(error: ResizeArray<Error>) =
    let scope = Stack([| Scope.Prelude |])

    /// union find set
    let ufs = Dictionary<int, Type>()

    let pred = MultiMap<int, Type>()

    let mutable tVarId = 0

    member _.NewTVar sym span =
        let tvar =
            { Level = scope.Count
              Id = tVarId
              Sym = sym
              Span = span }

        tVarId <- tVarId + 1

        tvar

    member _.EnterScope data =
        let s = Scope.Create data

        scope.Push s

    member _.Current = scope.Peek()

    member _.ExitScope() = scope.Pop() |> ignore

    member _.Pick picker =
        let rec loop (i: int) =
            match picker (scope.ElementAt(i)) with
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

    member _.RegisterVar (mayShadow: bool) (info: VarInfo) =
        let curr = scope.Peek()

        if not mayShadow && curr.Var.ContainsKey info.Def.Sym then
            error.Add(DuplicateDefinition info.Def)

        curr.Var[info.Def.Sym] <- info

    member _.RegisterField(decl: StructDecl) =
        for field in decl.Field do
            scope.Peek().Field.Add field.Name.Sym decl.Name

    member _.GetVarInfoWithCapture(id: Id) =
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
            else if i = scope.Count then
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

        resolveVar [||] true 0

    member this.GetVarInfo(id: Id) =
        let pickId scope =
            if scope.Var.ContainsKey id.Sym then
                let id = scope.Var[id.Sym]
                Some id
            else
                None

        this.Pick pickId

    member this.NormalizeTy ty =
        let onvar (tvar: Var) =
            if ufs.ContainsKey tvar.Id then
                // we don't need to recursively find tvar here
                // all the work has been done in unify
                let p = this.NormalizeTy ufs[tvar.Id]
                ufs[tvar.Id] <- p
                p
            else
                TVar tvar

        ty.Walk onvar

    member this.Unify expect actual span =
        let expect = this.NormalizeTy expect
        let actual = this.NormalizeTy actual

        let rec find k =
            let p = ufs[k]

            match p with
            | TVar v ->
                let p = if ufs.ContainsKey v.Id then find v.Id else TVar v
                ufs[k] <- p
                p
            | p -> p

        match expect, actual with
        | p1, p2 when p1 = p2 -> ()
        | TNever, _
        | _, TNever -> ()
        | TVar v1 as t1, (TVar v2 as t2) ->
            if v1.Level > v2.Level then
                ufs.Add(v1.Id, t2)
            else if v1.Level = v2.Level then
                if v1.Id > v2.Id then
                    ufs.Add(v1.Id, t2)
                else
                    ufs.Add(v2.Id, t1)
            else
                ufs.Add(v2.Id, t1)

        | TVar v, ty
        | ty, TVar v ->
            match ty.FindTVar() |> Seq.tryFind ((=) v) with
            | Some _ -> error.Add(FailToUnify(expect, actual, span))
            | None -> ufs.Add(v.Id, ty)

        | TFn f1, TFn f2 ->
            if f1.Param.Length <> f2.Param.Length then
                error.Add(TypeMismatch(expect, actual, span))
            else
                for (p1, p2) in (Array.zip f1.Param f2.Param) do
                    this.Unify p1 p2 span

                this.Unify f1.Ret f2.Ret span

        | TRef r1, TRef r2 -> this.Unify r1 r2 span

        | TStruct(id1, v1), TStruct(id2, v2)
        | TEnum(id1, v1), TEnum(id2, v2) when id1 = id2 ->
            for (v1, v2) in Array.zip v1 v2 do
                this.Unify v1 v2 span

        | TTuple t1, TTuple t2 ->
            if t1.Length <> t2.Length then
                error.Add(TupleLengthMismatch(span, t1.Length, t2.Length))
            else
                for (t1, t2) in Array.zip t1 t2 do
                    this.Unify t1 t2 span

        | _, _ -> error.Add(TypeMismatch(expect, actual, span))

    member this.FinishScope() = scope.Pop() |> ignore

    member this.Generalize tvar fnTy =
        let inScope (v: Var) = v.Level > scope.Count

        let param = Array.map this.NormalizeTy fnTy.Param
        let fromRet = fnTy.Ret.FindTVar() |> Set.ofSeq
        let ret = this.NormalizeTy fnTy.Ret

        let newTVar = param |> Seq.map _.FindTVar() |> Seq.concat

        let tvar =
            Seq.append newTVar (ret.FindTVar())
            |> Seq.filter inScope
            |> Seq.filter (fun v -> not (Set.contains v fromRet))
            |> Seq.append tvar
            |> Seq.distinct
            |> Array.ofSeq

        tvar, { Param = param; Ret = ret }

    member this.Instantiate span tvar (fn: Function) =
        let map = tvar |> Array.map (fun v -> v, this.NewTVar None span) |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TVar t
            | Some t -> TVar t

        { Ret = fn.Ret.Walk getMap
          Param = fn.Param |> Array.map _.Walk(getMap) }
