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

type internal NormalConstraint =
    { Expect: Type
      Actual: Type
      Span: Span }

type internal Constraint =
    | CNormal of NormalConstraint
    | CDeref of NormalConstraint

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
      Constr: ResizeArray<Constraint>
      Data: ScopeData }

    static member Create data =
        { Ty = Dictionary()
          Var = Dictionary()
          Field = MultiMap()
          Constr = ResizeArray()
          Data = data }

    static member Prelude =
        let scope = Scope.Create TopLevelScope

        for p in primitive do
            scope.Ty[p.Print()] <- p

        scope

type internal Environment(error: ResizeArray<Error>) =
    let scope = Stack([| Scope.Prelude |])

    // union find set
    let union = Dictionary<Var, Type>()

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

        curr.Ty.Add(id.Sym, ty)

    member this.GetTy(id: Id) =
        let pickId scope =
            if scope.Ty.ContainsKey id.Sym then
                let id = scope.Ty[id.Sym]
                Some id
            else
                None

        this.Pick pickId

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

    member _.AddConstr constr = scope.Peek().Constr.Add constr

    member this.Find k =
        if union.ContainsKey k then
            let p = union[k]

            match p with
            | TVar v ->
                let p = this.Find v
                union[k] <- p
                p
            | p -> p
        else
            TVar k

    member this.TryFind k =
        if union.ContainsKey k then Some(this.Find k) else None

    member this.ResolveTy ty =
        let onvar tvar =
            if union.ContainsKey tvar then
                let p = this.ResolveTy union[tvar]
                union[tvar] <- p
                p
            else
                TVar tvar

        ty.Walk onvar

    /// unify last scope then exit
    member this.FinishScope() =
        let rec unifyNormal c deref =
            let addUnion v ty =
                match this.TryFind v with
                | None -> union[v] <- ty
                | Some prev ->
                    unifyNormal
                        { Expect = ty
                          Actual = prev
                          Span = c.Span }
                        deref

                    union[v] <- this.ResolveTy prev

            match c.Expect, c.Actual with
            | p1, p2 when p1 = p2 -> ()
            | TVar v1 as t1, (TVar v2 as t2) ->
                if v1.Level > v2.Level then
                    addUnion v1 t2
                else if v1.Level = v2.Level then
                    if v1.Id > v2.Id then addUnion v1 t2 else addUnion v2 t1
                else
                    addUnion v2 t1
            | TVar v, ty
            | ty, TVar v ->
                match ty.FindTVar |> Seq.tryFind ((=) v) with
                | Some _ -> error.Add(FailToUnify(c.Expect, c.Actual, c.Span))
                | None -> addUnion v ty

            | TFn f1, TFn f2 ->
                if f1.Param.Length <> f2.Param.Length then
                    error.Add(TypeMismatch(c.Expect, c.Actual, c.Span))
                else
                    for (p1, p2) in (Array.zip f1.Param f2.Param) do
                        unifyNormal
                            { Expect = p1
                              Actual = p2
                              Span = c.Span }
                            deref

                    unifyNormal
                        { Expect = f1.Ret
                          Actual = f2.Ret
                          Span = c.Span }
                        false

            | TRef r1, TRef r2 ->
                unifyNormal
                    { Expect = r1
                      Actual = r2
                      Span = c.Span }
                    false

            | TRef r, t
            | t, TRef r when deref ->
                unifyNormal
                    { Expect = r.StripRef
                      Actual = t
                      Span = c.Span }
                    false

            | TNever, _
            | _, TNever -> ()
            | TStruct(id1, v1), TStruct(id2, v2)
            | TEnum(id1, v1), TEnum(id2, v2) when id1 = id2 ->
                for (v1, v2) in Array.zip v1 v2 do
                    unifyNormal
                        { Expect = v1
                          Actual = v2
                          Span = c.Span }
                        false

            | TTuple t1, TTuple t2 ->
                if t1.Length <> t2.Length then
                    error.Add(TupleLengthMismatch(c.Span, t1.Length, t2.Length))
                else
                    for (t1, t2) in Array.zip t1 t2 do
                        unifyNormal
                            { Expect = t1
                              Actual = t2
                              Span = c.Span }
                            false
            | _, _ -> error.Add(TypeMismatch(c.Expect, c.Actual, c.Span))

        for c in scope.Peek().Constr do
            match c with
            | CNormal c -> unifyNormal c false
            | CDeref c -> unifyNormal c true

        scope.Pop() |> ignore

    member this.Generalize tvar fnTy =
        let inScope (v: Var) = v.Level > scope.Count

        let param = Array.map this.ResolveTy fnTy.Param
        let fromRet = fnTy.Ret.FindTVar |> Set.ofSeq
        let ret = this.ResolveTy fnTy.Ret

        let newTVar = param |> Seq.map _.FindTVar |> Seq.concat

        let tvar =
            Seq.append newTVar (ret.FindTVar)
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
