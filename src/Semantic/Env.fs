module internal Semantic.Env

open System.Collections.Generic
open System.Linq

open Common.Span
open Common.MultiMap
open Common.Util
open Syntax.AST
open Semantic

let primitive =
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

type FnScope =
    { Param: Type[]
      Ret: Type
      Fixed: bool
      Name: Id }

type ClosureScope = { Closure: Closure; Ret: Type }
type MethodScope = { Self: Type; Ret: Type }

type AdtScope = { Self: Type }

type ScopeData =
    | FnScope of FnScope
    | ClosureScope of ClosureScope
    | BlockScope
    | AdtScope of AdtScope
    | TraitScope of AdtScope
    | ImplScope of AdtScope
    | MethodScope of MethodScope
    | TypeScope
    | TopLevelScope

type TyInfo = { Def: Id; Ty: Type }

type VarInfo = { Def: Id; Mut: bool; Static: bool }

type Scope =
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

type Obligation =
    { Pred: Pred
      TVar: Var[]
      Span: Span }

    static member FromPred span (pred: Pred) =
        let tvar =
            pred.Type |> Array.map _.FindTVar() |> Array.map Array.ofSeq |> Array.concat

        { Pred = pred
          TVar = tvar
          Span = span }

type private TraitImpl =
    { Generic: Generic[]
      Pred: Pred[]
      Type: Type[] }

type Environment(sema: SemanticInfo, error: ResizeArray<Error>) =
    let scope = Stack([| Scope.Prelude |])

    let unionFind = Dictionary<int, Type>()
    let traitImpl = Dictionary<Trait, ResizeArray<TraitImpl>>(HashIdentity.Reference)
    let pending = Dictionary<Pred, Obligation>()
    let predCache = Dictionary<Pred, Type[]>()

    let mutable varId = 0
    let mutable genId = 0

    member _.NewTVar span =
        let tvar =
            { Level = scope.Count
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

    member this.NormalizeTyWith (subst: Dictionary<int, Type>) (ty: Type) =
        let ty = this.NormalizeTy ty

        let rec calc ty =
            match ty with
            | TVar t -> if subst.ContainsKey t.Id then calc subst[t.Id] else ty
            | _ -> ty

        calc ty

    member this.UnifyInner expect actual span =
        let union = Dictionary<int, Type>()
        let error = ResizeArray()

        let rec unify expect actual =
            let expect = this.NormalizeTyWith union expect
            let actual = this.NormalizeTyWith union actual

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
                    for p1, p2 in (Array.zip f1.Param f2.Param) do
                        unify p1 p2

                    unify f1.Ret f2.Ret

            | TRef r1, TRef r2 -> unify r1 r2

            | TStruct a1, TStruct a2
            | TEnum a1, TEnum a2 when a1.Name = a2.Name ->
                for v1, v2 in Array.zip a1.Generic a2.Generic do
                    unify v1 v2

            | TTuple t1, TTuple t2 ->
                if t1.Length <> t2.Length then
                    error.Add(ParamLenMismatch(span, t1.Length, t2.Length))
                else
                    for t1, t2 in Array.zip t1 t2 do
                        unify t1 t2

            | TSlice t1, TSlice t2 -> unify t1 t2

            | _, _ -> error.Add(TypeMismatch(expect, actual, span))

        unify expect actual

        if error.Count > 0 then Error(error.ToArray()) else Ok union

    member this.Unify expect actual span =
        let res = this.UnifyInner expect actual span

        match res with
        | Ok union ->
            for KeyValue(var, ty) in union do
                unionFind.Add(var, ty)

            for key in pending.Keys |> Array.ofSeq do
                if pending.ContainsKey key then
                    let ob = pending[key]

                    let remain (v: Var) =
                        match this.NormalizeTy(TVar v) with
                        | TVar v -> Some v
                        | _ -> None

                    let pred =
                        { ob.Pred with
                            Type = Array.map this.NormalizeTy ob.Pred.Type }

                    let remain =
                        pred.Type
                        |> Array.map _.FindTVar()
                        |> Array.map (Seq.choose remain)
                        |> Array.map (Array.ofSeq)

                    // improve by functional dependency
                    if remain |> pred.Trait.GetFree |> Array.forall Array.isEmpty then
                        pending.Remove key |> ignore

                        match this.HasTrait span pred with
                        | Some assoc ->
                            let toUnify = pred.Type |> pred.Trait.GetDep |> Array.zip assoc

                            for assoc, ty in toUnify do
                                this.Unify assoc ty span
                        | None -> error.Add(TraitNotImpl(pred, ob.Span))

                    else
                        let remain = Array.concat remain

                        if remain <> ob.TVar then
                            let ob = { ob with Pred = pred; TVar = remain }

                            pending[key] <- ob

        | Error unionError ->
            for e in unionError do
                error.Add e

    member this.Instantiate (scm: Scheme) span =
        if scm.Generic.Length = 0 then
            scm.Type, [||]
        else
            let inst gen =
                let var = this.NewTVar span |> TVar
                (gen, var)

            let map = Array.map inst scm.Generic |> Map.ofArray

            this.InstantiateWithMap scm map

    member _.InstantiateWithMap (scm: Scheme) map =
        let ty = scm.Type.InstantiateWithMap map

        let instPred (pred: Pred) =
            let inst (ty: Type) = ty.InstantiateWithMap map

            { pred with
                Type = Array.map inst pred.Type }

        let pred = Array.map instPred scm.Pred

        ty, pred

    member this.Generalize(fnTy: Function) : Scheme =
        let group = this.NewGenGroup()
        let outScope (v: Var) = v.Level <= scope.Count

        let acc map (var: Var) =
            if outScope var || Map.containsKey var map then
                map
            else
                let c = Map.count map

                let gen =
                    { Id = c
                      GroupId = group
                      Span = var.Span
                      Sym = "" }

                unionFind.Add(var.Id, TGen gen)
                Map.add var gen map

        let seqAcc map (ty: Type) = ty.FindTVar() |> Seq.fold acc map

        let param = fnTy.Param |> Array.map this.NormalizeTy
        let map = param |> Array.fold seqAcc Map.empty

        let ret = this.NormalizeTy fnTy.Ret

        let map =
            match ret with
            | TFn f -> f.Param |> Array.fold seqAcc map
            | _ -> map

        let toGen t =
            match Map.tryFind t map with
            | Some t -> TGen t
            | None -> TVar t

        let resolve (ty: Type) = ty.Walk toGen TGen

        let param = Array.map resolve param
        let ret = resolve ret

        let generic = map.Values.ToArray()
        let ty = { Param = param; Ret = ret }

        let pred = HashSet()

        let addToPred (p: Pred) =
            if not (pred.Contains p) then
                pred.Add p |> ignore

        for KeyValue(key, ob) in pending |> Array.ofSeq do
            pending.Remove key |> ignore

            let remain key = Map.containsKey key map |> not
            let remain = Array.filter remain ob.TVar

            if remain.Length = 0 then
                let p =
                    { Trait = ob.Pred.Trait
                      Type = Array.map resolve ob.Pred.Type }

                // improvment by instance
                match this.TraitByInst p with
                | None -> addToPred p
                // TODO: what shall we do?
                | Some(p, _) ->
                    for p in p do
                        addToPred p
            else if Array.forall outScope remain then
                let newKey =
                    { key with
                        Type = Array.map resolve key.Type }

                pending[newKey] <-
                    { ob with
                        TVar = remain
                        Pred =
                            { ob.Pred with
                                Type = Array.map resolve ob.Pred.Type } }

            else
                let unresolved = Array.filter (outScope >> not) remain

                for u in unresolved do
                    error.Add(AmbiguousTypeVar u)

        { Generic = generic
          Type = TFn ty
          Pred = pred.ToArray() }

    member this.AddOb({ Pred = pred } as ob: Obligation) =
        let key =
            { pred with
                Type = pred.Trait.GetFree pred.Type }

        if pending.ContainsKey key then
            let prev = pending[key]

            // improvement by functional dependency
            for t1, t2 in Array.zip prev.Pred.Type pred.Type do
                this.Unify t1 t2 ob.Span

        else
            pending.Add(key, ob)

            // improvement by super
            // TODO: properly handle super trait with multi params
            for s in this.AllSuperTrait key.Trait do
                pending.Remove { key with Trait = s } |> ignore

    member this.AllSuperTrait trait_ =
        seq {
            yield! trait_.Super

            for s in trait_.Super do
                yield! this.AllSuperTrait s
        }

    member this.ImplTrait generic pred trait_ traitTy ty span =
        let impl =
            { Pred = pred
              Type = Array.append [| ty |] traitTy
              Generic = generic }
        // TODO: pred?
        let ty, pred =
            this.Instantiate
                { Generic = generic
                  Pred = pred
                  Type = ty }
                Span.dummy

        let ty = Array.append [| ty |] traitTy

        for super in this.AllSuperTrait trait_ do
            let pred =
                { Trait = super
                  Type = Array.append ty traitTy }

            if this.HasTrait span pred = None then
                error.Add(TraitNotImpl(pred, span))

        if traitImpl.ContainsKey trait_ then
            let value = traitImpl[trait_]

            let overlap (prevTy, ty) =
                match this.UnifyInner prevTy ty Span.dummy with
                | Ok _ -> Some prevTy
                | Error _ -> None

            let allOverlap prev =
                let inst gen =
                    let var = this.NewTVar span |> TVar
                    (gen, var)

                let map = Array.map inst prev.Generic |> Map.ofArray

                let instTy (ty: Type) = ty.InstantiateWithMap map

                let prevTy = prev.Type |> trait_.GetFree |> Array.map instTy

                let res = ty |> trait_.GetFree |> Array.zip prevTy |> Array.map overlap

                if Array.contains None res then
                    None
                else
                    res |> Array.map Option.get |> Some

            let res = Util.pick allOverlap value

            match res with
            | None -> value.Add impl
            | Some prev -> error.Add(OverlapImpl(trait_, ty, prev, span))

        else
            let value = ResizeArray()
            value.Add impl
            traitImpl[trait_] <- value

    member this.TraitByInst{ Type = ty; Trait = trait_ } =
        let value = traitImpl[trait_]

        let overlap subst (prevTy, ty) =
            let prevTy = this.NormalizeTyWith subst prevTy

            match this.UnifyInner prevTy ty Span.dummy with
            | Ok s ->
                for KeyValue(var, ty) in s do
                    subst.Add(var, ty)

                true
            | Error _ -> false

        let allOverlap prev =
            let inst gen =
                let var = this.NewTVar Span.dummy |> TVar
                (gen, var)

            let map = Array.map inst prev.Generic |> Map.ofArray

            let instTy (ty: Type) = ty.InstantiateWithMap map

            let implTy = Array.map instTy prev.Type

            let instPred (pred: Pred) =
                let inst (ty: Type) = ty.InstantiateWithMap map

                { pred with
                    Type = Array.map inst pred.Type }

            let prevPred = Array.map instPred prev.Pred

            let subst = Dictionary()

            let res =
                implTy
                |> trait_.GetFree
                |> Array.zip (trait_.GetFree ty)
                |> Array.map (overlap subst)

            if Array.contains false res then
                None
            else
                let normal (pred: Pred) =
                    { pred with
                        Type = Array.map (this.NormalizeTyWith subst) pred.Type }

                let prevPred = Array.map normal prevPred

                Some(prevPred, trait_.GetDep implTy)

        Util.pick allOverlap value

    member this.HasTrait span pred =
        // in cache, fast path
        if predCache.ContainsKey pred then
            Some(predCache[pred])
        else if not (traitImpl.ContainsKey pred.Trait) then
            None
        else
            match this.TraitByInst pred with
            | None -> None
            | Some(p, assoc) ->
                // TODO: same here
                if Array.forall (this.HasTrait span >> Option.isSome) p then
                    this.AddPred pred assoc
                    Some(assoc)
                else
                    None

    member this.AddPred (pred: Pred) assoc =
        for super in this.AllSuperTrait pred.Trait do
            predCache[{ pred with Trait = super }] <- [||]

        predCache.Add(pred, assoc)

    member _.EnterScope data =
        let s = Scope.Create data

        scope.Push s

    member this.ExitScope() =
        let last = scope.Pop()

        match last.Data with
        | FnScope { Param = param
                    Ret = ret
                    Name = name
                    Fixed = f } ->

            if not f then
                let scm = this.Generalize { Param = param; Ret = ret }
                sema.DeclTy[name] <- scm
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

        traitImpl.Add(trait_, ResizeArray())

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

            let ty, pred = this.Instantiate scm id.Span
            let ob = Array.map (Obligation.FromPred id.Span) pred

            for ob in ob do
                this.AddOb ob

            Some ty

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

            sema.Binding.Add(id, def)

            let scm = sema.DeclTy[def]
            let ty, pred = this.Instantiate scm id.Span
            let ob = Array.map (Obligation.FromPred id.Span) pred

            for ob in ob do
                this.AddOb ob

            Some ty

    member _.GetStruct id = sema.Struct[id]

    member this.FindField ty field span =
        let ty = this.NormalizeTy ty

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

    member this.FindMethod ty (arg: Type[]) field span =
        let ty = this.NormalizeTy ty
        let tvar = ty.FindTVar() |> Seq.toArray
        let arg = Array.map this.NormalizeTy arg

        let findTrait scope =
            match scope.Method.Get field with
            | None -> None
            | Some id ->
                let tr = sema.Trait[id]
                let map = Map [| tr.Generic[0], ty |]

                let genTVar =
                    Array.map (fun (gen: Generic) -> this.NewTVar gen.Span) tr.Generic[1..]

                let genTy = Array.map TVar genTVar

                let pred =
                    { Trait = tr
                      Type = Array.append [| ty |] genTy }

                if not (Array.isEmpty tvar) || tr.FreeVarLength > 1 then
                    this.AddPred pred (pred.Trait.GetDep pred.Type)

                    let ob =
                        { Pred = pred
                          TVar = Array.append tvar genTVar
                          Span = span }

                    this.AddOb ob

                    let map =
                        genTVar
                        |> Array.map TVar
                        |> Array.zip tr.Generic[1..]
                        |> Map.ofArray
                        |> Map.foldBack Map.add map

                    Some(tr, map)
                else
                    match this.HasTrait span pred with
                    | Some assoc ->
                        let map =
                            assoc
                            |> Array.zip (tr.GetDep tr.Generic)
                            |> Map.ofArray
                            |> Map.foldBack Map.add map

                        Some(tr, map)
                    | None -> None

        let trait_ = this.Pick findTrait

        match trait_ with
        | None ->
            error.Add(UndefinedMethod(span, ty, field))
            TNever
        | Some(t, map) ->
            let m = t.Method[field]

            if m.Param.Length <> arg.Length then
                error.Add(ParamLenMismatch(span, m.Param.Length, arg.Length))
            else
                for p, a in Array.zip m.Param arg do
                    let p = p.InstantiateWithMap map
                    this.Unify p a span

            m.Ret.InstantiateWithMap map

    member this.GetReturn() =
        let pickRet scope =
            match scope.Data with
            | FnScope { Ret = r }
            | MethodScope { Ret = r }
            | ClosureScope { Ret = r } -> Some r
            | _ -> None

        this.Pick pickRet

    member _.GetSelfType() =
        let rec loop (i: int) =
            let data = (scope.ElementAt i).Data

            match data with
            | AdtScope { Self = self }
            | TraitScope { Self = self }
            | ImplScope { Self = self } -> Some self
            | FnScope _ -> None
            | _ -> if i + 1 = scope.Count then None else loop (i + 1)

        loop 0

    member this.ToNever(name: Id) =
        let toNever t =
            let t = this.NormalizeTy(TVar t)

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

    member _.RegisterExpr expr ty = sema.ExprTy.Add(expr, ty)
    member _.RegisterPat pat ty = sema.PatTy.Add(pat, ty)
    member _.GetPatTy pat = sema.PatTy[pat]

    member _.AddError e = error.Add e
