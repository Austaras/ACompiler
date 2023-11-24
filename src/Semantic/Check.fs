module Semantic.Check

open System.Collections.Generic

// TODO: module system
// TODO: type alias
// TODO: trait, operator overloading and type alias
// TODO: pipe and compose operator

open Common.Span
open Util.Util
open Util.MultiMap
open AST.AST
open Semantic.Semantic

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
       TChar |]

type internal NormalConstraint =
    { Expect: Type
      Actual: Type
      Span: Span }

type internal Constraint =
    | CNormal of NormalConstraint
    | CDeref of NormalConstraint

type internal FnScope = { Fn: Either<Fn, Closure>; Ret: Type }

type internal ScopeData =
    | FnScope of FnScope
    | BlockScope
    | TypeScope
    | TopLevelScope

type internal Scope =
    { Id: int
      Ty: Dictionary<string, Type>
      Var: Dictionary<string, Id * bool>
      Field: MultiMap<string, Id>
      Constr: ResizeArray<Constraint>
      Data: ScopeData
      mutable VarId: int }

    member this.AddVar(id: Id, ?mut) =
        let mut =
            match mut with
            | Some m -> m
            | None -> false

        this.Var[id.Sym] <- id, mut

    member this.NewTVar sym span =
        let tvar =
            { Scope = this.Id
              Id = this.VarId
              Sym = sym
              Span = span }

        this.VarId <- this.VarId + 1

        tvar

    static member Empty id data =
        { Id = id
          Ty = Dictionary()
          Var = Dictionary()
          Field = MultiMap()
          Constr = ResizeArray()
          Data = data
          VarId = 0 }

    static member Prelude =
        let scope =
            { Id = 0
              Ty = Dictionary()
              Var = Dictionary()
              Field = MultiMap()
              Constr = ResizeArray()
              Data = TopLevelScope
              VarId = 0 }

        for p in primitive do
            scope.Ty[p.ToString] <- p

        scope

type internal ActiveScope =
    { Scope: Scope[] }

    member this.WithNew s =
        { Scope = Array.append this.Scope [| s |] }

    member this.Current = Array.last this.Scope

    member this.Pick picker = tryPickBack picker this.Scope

    member this.ResolveTy(id: Id) =
        let pickId scope =
            if scope.Ty.ContainsKey id.Sym then
                let id = scope.Ty[id.Sym]
                Some id
            else
                None

        this.Pick pickId

    member this.ResolveVar(id: Id) =
        let pickId scope =
            if scope.Var.ContainsKey id.Sym then
                let id = scope.Var[id.Sym]
                Some id
            else
                None

        this.Pick pickId

// union find set
type internal TyUnion() =
    let pred = Dictionary<Var, Type>()

    member _.Add k p = pred[k] <- p

    member this.Find k =
        if pred.ContainsKey k then
            let p = pred[k]

            match p with
            | TVar v ->
                let p = this.Find v

                pred[k] <- p

                p
            | p -> p
        else
            TVar k

    member this.Resolve ty =
        let onvar tvar =
            if pred.ContainsKey tvar then
                let p = this.Resolve pred[tvar]

                pred[tvar] <- p

                p
            else
                TVar tvar

        ty.Walk onvar

    member this.TryFind k =
        if pred.ContainsKey k then Some(this.Find k) else None

type internal LetPat = { Mut: bool; Static: bool }

type internal PatMode =
    | ParamPat
    | CondPat
    | LetPat of LetPat

type TypeCheck(moduleMap: Map<string, ModuleType>) =
    let mutable scopeId = 0

    let sema = SemanticInfo.Create()

    let tyUnion = TyUnion()
    let error = ResizeArray<Error>()

    member internal _.NewScope scopeData =
        scopeId <- scopeId + 1
        Scope.Empty scopeId scopeData

    member internal this.ProcessTy (scope: ActiveScope) ty =
        let resolve id =
            match scope.ResolveTy id with
            | Some ty -> ty
            | None ->
                error.Add(Undefined id)
                TNever

        match ty with
        | NeverType _ -> TNever
        | TypeId i -> resolve i
        | PathType p ->
            if p.Prefix <> None || p.Seg.Length > 1 then
                failwith "Not Implemented"

            let id, ty = p.Seg[0]

            let instType = Array.map (this.ProcessTy scope) ty

            let container = resolve id

            match container with
            | TStruct(id, gen) when gen.Length = instType.Length -> TStruct(id, instType)
            | TEnum(id, gen) when gen.Length = instType.Length -> TEnum(id, instType)
            | _ ->
                error.Add(GenericMismatch(container, instType, p.Span))

                TNever
        | TupleType t -> TTuple(Array.map (this.ProcessTy scope) t.Ele)
        | RefType r -> TRef(this.ProcessTy scope r.Ty)
        | InferedType span ->
            let newTVar = scope.Current.NewTVar None span

            TVar newTVar
        | LitType _ -> failwith "Not Implemented"
        | ArrayType _ -> failwith "Not Implemented"
        | FnType _ -> failwith "Not Implemented"

    member internal this.ProcessPat (scope: ActiveScope) mode pat ty =
        let mut, mayShadow, isCond =
            match mode with
            | LetPat { Mut = mut; Static = static_ } -> mut, not static_, false
            | ParamPat -> true, false, false
            | CondPat -> true, true, true

        let addSym sym (i: Id) (ty: Type) =
            if Map.containsKey i.Sym sym then
                error.Add(DuplicateDefinition i)

            Map.add i.Sym (i, ty) sym

        let currScope = scope.Current

        let rec proc sym ty pat =
            match pat with
            | IdPat i -> addSym sym i ty
            | LitPat(l, span) ->
                if not isCond then
                    error.Add(RefutablePat span)

                let litTy =
                    match l with
                    | Int _ -> TInt(true, ISize)
                    | Bool _ -> TBool
                    | Char _ -> TChar
                    | Float _ -> TFloat F64
                    | String _ -> failwith "Not Implemented"
                    | NegInt _ -> failwith "Unreachable"

                currScope.Constr.Add(
                    CNormal
                        { Actual = litTy
                          Expect = ty
                          Span = span }
                )

                sym
            | RangePat { Span = span } -> failwith "Not Implemented"
            | CatchAllPat _ -> sym
            | TuplePat t ->
                let addBinding pat =
                    let sym =
                        match pat with
                        | IdPat id -> Some id.Sym
                        | _ -> None

                    let newVar = currScope.NewTVar sym pat.Span |> TVar

                    newVar

                let patTy = t.Ele |> Array.map addBinding

                currScope.Constr.Add(
                    CNormal
                        { Actual = TTuple patTy
                          Expect = ty
                          Span = t.Span }
                )

                Array.fold2 proc sym patTy t.Ele
            | AsPat a ->
                let sym = addSym sym a.Id ty

                proc sym ty a.Pat
            | OrPat { Pat = pat; Span = span } ->
                if not isCond then
                    error.Add(RefutablePat span)

                let allSym = Array.map (proc Map.empty ty) pat

                let first = allSym[0]

                for (idx, sym) in Array.indexed allSym do
                    if idx > 0 then
                        let firstKey = first |> Map.keys |> Array.ofSeq
                        let currKey = sym |> Map.keys |> Array.ofSeq

                        if firstKey <> currKey then
                            error.Add(OrPatDifferent(pat[idx].Span, firstKey, currKey))

                        for key in firstKey do
                            let firstTy = snd first[key]
                            let id, currTy = sym[key]

                            currScope.Constr.Add(
                                CNormal
                                    { Expect = firstTy
                                      Actual = currTy
                                      Span = id.Span }
                            )

                let mergeSym sym curr =
                    Map.fold (fun sym _ (id, ty) -> addSym sym id ty) sym curr

                Array.fold mergeSym sym allSym
            | ArrayPat(_) -> failwith "Not Implemented"
            | PathPat(_) -> failwith "Not Implemented"
            | EnumPat e ->
                if e.Name.Prefix <> None || e.Name.Seg.Length <> 2 then
                    failwith "Not Implemented"

                if not isCond then
                    error.Add(RefutablePat e.Span)

                let enumId = e.Name.Seg[0]
                let variant = e.Name.Seg[1]

                let enumTy =
                    match scope.ResolveTy enumId with
                    | Some ty -> ty
                    | None ->
                        error.Add(Undefined enumId)
                        TNever

                let payloadTy =
                    match enumTy with
                    | TEnum(enum, v) ->
                        let enumData = sema.Enum[enum]
                        let inst = Array.map (fun _ -> TVar(currScope.NewTVar None e.Span)) v

                        if enumData.variant.ContainsKey variant.Sym then
                            currScope.Constr.Add(
                                CNormal
                                    { Expect = TEnum(enum, inst)
                                      Actual = ty
                                      Span = e.Span }
                            )

                            let payload = enumData.variant[variant.Sym]

                            if payload.Length <> e.Payload.Length then
                                error.Add(PayloadMismatch(e.Span, enumData))

                            let getTy idx _ =
                                if idx < payload.Length then
                                    payload[idx].Instantiate enumData.tvar inst
                                else
                                    TNever

                            Array.mapi getTy e.Payload
                        else
                            error.Add(UndefinedVariant(enumId, variant))

                            Array.map (fun _ -> TNever) e.Payload

                    | ty ->
                        error.Add(ExpectEnum(enumId, ty))

                        Array.map (fun _ -> TNever) e.Payload

                Array.fold2 proc sym payloadTy e.Payload
            | StructPat(_) -> failwith "Not Implemented"
            | RestPat span ->
                if not isCond then
                    error.Add(RefutablePat span)

                sym
            | SelfPat(_) -> failwith "Not Implemented"
            | RefSelfPat(_) -> failwith "Not Implemented"

        let map = proc Map.empty ty pat

        for (id, ty) in map.Values do
            if mayShadow && currScope.Var.ContainsKey id.Sym then
                error.Add(DuplicateDefinition id)

            currScope.AddVar(id, mut)
            sema.Var[id] <- ty

    member internal this.ProcessHoistedDecl (scope: ActiveScope) (decl: seq<Decl>) =
        let currScope = scope.Current

        let topLevel =
            match currScope.Data with
            | TopLevelScope -> true
            | _ -> false

        // Process Type Decl Hoisted Name
        for d in decl do
            let dummyTVar _ =
                TVar
                    { Scope = 0
                      Id = 0
                      Sym = None
                      Span = Span.dummy }

            match d with
            | Let _
            | Const _
            | FnDecl _ -> ()
            | StructDecl s ->
                if currScope.Ty.ContainsKey s.Id.Sym then
                    error.Add(DuplicateDefinition s.Id)

                let tvar = Array.map dummyTVar s.TyParam
                currScope.Ty[s.Id.Sym] <- TStruct(s.Id, tvar)

                for field in s.Field do
                    currScope.Field.Add field.Name.Sym s.Id

            | EnumDecl e ->
                if currScope.Ty.ContainsKey e.Id.Sym then
                    error.Add(DuplicateDefinition e.Id)

                let tvar = Array.map dummyTVar e.TyParam
                currScope.Ty[e.Id.Sym] <- TEnum(e.Id, tvar)
            | TypeDecl t ->
                if currScope.Ty.ContainsKey t.Name.Sym then
                    error.Add(DuplicateDefinition t.Name)

                currScope.Ty[t.Name.Sym] <- TNever
            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        let staticItem = ResizeArray()

        // Process Type Decl
        for d in decl do
            match d with
            | Let _ ->
                if topLevel then
                    staticItem.Add d
            | Const _ -> ()
            | FnDecl _ -> staticItem.Add d
            | StructDecl s ->
                let scope, tvar =
                    if s.TyParam.Length > 0 then
                        let newScope = this.NewScope TypeScope

                        let processParam (param: TypeParam) =
                            let newTVar = newScope.NewTVar (Some param.Id.Sym) param.Id.Span

                            newScope.Ty[param.Id.Sym] <- TVar newTVar

                            newTVar

                        scope.WithNew newScope, Array.map processParam s.TyParam
                    else
                        scope, [||]

                let processField m (field: StructFieldDef) =
                    let name = field.Name.Sym

                    if Map.containsKey name m then
                        error.Add(DuplicateField field.Name)

                    Map.add name (this.ProcessTy scope field.Ty) m

                let field = Array.fold processField Map.empty s.Field

                let stru =
                    { Name = s.Id
                      Field = field
                      TVar = tvar }

                sema.Struct[s.Id] <- stru

            | EnumDecl e ->
                let scope, tvar =
                    if e.TyParam.Length > 0 then
                        let newScope = this.NewScope TypeScope

                        let processParam (param: TypeParam) =
                            let newTVar = newScope.NewTVar (Some param.Id.Sym) param.Id.Span

                            newScope.Ty[param.Id.Sym] <- TVar newTVar

                            newTVar

                        scope.WithNew newScope, Array.map processParam e.TyParam
                    else
                        scope, [||]

                let processVariant m (variant: EnumVariantDef) =
                    let name = variant.Id.Sym

                    if Map.containsKey name m then
                        error.Add(DuplicateVariant variant.Id)

                    let payload = Array.map (this.ProcessTy scope) variant.Payload

                    Map.add name payload m

                let variant = Array.fold processVariant Map.empty e.Variant

                let enum =
                    { name = e.Id
                      variant = variant
                      tvar = tvar }

                sema.Enum[e.Id] <- enum

            | TypeDecl t -> currScope.Ty[t.Name.Sym] <- this.ProcessTy scope t.Ty

            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        let valueMap = Dictionary()
        let scopeMap = Dictionary()

        for item in staticItem do
            match item with
            | FnDecl f ->
                if currScope.Var.ContainsKey f.Name.Sym then
                    error.Add(DuplicateDefinition f.Name)

                currScope.AddVar f.Name

                let newScope = this.NewScope TypeScope

                let tvar =
                    let processParam (param: TypeParam) =
                        let newTVar = newScope.NewTVar (Some param.Id.Sym) param.Id.Span

                        newScope.Ty.Add(param.Id.Sym, TVar newTVar)

                        newTVar

                    Array.map processParam f.TyParam

                let scope = scope.WithNew newScope

                let paramTy (p: Param) =
                    match p.Ty with
                    | Some ty -> this.ProcessTy scope ty
                    | None ->
                        let sym =
                            match p.Pat with
                            | IdPat i -> Some(i.Sym)
                            | _ -> None

                        let newTVar = newScope.NewTVar sym p.Span

                        TVar newTVar

                let param = Array.map paramTy f.Param

                let ret =
                    match f.Ret with
                    | Some ty -> this.ProcessTy scope ty
                    | None -> TVar(newScope.NewTVar None f.Span)

                let newScope =
                    { newScope with
                        Data = FnScope { Fn = Left f; Ret = ret } }

                scopeMap.Add(f, newScope)

                let fnTy =
                    TFn
                        { Param = param
                          Ret = ret
                          TVar = tvar }

                sema.Var[f.Name] <- fnTy

            | Let l ->
                let ty =
                    match l.Ty with
                    | Some ty -> this.ProcessTy scope ty
                    | None ->
                        let sym =
                            match l.Pat with
                            | IdPat i -> Some(i.Sym)
                            | _ -> None

                        let newTVar = currScope.NewTVar sym l.Span

                        TVar newTVar

                valueMap.Add(l.Pat, ty)
                this.ProcessPat scope (LetPat { Mut = l.Mut; Static = true }) l.Pat ty
            | _ -> ()

        for item in staticItem do
            match item with
            | FnDecl f ->
                let newScope = scope.WithNew scopeMap[f]
                this.ProcessFn newScope f
            | Let l ->
                let value = this.ProcessExpr scope l.Value

                currScope.Constr.Add(
                    CNormal
                        { Expect = valueMap[l.Pat]
                          Actual = value
                          Span = l.Span }
                )
            | _ -> ()

    member internal this.ProcessDecl (scope: ActiveScope) d =
        match d with
        | Let l ->
            let value = this.ProcessExpr scope l.Value

            let ty =
                match l.Ty with
                | Some ty ->
                    let ty = this.ProcessTy scope ty

                    scope.Current.Constr.Add(
                        CNormal
                            { Expect = ty
                              Actual = value
                              Span = l.Span }
                    )

                    ty
                | None -> value

            this.ProcessPat scope (LetPat { Mut = l.Mut; Static = false }) l.Pat ty

        | Const _ -> failwith "Not Implemented"
        | Use _ -> failwith "Not Implemented"
        | FnDecl _
        | StructDecl _
        | EnumDecl _
        | TypeDecl _
        | Trait _
        | Impl _ -> ()

    member internal this.ProcessCond (scope: ActiveScope) cond block =
        let currScope = scope.Current

        match cond with
        | BoolCond b ->
            currScope.Constr.Add(
                CNormal
                    { Expect = TBool
                      Actual = this.ProcessExpr scope b
                      Span = b.Span }
            )

            this.ProcessBlock scope block
        | LetCond c ->
            let value = this.ProcessExpr scope c.Value
            let newScope = this.NewScope BlockScope
            let scope = scope.WithNew newScope

            this.ProcessPat scope CondPat c.Pat value

            let ty = this.ProcessBlock scope block

            this.Unify newScope

            tyUnion.Resolve ty

    member internal this.ProcessExpr (scope: ActiveScope) e =
        let currScope = scope.Current

        match e with
        | Id id ->
            let rec resolveVar captured i =
                let curr = scope.Scope[i]

                if curr.Var.ContainsKey id.Sym then
                    let captured =
                        match curr.Data with
                        | TopLevelScope -> [||]
                        | _ -> captured

                    Some(curr.Var[id.Sym], captured)
                else if i = 0 then
                    None
                else
                    let captured =
                        match curr.Data with
                        | FnScope { Fn = fn } -> Array.append captured [| fn |]
                        | _ -> captured

                    resolveVar captured (i - 1)

            match resolveVar [||] (scope.Scope.Length - 1) with
            | None ->
                error.Add(Undefined id)
                TNever
            | Some((id, _), captured) ->
                for c in captured do
                    sema.Capture.Add c id

                match sema.Var[id] with
                | TFn f ->
                    let newTVar = Array.map (fun _ -> currScope.NewTVar None id.Span) f.TVar
                    TFn(f.Instantiate newTVar)
                | t -> t

        | Binary b ->
            let l = this.ProcessExpr scope b.Left
            let r = this.ProcessExpr scope b.Right

            match b.Op with
            | Arithmetic(LogicalAnd | LogicalOr) ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TBool
                          Actual = l
                          Span = b.Left.Span }
                )

                currScope.Constr.Add(
                    CNormal
                        { Expect = TBool
                          Actual = r
                          Span = b.Right.Span }
                )

                TBool
            | Arithmetic _ ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TInt(true, ISize)
                          Actual = l
                          Span = b.Left.Span }
                )

                currScope.Constr.Add(
                    CNormal
                        { Expect = TInt(true, ISize)
                          Actual = r
                          Span = b.Right.Span }
                )

                TInt(true, ISize)
            | EqEq
            | NotEq
            | Lt
            | Gt
            | LtEq
            | GtEq ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = l
                          Actual = r
                          Span = b.Span }
                )

                TBool
            | Pipe -> failwith "Not Implemented"
            | As -> failwith "Not Implemented"

        | SelfExpr(_) -> failwith "Not Implemented"
        | LitExpr(l, _) ->
            match l with
            | Int _ -> TInt(true, ISize)
            | Bool _ -> TBool
            | Char _ -> TChar
            | Float _ -> TFloat F64
            | String _ -> failwith "Not Implemented"
            | NegInt _ -> failwith "Unreachable"

        | If i ->
            let then_ = this.ProcessCond scope i.Cond i.Then

            for br in i.ElseIf do
                let elseif = this.ProcessCond scope br.Cond br.Block

                currScope.Constr.Add(
                    CNormal
                        { Expect = then_
                          Actual = elseif
                          Span = i.Span }
                )

            match i.Else with
            | Some else_ ->
                let else_ = this.ProcessBlock scope else_

                currScope.Constr.Add(
                    CNormal
                        { Expect = then_
                          Actual = else_
                          Span = i.Span }
                )
            | None ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = then_
                          Actual = UnitType
                          Span = i.Span }
                )

            then_
        | Match m ->
            let value = this.ProcessExpr scope m.expr

            let typeOfBranch (br: MatchBranch) =
                let newScope = this.NewScope BlockScope
                let scope = scope.WithNew newScope

                this.ProcessPat scope CondPat br.Pat value

                match br.Guard with
                | Some g ->
                    newScope.Constr.Add(
                        CNormal
                            { Actual = this.ProcessExpr scope g
                              Expect = TBool
                              Span = g.Span }
                    )
                | None -> ()

                let brTy = this.ProcessExpr scope br.Expr

                this.Unify newScope

                tyUnion.Resolve brTy

            if Array.length m.branch = 0 then
                UnitType
            else
                let first = typeOfBranch m.branch[0]

                for br in m.branch[1..] do
                    let brTy = typeOfBranch br

                    currScope.Constr.Add(
                        CNormal
                            { Expect = first
                              Actual = brTy
                              Span = br.Span }
                    )

                first

        | Block b -> this.ProcessBlock scope b
        | Call c ->
            let callee = this.ProcessExpr scope c.Callee

            let arg = Array.map (this.ProcessExpr scope) c.Arg
            let ret = TVar(currScope.NewTVar None c.Span)

            currScope.Constr.Add(
                CNormal
                    { Expect = TFn { Param = arg; Ret = ret; TVar = [||] }
                      Actual = callee
                      Span = c.Span }
            )

            ret
        | Unary u ->
            match u.Op with
            | Not ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TBool
                          Actual = this.ProcessExpr scope u.Expr
                          Span = u.Span }
                )

                TBool
            | Neg ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TInt(true, ISize)
                          Actual = this.ProcessExpr scope u.Expr
                          Span = u.Span }
                )

                TInt(true, ISize)
            | Ref ->
                let rec getVar expr =
                    match expr with
                    | Id i -> Some i
                    | Field { Receiver = receiver } -> getVar receiver
                    | Index { Container = container } -> getVar container
                    | Unary { Op = Deref; Expr = expr } -> getVar expr
                    | _ -> None

                TRef(this.ProcessExpr scope u.Expr)
            | Deref ->
                let sym =
                    match u.Expr with
                    | Id i -> Some i.Sym
                    | _ -> None

                let ptr = TVar(currScope.NewTVar sym u.Expr.Span)

                currScope.Constr.Add(
                    CNormal
                        { Expect = TRef ptr
                          Actual = this.ProcessExpr scope u.Expr
                          Span = u.Span }
                )

                ptr
        | Assign a ->
            let value = this.ProcessExpr scope a.Value
            let place = this.ProcessExpr scope a.Place

            currScope.Constr.Add(
                CNormal
                    { Expect = place
                      Actual = value
                      Span = a.Span }
            )

            let rec getVar expr =
                match expr with
                | Id i -> Some i
                | Field { Receiver = receiver } -> getVar receiver
                | Index { Container = container } -> getVar container
                | Unary { Op = Deref; Expr = expr } -> getVar expr
                | _ -> None

            match getVar a.Place with
            | None -> ()
            | Some id ->
                match scope.ResolveVar id with
                | None -> ()
                | Some(id, mut) ->
                    if not mut then
                        error.Add(AssignImmutable(id, a.Span))

            UnitType
        | Field f ->
            let receiver = this.ProcessExpr scope f.Receiver
            let key = f.Prop.Sym

            match receiver with
            | TStruct(i, inst) ->
                let stru = sema.Struct[i]

                match Map.tryFind key stru.Field with
                | Some f -> f.Instantiate stru.TVar inst
                | None ->
                    error.Add(UndefinedField(f.Span, key))

                    TNever
            | _ ->
                let findStruct scope =
                    match scope.Field.Get key with
                    | None -> None
                    | Some id -> Some sema.Struct[id]

                let stru = scope.Pick findStruct

                match stru with
                | Some s ->
                    let inst = Array.map (fun _ -> TVar(currScope.NewTVar None f.Span)) s.TVar

                    currScope.Constr.Add(
                        CDeref
                            { Expect = TStruct(s.Name, inst)
                              Actual = receiver
                              Span = f.Span }
                    )

                    s.Field[key].Instantiate s.TVar inst
                | None ->
                    error.Add(UndefinedField(f.Span, key))
                    TNever

        | Index(_) -> failwith "Not Implemented"
        | Array(_) -> failwith "Not Implemented"
        | ArrayRepeat(_) -> failwith "Not Implemented"
        | StructLit(_) -> failwith "Not Implemented"
        | Tuple s -> Array.map (this.ProcessExpr scope) s.element |> TTuple
        | Closure c ->
            let paramTy (p: Param) =
                match p.Ty with
                | Some ty -> this.ProcessTy scope ty
                | None ->
                    let sym =
                        match p.Pat with
                        | IdPat i -> Some i.Sym
                        | _ -> None

                    let newTVar = currScope.NewTVar sym p.Span

                    TVar newTVar

            let paramTy = Array.map paramTy c.Param

            let retTy =
                match c.Ret with
                | Some ty -> this.ProcessTy scope ty
                | None -> TVar(currScope.NewTVar None c.Span)

            let closureScope = this.NewScope(FnScope { Fn = Right c; Ret = retTy })

            let scope = scope.WithNew closureScope

            for (param, ty) in Array.zip c.Param paramTy do
                this.ProcessPat scope ParamPat param.Pat ty

            let ret = this.ProcessExpr scope c.Body

            closureScope.Constr.Add(
                CNormal
                    { Expect = retTy
                      Actual = ret
                      Span = c.Span }
            )

            this.Unify closureScope

            let resolve ty = tyUnion.Resolve ty

            TFn
                { Param = Array.map resolve paramTy
                  Ret = resolve retTy
                  TVar = [||] }

        | Path p ->
            if p.Prefix <> None || p.Seg.Length <> 2 then
                failwith "Not Implemented"

            let enumId, _ = p.Seg[0]
            let variant, _ = p.Seg[1]

            let enumTy =
                match scope.ResolveTy enumId with
                | Some ty -> ty
                | None ->
                    error.Add(Undefined enumId)
                    TNever

            match enumTy with
            | TEnum(enum, _) ->
                let enumData = sema.Enum[enum]
                let inst = Array.map (fun _ -> TVar(currScope.NewTVar None e.Span)) enumData.tvar

                if enumData.variant.ContainsKey variant.Sym then
                    let payload = enumData.variant[variant.Sym]

                    if payload.Length = 0 then
                        TEnum(enum, inst)
                    else
                        let payload = Array.map (fun (t: Type) -> t.Instantiate enumData.tvar inst) payload

                        TFn
                            { Param = payload
                              Ret = TEnum(enum, inst)
                              TVar = [||] }
                else
                    error.Add(UndefinedVariant(enumId, variant))

                    TNever

            | ty ->
                error.Add(ExpectEnum(enumId, ty))

                TNever

        | Break _ -> TNever
        | Continue _ -> TNever
        | Return r ->
            let pickFn scope =
                match scope.Data with
                | FnScope f -> Some f
                | _ -> None

            let retTy =
                match scope.Pick pickFn with
                | Some { Ret = retTy } -> retTy
                | None -> failwith "Unreachable"

            let ty =
                match r.Value with
                | Some v -> this.ProcessExpr scope v
                | None -> UnitType

            currScope.Constr.Add(
                CNormal
                    { Expect = retTy
                      Actual = ty
                      Span = r.Span }
            )

            TNever
        | Range(_) -> failwith "Not Implemented"
        | For(_) -> failwith "Not Implemented"
        | While w ->
            let _ = this.ProcessCond scope w.Cond w.Body

            UnitType
        | TryReturn(_) -> failwith "Not Implemented"

    member internal this.ProcessBlock (scope: ActiveScope) (b: Block) =
        let blockScope = this.NewScope BlockScope

        let scope = scope.WithNew blockScope

        let chooseDecl s =
            match s with
            | DeclStmt d -> Some d
            | ExprStmt _ -> None

        let decl = Seq.choose chooseDecl b.Stmt

        this.ProcessHoistedDecl scope decl

        let typeof _ stmt =
            match stmt with
            | DeclStmt d ->
                this.ProcessDecl scope d

                UnitType
            | ExprStmt e -> this.ProcessExpr scope e

        let ty = Array.fold typeof UnitType b.Stmt

        this.Unify blockScope

        tyUnion.Resolve ty

    member internal this.ProcessFn (scope: ActiveScope) (f: Fn) =
        let fnTy =
            match sema.Var[f.Name] with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        let currScope = scope.Current

        for (param, ty) in Array.zip f.Param fnTy.Param do
            this.ProcessPat scope ParamPat param.Pat ty

        let ret = this.ProcessBlock scope f.Body

        currScope.Constr.Add(
            CNormal
                { Expect = fnTy.Ret
                  Actual = ret
                  Span = f.Name.Span }
        )

        this.Unify currScope

        let generalize ty =
            match tyUnion.Resolve ty with
            | TFn f -> TFn(f.Generalize scope.Current.Id)
            | _ -> failwith "Unreachable"

        let oldTy = sema.Var[f.Name]
        sema.Var[f.Name] <- generalize oldTy

    member internal this.Unify scope =
        let rec unifyNormal c deref =
            let addUnion v ty =
                match tyUnion.TryFind v with
                | None -> tyUnion.Add v ty
                | Some prev ->
                    unifyNormal
                        { Expect = ty
                          Actual = prev
                          Span = c.Span }
                        deref

                    tyUnion.Add v (tyUnion.Resolve prev)

            match c.Expect, c.Actual with
            | p1, p2 when p1 = p2 -> ()
            | TVar v1 as t1, (TVar v2 as t2) ->
                if v1.Scope > v2.Scope then
                    addUnion v1 t2
                else if v1.Scope = v2.Scope then
                    if v1.Id > v2.Id then addUnion v1 t2 else addUnion v2 t1
                else
                    addUnion v2 t1
            | TVar v, ty
            | ty, TVar v ->
                // let ty = tyUnion.Resolve ty

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

        for c in scope.Constr do
            match c with
            | CNormal c -> unifyNormal c false
            | CDeref c -> unifyNormal c true

    member this.Check m =
        let topLevel = this.NewScope TopLevelScope
        let scope = { Scope = [| Scope.Prelude; topLevel |] }

        let getDecl m = m.Decl

        let decl = Array.map getDecl m.Item

        this.ProcessHoistedDecl scope decl

        this.Unify topLevel

        for id in sema.Var.Keys do
            let oldTy = sema.Var[id]
            sema.Var[id] <- tyUnion.Resolve oldTy

    member _.GetInfo = sema

    member _.GetError = error
