module Semantic.Check

open System.Collections.Generic

// TODO: module system
// TODO: type alias
// TODO: trait, operator overloading and type alias
// TODO: pipe and compose operator

open Util.Util
open AST.AST
open Semantic.Semantic

type Error =
    | Undefined of Id
    | UndefinedField of Span * string
    | UndefinedVariant of Id * Id
    | DuplicateDefinition of Id
    | DuplicateField of Id
    | DuplicateVariant of Id
    | LoopInDefintion of Id * Id
    | PrivatecInPublic of Id * Id
    | ExpectEnum of Id * Type
    | PayloadMismatch of Span * Enum
    | TupleLengthMismatch of Span * int * int
    | TypeMismatch of Type * Type * Span
    | GenericMismatch of Type * Type[] * Span
    | FailToUnify of Type * Type * Span
    | CalleeNotCallable of Type * Span
    | AssignImmutable of Id * Span
    | RefutablePat of Span
    | LoopInType of Id[]

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
    { expect: Type
      actual: Type
      span: Span }

type internal Constraint =
    | CNormal of NormalConstraint
    | CDeref of NormalConstraint

type internal ScopeData =
    | FnScope of Type // return type
    | BlockScope
    | TypeScope
    | TopLevelScope

type internal Scope =
    { ty: Dictionary<string, Id>
      var: Dictionary<string, Id>
      constr: ResizeArray<Constraint>
      id: int
      data: ScopeData
      mutable varId: int }

    member this.AddTy(id: Id) = this.ty[id.sym] <- id

    member this.AddVar(id: Id) = this.var[id.sym] <- id

    member this.NewTVar sym span =
        let tvar =
            { scope = this.id
              id = this.varId
              sym = sym
              span = span }

        this.varId <- this.varId + 1

        tvar

    static member Empty id data =
        { ty = Dictionary()
          var = Dictionary()
          constr = ResizeArray()
          id = id
          data = data
          varId = 0 }

    static member Prelude =
        let scope =
            { ty = Dictionary()
              var = Dictionary()
              constr = ResizeArray()
              id = 0
              data = TopLevelScope
              varId = 0 }

        for p in primitive do
            let name = p.ToString
            scope.ty[name] <- { sym = name; span = Span.dummy }

        scope

type internal ActiveScope =
    { scope: Scope[] }

    member this.WithNew s =
        { scope = Array.append this.scope [| s |] }

    member this.current = Array.last this.scope

    member this.PickCurrent picker = tryPickBack picker this.scope

    member this.ResolveTy(id: Id) =
        let pickId scope =
            if scope.ty.ContainsKey id.sym then
                let id = scope.ty[id.sym]
                Some id
            else
                None

        this.PickCurrent pickId

type Checker(moduleMap: Map<string, ModuleType>) =
    let mutable scopeId = 0

    let sema =
        let sema = SemanticInfo.Empty()

        for t in primitive do
            let id = { sym = t.ToString; span = Span.dummy }

            sema.ty[id] <- t

        sema

    let tVarMap = Dictionary<Var, Type>()
    let error = ResizeArray<Error>()

    member internal _.NewScope scopeData =
        scopeId <- scopeId + 1
        Scope.Empty scopeId scopeData

    member internal this.ProcessTy (scope: ActiveScope) ty =
        let resolve id =
            match scope.ResolveTy id with
            | Some id -> sema.ty[id]
            | None ->
                error.Add(Undefined id)
                TNever

        match ty with
        | NeverType _ -> TNever
        | TypeId i -> resolve i
        | PathType p ->
            if p.prefix <> None || p.seg.Length > 1 then
                failwith "Not Implemented"

            let id, ty = p.seg[0]

            let instType = Array.map (this.ProcessTy scope) ty

            let container = resolve id

            match container with
            | TStruct(id, gen) when gen.Length = instType.Length -> TStruct(id, instType)
            | TEnum(id, gen) when gen.Length = instType.Length -> TEnum(id, instType)
            | _ ->
                error.Add(GenericMismatch(container, instType, p.span))

                TNever
        | TupleType t -> TTuple(Array.map (this.ProcessTy scope) t.element)
        | RefType r -> TRef(this.ProcessTy scope r.ty)
        | InferedType span ->
            let newTVar = scope.current.NewTVar None span

            TVar newTVar
        | LitType _ -> failwith "Not Implemented"
        | ArrayType _ -> failwith "Not Implemented"
        | FnType _ -> failwith "Not Implemented"

    member internal this.ProcessDeclPat (scope: Scope) pat ty mut (seen: HashSet<string>) =
        match pat with
        | IdPat i ->
            if seen.Contains i.sym then
                error.Add(DuplicateDefinition i)

            seen.Add i.sym |> ignore
            scope.AddVar i

            sema.AddVar i ty mut
        | LitPat(_, span)
        | RangePat { span = span } -> error.Add(RefutablePat span)
        | CatchAllPat _ -> ()
        | TuplePat t ->
            let addBinding pat =
                let sym =
                    match pat with
                    | IdPat id -> Some id.sym
                    | _ -> None

                let newVar = scope.NewTVar sym pat.span |> TVar
                this.ProcessDeclPat scope pat newVar mut seen

                newVar

            let patTy = Array.map addBinding t.element

            scope.constr.Add(
                CNormal
                    { actual = TTuple patTy
                      expect = ty
                      span = t.span }
            )
        | AsPat a ->
            if seen.Contains a.id.sym then
                error.Add(DuplicateDefinition a.id)

            seen.Add a.id.sym |> ignore
            scope.AddVar a.id
            sema.AddVar a.id ty mut

            this.ProcessDeclPat scope a.pat ty mut seen
        | ArrayPat(_) -> failwith "Not Implemented"
        | PathPat(_) -> failwith "Not Implemented"
        | EnumPat(_) -> failwith "Not Implemented"
        | StructPat(_) -> failwith "Not Implemented"
        | OrPat(_) -> failwith "Not Implemented"
        | RestPat(_) -> failwith "Not Implemented"
        | SelfPat(_) -> failwith "Not Implemented"
        | RefSelfPat(_) -> failwith "Not Implemented"

    member internal this.ProcessCondPat (scope: ActiveScope) pat ty (seen: HashSet<string>) =
        let currScope = scope.current

        match pat with
        | IdPat i ->
            if seen.Contains i.sym then
                error.Add(DuplicateDefinition i)

            seen.Add i.sym |> ignore
            currScope.AddVar i
            sema.AddVar i ty true
        | LitPat(l, span) ->
            let litTy =
                match l with
                | Int _ -> TInt(true, ISize)
                | Bool _ -> TBool
                | Char _ -> TChar
                | Float _ -> TFloat F64
                | String _ -> failwith "Not Implemented"
                | NegInt _ -> failwith "Unreachable"

            currScope.constr.Add(
                CNormal
                    { actual = litTy
                      expect = ty
                      span = span }
            )
        | RangePat _ -> failwith "Not Implemented"
        | CatchAllPat _ -> ()
        | TuplePat t ->
            let addBinding pat =
                let sym =
                    match pat with
                    | IdPat id -> Some id.sym
                    | _ -> None

                let newVar = currScope.NewTVar sym pat.span |> TVar
                this.ProcessCondPat scope pat newVar seen

                newVar

            let patTy = Array.map addBinding t.element

            currScope.constr.Add(
                CNormal
                    { actual = TTuple patTy
                      expect = ty
                      span = t.span }
            )
        | AsPat a ->
            if seen.Contains a.id.sym then
                error.Add(DuplicateDefinition a.id)

            seen.Add a.id.sym |> ignore
            currScope.AddVar a.id
            sema.AddVar a.id ty true

            this.ProcessCondPat scope a.pat ty seen
        | ArrayPat _ -> failwith "Not Implemented"
        | PathPat _ -> failwith "Not Implemented"
        | EnumPat e ->
            if e.name.prefix <> None || e.name.seg.Length <> 2 then
                failwith "Not Implemented"

            let enumId = e.name.seg[0]
            let variant = e.name.seg[1]

            let enumTy =
                match scope.ResolveTy enumId with
                | Some id -> sema.ty[id]
                | None ->
                    error.Add(Undefined enumId)
                    TNever

            match enumTy with
            | TEnum(enum, v) ->
                let enumData = sema.enum[enum]
                let inst = Array.map (fun _ -> TVar(currScope.NewTVar None e.span)) v

                if enumData.variant.ContainsKey variant.sym then
                    let payload = enumData.variant[variant.sym]

                    if payload.Length <> e.content.Length then
                        error.Add(PayloadMismatch(e.span, enumData))

                    for idx, c in Array.indexed e.content do
                        let payload =
                            if idx < payload.Length then
                                payload[idx].Instantiate enumData.tvar inst
                            else
                                TNever

                        this.ProcessCondPat scope c payload seen


                    currScope.constr.Add(
                        CNormal
                            { expect = TEnum(enum, inst)
                              actual = ty
                              span = e.span }
                    )
                else
                    error.Add(UndefinedVariant(enumId, variant))

                    for c in e.content do
                        this.ProcessCondPat scope c TNever seen

            | ty ->
                error.Add(ExpectEnum(enumId, ty))

                for c in e.content do
                    this.ProcessCondPat scope c TNever seen

        | StructPat(_) -> failwith "Not Implemented"
        | OrPat(_) -> failwith "Not Implemented"
        | RestPat(_) -> failwith "Not Implemented"
        | SelfPat _
        | RefSelfPat _ -> failwith "Unreachable"

    member internal this.ResolveTy ty =
        let onvar tvar =
            if tVarMap.ContainsKey tvar then
                this.ResolveTy tVarMap[tvar]
            else
                TVar tvar

        ty.Walk onvar

    member internal _.ResolveVar (scope: ActiveScope) (id: Id) =
        let resolve scope =
            if scope.var.ContainsKey id.sym then
                Some scope.var[id.sym]
            else
                None

        match scope.PickCurrent resolve with
        | Some var -> Some var
        | None ->
            error.Add(Undefined id)
            None

    member internal this.ProcessHoistedDecl (scope: ActiveScope) (decl: seq<Decl>) =
        let currScope = scope.current

        for d in decl do
            let dummyTVar _ =
                TVar
                    { scope = 0
                      id = 0
                      sym = None
                      span = Span.dummy }

            match d with
            | Let _
            | Const _ -> ()
            | FnDecl f ->
                if currScope.var.ContainsKey f.name.sym then
                    error.Add(DuplicateDefinition f.name)

                currScope.AddVar f.name
            | StructDecl s ->
                if currScope.ty.ContainsKey s.name.sym then
                    error.Add(DuplicateDefinition s.name)

                currScope.AddTy s.name
                let tvar = Array.map dummyTVar s.tyParam
                sema.ty.Add(s.name, TStruct(s.name, tvar))
            | EnumDecl e ->
                if currScope.ty.ContainsKey e.name.sym then
                    error.Add(DuplicateDefinition e.name)

                currScope.AddTy e.name
                let tvar = Array.map dummyTVar e.tyParam
                sema.ty.Add(e.name, TEnum(e.name, tvar))
            | TypeDecl t ->
                if currScope.ty.ContainsKey t.name.sym then
                    error.Add(DuplicateDefinition t.name)

                currScope.AddTy t.name
            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        let fn = ResizeArray()

        for d in decl do
            match d with
            | Let _
            | Const _ -> ()
            | FnDecl f -> fn.Add f
            | StructDecl s ->
                let scope, tvar =
                    if s.tyParam.Length > 0 then
                        let newScope = this.NewScope TypeScope

                        let processParam (param: TypeParam) =
                            let newTVar = newScope.NewTVar (Some param.id.sym) param.id.span

                            sema.ty.Add(param.id, TVar newTVar)
                            newScope.ty.Add(param.id.sym, param.id)

                            newTVar

                        scope.WithNew newScope, Array.map processParam s.tyParam
                    else
                        scope, [||]

                let processField m (field: StructFieldDef) =
                    let name = field.name.sym

                    if Map.containsKey name m then
                        error.Add(DuplicateField field.name)

                    Map.add name (this.ProcessTy scope field.ty) m

                let field = Array.fold processField Map.empty s.field

                let stru =
                    { name = s.name
                      field = field
                      tvar = tvar }

                sema.stru[s.name] <- stru

            | EnumDecl e ->
                let scope, tvar =
                    if e.tyParam.Length > 0 then
                        let newScope = this.NewScope TypeScope

                        let processParam (param: TypeParam) =
                            let newTVar = newScope.NewTVar (Some param.id.sym) param.id.span

                            sema.ty.Add(param.id, TVar newTVar)
                            newScope.ty.Add(param.id.sym, param.id)

                            newTVar

                        scope.WithNew newScope, Array.map processParam e.tyParam
                    else
                        scope, [||]

                let processVariant m (variant: EnumVariantDef) =
                    let name = variant.name.sym

                    if Map.containsKey name m then
                        error.Add(DuplicateVariant variant.name)

                    let payload = Array.map (this.ProcessTy scope) variant.payload

                    Map.add name payload m

                let variant = Array.fold processVariant Map.empty e.variant

                let enum =
                    { name = e.name
                      variant = variant
                      tvar = tvar }

                sema.enum[e.name] <- enum

            | TypeDecl t -> sema.ty[t.name] <- this.ProcessTy scope t.ty

            | Use(_) -> failwith "Not Implemented"
            | Trait(_) -> failwith "Not Implemented"
            | Impl(_) -> failwith "Not Implemented"

        for f in fn do
            let scope, tvar =
                if f.tyParam.Length > 0 then
                    let newScope = this.NewScope TypeScope

                    let processParam (param: TypeParam) =
                        let newTVar = newScope.NewTVar (Some param.id.sym) param.id.span

                        sema.ty.Add(param.id, TVar newTVar)
                        newScope.ty.Add(param.id.sym, param.id)

                        newTVar

                    scope.WithNew newScope, Array.map processParam f.tyParam
                else
                    scope, [||]

            let paramTy (p: Param) =
                match p.ty with
                | Some ty -> this.ProcessTy scope ty
                | None ->
                    let sym =
                        match p.pat with
                        | IdPat i -> Some(i.sym)
                        | _ -> None

                    let newTVar = currScope.NewTVar sym p.span

                    TVar newTVar

            let param = Array.map paramTy f.param

            let ret =
                match f.retTy with
                | Some ty -> this.ProcessTy scope ty
                | None -> TVar(currScope.NewTVar None f.span)

            let fnTy =
                TFn
                    { param = param
                      ret = ret
                      tvar = tvar }

            sema.AddVar f.name fnTy false

        for f in fn do
            this.InferFn scope f

    member internal this.ProcessDecl (scope: ActiveScope) d =
        match d with
        | Let l ->
            let value = this.TypeOfExpr scope l.value

            match l.ty with
            | Some ty ->
                scope.current.constr.Add(
                    CNormal
                        { expect = this.ProcessTy scope ty
                          actual = value
                          span = l.span }
                )
            | None -> ()

            this.ProcessDeclPat scope.current l.pat value l.mut (HashSet())

        | Const _ -> failwith "Not Implemented"
        | Use _ -> failwith "Not Implemented"
        | FnDecl _
        | StructDecl _
        | EnumDecl _
        | TypeDecl _
        | Trait _
        | Impl _ -> ()

    member internal _.TypeOfVar (scope: Scope) (id: Id) span =
        match sema.TypeOfVar id with
        | TFn f ->
            let newTVar = Array.map (fun _ -> scope.NewTVar None span) f.tvar
            TFn(f.Instantiate newTVar)
        | t -> t

    member internal this.TypeOfExpr (scope: ActiveScope) e =
        let currScope = scope.current

        match e with
        | Id id ->
            match this.ResolveVar scope id with
            | None -> TNever
            | Some id -> this.TypeOfVar currScope id id.span

        | Binary b ->
            let l = this.TypeOfExpr scope b.left
            let r = this.TypeOfExpr scope b.right

            match b.op with
            | Arithmetic(LogicalAnd | LogicalOr) ->
                currScope.constr.Add(
                    CNormal
                        { expect = TBool
                          actual = l
                          span = b.left.span }
                )

                currScope.constr.Add(
                    CNormal
                        { expect = TBool
                          actual = r
                          span = b.right.span }
                )

                TBool
            | Arithmetic _ ->
                currScope.constr.Add(
                    CNormal
                        { expect = TInt(true, ISize)
                          actual = l
                          span = b.left.span }
                )

                currScope.constr.Add(
                    CNormal
                        { expect = TInt(true, ISize)
                          actual = r
                          span = b.right.span }
                )

                TInt(true, ISize)
            | EqEq
            | NotEq
            | Lt
            | Gt
            | LtEq
            | GtEq ->
                currScope.constr.Add(
                    CNormal
                        { expect = l
                          actual = r
                          span = b.span }
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
            let processLetCond (c: LetCond) block =
                let value = this.TypeOfExpr scope c.value
                let newScope = this.NewScope BlockScope
                let scope = scope.WithNew newScope

                this.ProcessCondPat scope c.pat value (HashSet())
                let ty = this.InferBlock scope block

                this.Unify newScope
                this.ResolveTy ty

            let then_ =
                match i.cond with
                | BoolCond b ->
                    currScope.constr.Add(
                        CNormal
                            { expect = TBool
                              actual = this.TypeOfExpr scope b
                              span = b.span }
                    )

                    this.InferBlock scope i.then_
                | LetCond c -> processLetCond c i.then_

            for br in i.elseif do
                let elseif =
                    match br.cond with
                    | BoolCond b ->
                        currScope.constr.Add(
                            CNormal
                                { expect = TBool
                                  actual = this.TypeOfExpr scope b
                                  span = b.span }
                        )

                        this.InferBlock scope br.block
                    | LetCond c -> processLetCond c br.block

                currScope.constr.Add(
                    CNormal
                        { expect = then_
                          actual = elseif
                          span = i.span }
                )

            match i.else_ with
            | Some else_ ->
                let else_ = this.InferBlock scope else_

                currScope.constr.Add(
                    CNormal
                        { expect = then_
                          actual = else_
                          span = i.span }
                )
            | None ->
                currScope.constr.Add(
                    CNormal
                        { expect = then_
                          actual = UnitType
                          span = i.span }
                )

            then_
        | Match m ->
            let value = this.TypeOfExpr scope m.expr

            let typeOfBranch (br: MatchBranch) =
                let newScope = this.NewScope BlockScope
                let scope = scope.WithNew newScope

                this.ProcessCondPat scope br.pat value (HashSet())

                match br.guard with
                | Some g ->
                    newScope.constr.Add(
                        CNormal
                            { actual = this.TypeOfExpr scope g
                              expect = TBool
                              span = g.span }
                    )
                | None -> ()

                let brTy = this.TypeOfExpr scope br.expr

                this.Unify newScope

                this.ResolveTy brTy

            if Array.length m.branch = 0 then
                UnitType
            else
                let first = typeOfBranch m.branch[0]

                for br in m.branch[1..] do
                    let brTy = typeOfBranch br

                    currScope.constr.Add(
                        CNormal
                            { expect = first
                              actual = brTy
                              span = br.span }
                    )

                first

        | Block b -> this.InferBlock scope b
        | Call c ->
            let callee = this.TypeOfExpr scope c.callee

            let arg = Array.map (this.TypeOfExpr scope) c.arg
            let ret = TVar(currScope.NewTVar None c.span)

            currScope.constr.Add(
                CNormal
                    { expect = TFn { param = arg; ret = ret; tvar = [||] }
                      actual = callee
                      span = c.span }
            )

            ret
        | Unary u ->
            match u.op with
            | Not ->
                currScope.constr.Add(
                    CNormal
                        { expect = TBool
                          actual = this.TypeOfExpr scope u.expr
                          span = u.span }
                )

                TBool
            | Neg ->
                currScope.constr.Add(
                    CNormal
                        { expect = TInt(true, ISize)
                          actual = this.TypeOfExpr scope u.expr
                          span = u.span }
                )

                TInt(true, ISize)
            | Ref -> TRef(this.TypeOfExpr scope u.expr)
            | Deref ->
                let ptr = TVar(currScope.NewTVar None u.expr.span)

                currScope.constr.Add(
                    CNormal
                        { expect = TRef ptr
                          actual = this.TypeOfExpr scope u.expr
                          span = u.span }
                )

                ptr
        | Assign a ->
            let value = this.TypeOfExpr scope a.value

            match a.place with
            | Id i ->
                let span = a.place.span
                let id = this.ResolveVar scope i

                match id with
                | Some id ->
                    let varInfo = sema.var[id]

                    if not varInfo.mut then
                        error.Add(AssignImmutable(id, span))

                    currScope.constr.Add(
                        CNormal
                            { expect = varInfo.ty
                              actual = value
                              span = a.span }
                    )

                    ()
                | None -> ()
            | _ -> failwith "Not Implemented"

            UnitType
        | Field f ->
            let receiver = this.TypeOfExpr scope f.receiver
            let key = f.prop.sym

            match receiver with
            | TStruct(i, inst) ->
                let stru = sema.stru[i]

                match Map.tryFind key stru.field with
                | Some f -> f.Instantiate stru.tvar inst
                | None ->
                    error.Add(UndefinedField(f.span, key))

                    TNever
            | _ ->
                let rec findStruct scope =
                    let tySeq = scope.ty |> Seq.map (|KeyValue|) |> Seq.rev

                    let find (_, ty) =
                        if sema.stru.ContainsKey ty then
                            let stru = sema.stru[ty]

                            match Map.tryFind key stru.field with
                            | Some t -> Some stru
                            | None -> None
                        else
                            None

                    Seq.tryPick find tySeq

                let stru = scope.PickCurrent findStruct

                match stru with
                | Some s ->
                    let inst = Array.map (fun _ -> TVar(currScope.NewTVar None f.span)) s.tvar

                    currScope.constr.Add(
                        CDeref
                            { expect = TStruct(s.name, inst)
                              actual = receiver
                              span = f.span }
                    )

                    s.field[key].Instantiate s.tvar inst
                | None ->
                    error.Add(UndefinedField(f.span, key))
                    TNever

        | Index(_) -> failwith "Not Implemented"
        | Array(_) -> failwith "Not Implemented"
        | ArrayRepeat(_) -> failwith "Not Implemented"
        | StructLit(_) -> failwith "Not Implemented"
        | Tuple s -> Array.map (this.TypeOfExpr scope) s.element |> TTuple
        | Closure c ->
            let paramTy (p: Param) =
                match p.ty with
                | Some ty -> this.ProcessTy scope ty
                | None ->
                    let sym =
                        match p.pat with
                        | IdPat i -> Some(i.sym)
                        | _ -> None

                    let newTVar = currScope.NewTVar sym p.span

                    TVar newTVar

            let paramTy = Array.map paramTy c.param

            let retTy =
                match c.ret with
                | Some ty -> this.ProcessTy scope ty
                | None -> TVar(currScope.NewTVar None c.span)

            let closureScope = this.NewScope(FnScope retTy)

            let seen = HashSet()

            for (param, ty) in Array.zip c.param paramTy do
                this.ProcessDeclPat closureScope param.pat ty true seen

            let newScope = scope.WithNew closureScope

            let ret = this.TypeOfExpr newScope c.body

            closureScope.constr.Add(
                CNormal
                    { expect = retTy
                      actual = ret
                      span = c.span }
            )

            this.Unify closureScope

            let resolve ty = this.ResolveTy ty

            TFn
                { param = Array.map resolve paramTy
                  ret = resolve retTy
                  tvar = [||] }

        | Path _ -> failwith "Not Implemented"
        | Break _ -> TNever
        | Continue _ -> TNever
        | Return r ->
            let pickFn scope =
                match scope.data with
                | FnScope f -> Some f
                | _ -> None

            let retTy =
                match scope.PickCurrent pickFn with
                | Some retTy -> retTy
                | None -> failwith "Unreachable"

            let ty =
                match r.value with
                | Some v -> this.TypeOfExpr scope v
                | None -> UnitType

            currScope.constr.Add(
                CNormal
                    { expect = retTy
                      actual = ty
                      span = r.span }
            )

            TNever
        | Range(_) -> failwith "Not Implemented"
        | For(_) -> failwith "Not Implemented"
        | While(_) -> failwith "Not Implemented"
        | TryReturn(_) -> failwith "Not Implemented"

    member internal this.InferBlock (scope: ActiveScope) (b: Block) =
        let blockScope = this.NewScope BlockScope

        let scope = scope.WithNew blockScope

        let chooseDecl s =
            match s with
            | DeclStmt d -> Some d
            | ExprStmt _ -> None

        let decl = Seq.choose chooseDecl b.stmt

        this.ProcessHoistedDecl scope decl

        let typeof _ stmt =
            match stmt with
            | DeclStmt d ->
                this.ProcessDecl scope d

                UnitType
            | ExprStmt e -> this.TypeOfExpr scope e

        let ty = Array.fold typeof UnitType b.stmt

        this.Unify blockScope

        this.ResolveTy ty

    member internal this.InferFn (scope: ActiveScope) (f: Fn) =
        let fnTy =
            match sema.TypeOfVar f.name with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        let fnScope = this.NewScope(FnScope fnTy.ret)

        let seen = HashSet()

        for (param, ty) in Array.zip f.param fnTy.param do
            this.ProcessDeclPat fnScope param.pat ty true seen

        let newScope = scope.WithNew fnScope

        let ret = this.InferBlock newScope f.body

        fnScope.constr.Add(
            CNormal
                { expect = fnTy.ret
                  actual = ret
                  span = f.name.span }
        )

        this.Unify fnScope

        let mapper ty =
            match this.ResolveTy ty with
            | TFn f -> TFn(f.Generalize scope.current.id)
            | _ -> failwith "Unreachable"

        sema.ModifyVarTy f.name mapper

    member internal this.Unify scope =
        let rec unify_normal c may_deref =
            let addMap v ty =
                if tVarMap.ContainsKey v then
                    let oldTy = tVarMap[v]

                    unify_normal
                        { expect = ty
                          actual = oldTy
                          span = c.span }
                        may_deref

                    tVarMap[v] <- this.ResolveTy oldTy
                else
                    tVarMap[v] <- ty

            match c.expect, c.actual with
            | p1, p2 when p1 = p2 -> ()
            | TVar v1, TVar v2 ->
                if v1.scope > v2.scope then
                    addMap v1 (TVar v2)
                else if v1.scope = v2.scope then
                    if v1.id > v2.id then
                        addMap v1 (TVar v2)
                    else
                        addMap v2 (TVar v1)
                else
                    addMap v2 (TVar v1)
            | TVar v, ty
            | ty, TVar v ->
                let ty = this.ResolveTy ty

                match ty.FindTVar |> Seq.tryFind ((=) v) with
                | Some _ -> error.Add(FailToUnify(c.expect, c.actual, c.span))
                | None -> addMap v ty

            | TFn f1, TFn f2 ->
                if f1.param.Length <> f2.param.Length then
                    error.Add(TypeMismatch(c.expect, c.actual, c.span))
                else
                    for (p1, p2) in (Array.zip f1.param f2.param) do
                        unify_normal
                            { expect = p1
                              actual = p2
                              span = c.span }
                            may_deref

                    unify_normal
                        { expect = f1.ret
                          actual = f2.ret
                          span = c.span }
                        false

            | TRef r1, TRef r2 ->
                unify_normal
                    { expect = r1
                      actual = r2
                      span = c.span }
                    false

            | TRef r, t
            | t, TRef r when may_deref ->
                unify_normal
                    { expect = r.StripRef
                      actual = t
                      span = c.span }
                    false
            | TNever, _
            | _, TNever -> ()
            | TStruct(id1, v1), TStruct(id2, v2)
            | TEnum(id1, v1), TEnum(id2, v2) when id1 = id2 ->
                for (v1, v2) in Array.zip v1 v2 do
                    unify_normal
                        { expect = v1
                          actual = v2
                          span = c.span }
                        false
            | TTuple t1, TTuple t2 ->
                if t1.Length <> t2.Length then
                    error.Add(TupleLengthMismatch(c.span, t1.Length, t2.Length))
                else
                    for (t1, t2) in Array.zip t1 t2 do
                        unify_normal
                            { expect = t1
                              actual = t2
                              span = c.span }
                            false
            | _, _ -> error.Add(TypeMismatch(c.expect, c.actual, c.span))

        for c in scope.constr do
            match c with
            | CNormal c -> unify_normal c false
            | CDeref c -> unify_normal c true

        for id in scope.var.Values do
            sema.ModifyVarTy id this.ResolveTy

    member this.Check m =
        let topLevel = this.NewScope TopLevelScope
        let scope = { scope = [| Scope.Prelude; topLevel |] }

        let getDecl m = m.decl

        let decl = Array.map getDecl m.item

        this.ProcessHoistedDecl scope decl

        for d in decl do
            this.ProcessDecl scope d

        this.Unify topLevel

    member _.GetInfo = sema

    member _.GetError = error
