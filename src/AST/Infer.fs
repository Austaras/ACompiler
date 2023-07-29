/// Perform HM type inference on AST
module AST.TypeInfer

open System.Collections.Generic
// TODO: ADT
// TODO: trait and type alias
// TODO: operator overloading
// TODO: pattern match
// TODO: closure

open AST.AST
open AST.Type

type Error =
    | Undefined of Id
    | UndefinedField of Span * string
    | UndefinedVariant of Id * Id
    | DuplicateDefinition of Id
    | DuplicateField of Id
    | DuplicateVariant of Id
    | LoopInDefintion of Id * Id
    | PrivateInPublic of Id * Id
    | ExpectEnum of Id * Type
    | PayloadNumMismatch of Span * Enum
    | TypeMismatch of Type * Type * Span
    | ArgumentCountMismatch of int * int * Span
    | CalleeNotCallable of Type * Span
    | CannotAssign of Id * Span
    | RefutablePat of Span

let internal primitive =
    [| Int(true, I8)
       Int(false, I8)
       Int(true, I32)
       Int(false, I32)
       Int(true, I64)
       Int(false, I64)
       Int(true, ISize)
       Int(false, ISize)
       Bool
       F32
       F64 |]

type internal Constraint =
    { expect: Type
      actual: Type
      span: Span }

type internal Scope =
    { ty: Dictionary<string, Id>
      var: Dictionary<string, Id>
      mut: HashSet<string>
      constr: ResizeArray<Constraint>
      id: int
      retTy: Option<Type>
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

    static member Empty id retTy =
        { ty = Dictionary()
          var = Dictionary()
          mut = HashSet()
          constr = ResizeArray()
          id = id
          retTy = retTy
          varId = 0 }

    static member Prelude =
        let env =
            { ty = Dictionary()
              var = Dictionary()
              mut = HashSet()
              constr = ResizeArray()
              id = 0
              retTy = None
              varId = 0 }

        for p in primitive do
            let name = p.str
            env.ty[p.str] <- { sym = name; span = Span.dummy }

        env

type Context(moduleMap) =
    let mutable scopeId = 0

    let binding =
        let binding =
            { var = Dictionary()
              ty = Dictionary()
              stru = Dictionary()
              enum = Dictionary() }

        for t in primitive do
            let id = { sym = t.str; span = Span.dummy }

            binding.ty[id] <- TPrim t

        binding

    let tVarMap = Dictionary<Var, Type>()
    let error = ResizeArray<Error>()

    member internal this.NewScope retTy =
        scopeId <- scopeId + 1
        Scope.Empty scopeId retTy

    member internal this.GetVarFromEnv id scope =
        if Array.length scope = 0 then
            error.Add(Undefined id)
            TNever
        else
            let curr = Array.last scope

            if curr.var.ContainsKey id.sym then
                let make () = curr.NewTVar None id.span

                match binding.var[curr.var[id.sym]] with
                | TFn f -> TFn(f.Instantiate make)
                | t -> t
            else
                this.GetVarFromEnv id scope[0 .. (Array.length scope - 2)]

    member internal this.ProcessTy (scope: Scope[]) ty =
        let rec resolve (id: Id) (e: Scope[]) =
            let len = e.Length

            if len = 0 then
                TNever
            else
                let last = e[len - 1]

                if last.ty.ContainsKey id.sym then
                    let id = last.ty[id.sym]

                    binding.ty[id]
                else
                    resolve id e[0 .. (len - 2)]

        match ty with
        | NeverType _ -> TNever
        | TypeId i -> resolve i scope
        | TupleType t -> Tuple(Array.map (this.ProcessTy scope) t.element)
        | RefType r -> TRef(this.ProcessTy scope r.ty)
        | LitType(_, _) -> failwith "Not Implemented"
        | ArrayType(_) -> failwith "Not Implemented"
        | InferedType(_) -> failwith "Not Implemented"
        | FnType(_) -> failwith "Not Implemented"
        | PathType(_) -> failwith "Not Implemented"

    member internal this.ProcessDeclPat scope pat ty =
        match pat with
        | IdPat i ->
            scope.var[i.sym] <- i
            binding.var[i] <- ty
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
                this.ProcessDeclPat scope pat newVar

                newVar

            let patTy = Array.map addBinding t.element

            scope.constr.Add
                { actual = Tuple patTy
                  expect = ty
                  span = t.span }
        | AsPat a ->
            scope.var[a.id.sym] <- a.id
            binding.var[a.id] <- ty

            this.ProcessDeclPat scope a.pat ty
        | ArrayPat(_) -> failwith "Not Implemented"
        | PathPat(_) -> failwith "Not Implemented"
        | EnumPat(_) -> failwith "Not Implemented"
        | StructPat(_) -> failwith "Not Implemented"
        | OrPat(_) -> failwith "Not Implemented"
        | RestPat(_) -> failwith "Not Implemented"
        | SelfPat(_) -> failwith "Not Implemented"
        | RefSelfPat(_) -> failwith "Not Implemented"

    member internal this.ProcessCondPat scope pat ty =
        let currScope = Array.last scope

        match pat with
        | IdPat i ->
            currScope.var[i.sym] <- i
            binding.var[i] <- ty
        | LitPat(l, span) ->
            let litTy =
                match l with
                | AST.Int _ -> TPrim(Int(true, I32))
                | AST.Bool _ -> TPrim Bool
                | AST.Char _ -> TPrim Char
                | AST.Float _ -> TPrim F64
                | AST.String _ -> failwith "Not Implemented"
                | AST.NegInt _ -> failwith "Unreachable"

            currScope.constr.Add
                { actual = litTy
                  expect = ty
                  span = span }
        | RangePat _ -> failwith "Not Implemented"
        | CatchAllPat _ -> ()
        | TuplePat t ->
            let addBinding pat =
                let sym =
                    match pat with
                    | IdPat id -> Some id.sym
                    | _ -> None

                let newVar = currScope.NewTVar sym pat.span |> TVar
                this.ProcessCondPat scope pat newVar

                newVar

            let patTy = Array.map addBinding t.element

            currScope.constr.Add
                { actual = Tuple patTy
                  expect = ty
                  span = t.span }
        | AsPat a ->
            currScope.var[a.id.sym] <- a.id
            binding.var[a.id] <- ty

            this.ProcessCondPat scope a.pat ty
        | ArrayPat(_) -> failwith "Not Implemented"
        | PathPat(_) -> failwith "Not Implemented"
        | EnumPat e ->
            if e.name.prefix <> None || e.name.seg.Length <> 2 then
                failwith "Not Implemented"

            let enumId = e.name.seg[0]
            let variant = e.name.seg[1]

            let rec findEnum scope =
                let last = Array.last scope

                if last.ty.ContainsKey enumId.sym then
                    let id = last.ty[enumId.sym]
                    binding.ty[id]
                else if scope.Length > 1 then
                    findEnum scope[.. scope.Length - 2]
                else
                    error.Add(Undefined enumId)
                    TNever

            let enumTy = findEnum scope

            currScope.constr.Add
                { expect = enumTy
                  actual = ty
                  span = e.span }

            match enumTy with
            | TEnum enum ->
                let enumData = binding.enum[enum]

                if enumData.variant.ContainsKey variant.sym then
                    let payload = enumData.variant[variant.sym]

                    if payload.Length <> e.content.Length then
                        error.Add(PayloadNumMismatch(e.span, enumData))

                    for idx, c in e.content |> Array.indexed do
                        let payload = if idx < payload.Length then payload[idx] else TNever

                        this.ProcessCondPat scope c payload
                else
                    error.Add(UndefinedVariant(enumId, variant))

                    for c in e.content do
                        this.ProcessCondPat scope c TNever

            | ty ->
                error.Add(ExpectEnum(enumId, ty))

                for c in e.content do
                    this.ProcessCondPat scope c TNever

        | StructPat(_) -> failwith "Not Implemented"
        | OrPat(_) -> failwith "Not Implemented"
        | RestPat(_) -> failwith "Not Implemented"
        | SelfPat(_) -> failwith "Not Implemented"
        | RefSelfPat(_) -> failwith "Not Implemented"

    member internal this.ResolveTy ty =
        let onvar tvar =
            if tVarMap.ContainsKey tvar then
                this.ResolveTy tVarMap[tvar]
            else
                TVar tvar

        ty.Walk onvar

    member internal this.Unify scope =
        let rec unify c =
            let addMap v ty =
                if tVarMap.ContainsKey v then
                    let oldTy = tVarMap[v]

                    unify
                        { expect = ty
                          actual = oldTy
                          span = c.span }

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

                addMap v ty

            | TFn f1, TFn f2 ->
                if f1.param.Length <> f2.param.Length then
                    error.Add(TypeMismatch(c.expect, c.actual, c.span))
                else
                    for (idx, p1) in (Array.indexed f1.param) do
                        unify
                            { expect = p1
                              actual = f2.param[idx]
                              span = c.span }

                    unify
                        { expect = f1.ret
                          actual = f2.ret
                          span = c.span }
            | TRef r1, TRef r2 ->
                unify
                    { expect = r1
                      actual = r2
                      span = c.span }
            | TNever, _
            | _, TNever -> ()
            | _, _ -> error.Add(TypeMismatch(c.expect, c.actual, c.span))

        for c in scope.constr do
            unify c

        for id in scope.var.Values do
            binding.var[id] <- this.ResolveTy binding.var[id]

    member internal this.HoistDeclName (scope: Scope) d =
        match d with
        | Let _
        | Const _ -> ()
        | FnDecl f ->
            if scope.var.ContainsKey f.name.sym then
                error.Add(DuplicateDefinition f.name)

            scope.AddVar f.name
        | StructDecl s ->
            if scope.ty.ContainsKey s.name.sym then
                error.Add(DuplicateDefinition s.name)

            scope.AddTy s.name
            binding.ty.Add(s.name, (TStruct s.name))
        | EnumDecl e ->
            if scope.ty.ContainsKey e.name.sym then
                error.Add(DuplicateDefinition e.name)

            scope.AddTy e.name
            binding.ty.Add(e.name, (TEnum e.name))
        | TypeDecl t ->
            if scope.ty.ContainsKey t.name.sym then
                error.Add(DuplicateDefinition t.name)

            scope.AddTy t.name
        | Use(_) -> failwith "Not Implemented"
        | Trait(_) -> failwith "Not Implemented"
        | Impl(_) -> failwith "Not Implemented"

    member internal this.HoistDecl (scope: Scope[]) d =
        let currScope = Array.last scope

        match d with
        | Let _
        | Const _ -> ()
        | FnDecl f ->
            let paramTy (p: Param) =
                let sym =
                    match p.pat with
                    | IdPat i -> Some(i.sym)
                    | _ -> None

                let newTVar = currScope.NewTVar sym p.span

                match p.ty with
                | Some ty ->
                    let ty = this.ProcessTy scope ty

                    currScope.constr.Add
                        { expect = ty
                          actual = TVar newTVar
                          span = p.span }

                | None -> ()

                TVar newTVar

            let param = Array.map paramTy f.param

            let ret = TVar(currScope.NewTVar None f.span)

            match f.retTy with
            | Some ty ->
                currScope.constr.Add
                    { expect = this.ProcessTy scope ty
                      actual = ret
                      span = f.name.span }
            | None -> ()

            binding.var[f.name] <-
                TFn
                    { param = param
                      ret = ret
                      tvar = [||] }

        | StructDecl s ->
            if s.tyParam.Length > 0 then
                failwith "Not Implemented"

            let processField m (field: StructFieldDef) =
                let name = field.name.sym

                if Map.containsKey name m then
                    error.Add(DuplicateField field.name)

                Map.add name (this.ProcessTy scope field.ty) m

            let field = Array.fold processField Map.empty s.field

            let stru = { name = s.name; field = field }

            binding.ty[s.name] <- TStruct s.name
            binding.stru[s.name] <- stru

        | EnumDecl e ->
            if e.tyParam.Length > 0 then
                failwith "Not Implemented"

            let processVariant m (variant: EnumVariantDef) =
                let name = variant.name.sym

                if Map.containsKey name m then
                    error.Add(DuplicateField variant.name)

                let payload = Array.map (this.ProcessTy scope) variant.payload

                Map.add name payload m

            let variant = Array.fold processVariant Map.empty e.variant

            let enum = { name = e.name; variant = variant }

            binding.ty[e.name] <- TEnum e.name
            binding.enum[e.name] <- enum

        | TypeDecl t -> binding.ty[t.name] <- this.ProcessTy scope t.ty

        | Use(_) -> failwith "Not Implemented"
        | Trait(_) -> failwith "Not Implemented"
        | Impl(_) -> failwith "Not Implemented"

    member internal this.TypeOfExpr (scope: Scope[]) e =
        let currScope = Array.last scope

        match e with
        | Binary b ->
            let l = this.TypeOfExpr scope b.left
            let r = this.TypeOfExpr scope b.right

            match b.op with
            | Arithmetic(LogicalAnd | LogicalOr) ->
                currScope.constr.Add
                    { expect = TPrim Bool
                      actual = l
                      span = b.left.span }

                currScope.constr.Add
                    { expect = TPrim Bool
                      actual = r
                      span = b.right.span }

                TPrim Bool
            | Arithmetic _ ->
                currScope.constr.Add
                    { expect = TPrim(Int(true, I32))
                      actual = l
                      span = b.left.span }

                currScope.constr.Add
                    { expect = TPrim(Int(true, I32))
                      actual = r
                      span = b.right.span }

                TPrim(Int(true, I32))
            | EqEq
            | NotEq
            | Lt
            | Gt
            | LtEq
            | GtEq ->
                currScope.constr.Add
                    { expect = l
                      actual = r
                      span = b.span }

                TPrim Bool
            | Pipe -> failwith "Not Implemented"
            | As -> failwith "Not Implemented"

        | Id v -> this.GetVarFromEnv v scope
        | SelfExpr(_) -> failwith "Not Implemented"
        | LitExpr(l, _) ->
            match l with
            | AST.Int _ -> TPrim(Int(true, I32))
            | AST.Bool _ -> TPrim Bool
            | AST.Char _ -> TPrim Char
            | AST.Float _ -> TPrim F64
            | AST.String _ -> failwith "Not Implemented"
            | AST.NegInt _ -> failwith "Unreachable"

        | If i ->
            let processLetCond (c: LetCond) block =
                let value = this.TypeOfExpr scope c.value
                let newScope = this.NewScope None
                let scope = Array.append scope [| newScope |]

                this.ProcessCondPat scope c.pat value
                let ty = this.InferBlock scope block

                this.Unify newScope
                this.ResolveTy ty

            let then_ =
                match i.cond with
                | BoolCond b ->
                    currScope.constr.Add
                        { expect = TPrim Bool
                          actual = this.TypeOfExpr scope b
                          span = b.span }

                    this.InferBlock scope i.then_
                | LetCond c -> processLetCond c i.then_

            for br in i.elseif do
                let elseif =
                    match br.cond with
                    | BoolCond b ->
                        currScope.constr.Add
                            { expect = TPrim Bool
                              actual = this.TypeOfExpr scope b
                              span = b.span }

                        this.InferBlock scope br.block
                    | LetCond c -> processLetCond c br.block

                currScope.constr.Add
                    { expect = then_
                      actual = elseif
                      span = i.span }

            match i.else_ with
            | Some else_ ->
                let else_ = this.InferBlock scope else_

                currScope.constr.Add
                    { expect = then_
                      actual = else_
                      span = i.span }
            | None ->
                currScope.constr.Add
                    { expect = then_
                      actual = UnitType
                      span = i.span }

            then_
        | Match m ->
            let value = this.TypeOfExpr scope m.expr

            let typeOfBranch (br: MatchBranch) =
                let newScope = this.NewScope None
                let scope = Array.append scope [| newScope |]

                this.ProcessCondPat scope br.pat value

                match br.guard with
                | Some g ->
                    newScope.constr.Add
                        { actual = this.TypeOfExpr scope g
                          expect = TPrim Bool
                          span = g.span }
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

                    currScope.constr.Add
                        { expect = first
                          actual = brTy
                          span = br.span }

                first

        | Block b -> this.InferBlock scope b
        | Call c ->
            let callee = this.TypeOfExpr scope c.callee

            let arg = Array.map (this.TypeOfExpr scope) c.arg
            let ret = TVar(currScope.NewTVar None c.span)

            currScope.constr.Add
                { expect = TFn { param = arg; ret = ret; tvar = [||] }
                  actual = callee
                  span = c.span }

            ret
        | Unary u ->
            match u.op with
            | Not ->
                currScope.constr.Add
                    { expect = TPrim Bool
                      actual = this.TypeOfExpr scope u.expr
                      span = u.span }

                TPrim Bool
            | Neg ->
                currScope.constr.Add
                    { expect = TPrim(Int(true, I32))
                      actual = this.TypeOfExpr scope u.expr
                      span = u.span }

                TPrim(Int(true, I32))
            | Ref -> TRef(this.TypeOfExpr scope u.expr)
            | Deref ->
                let ptr = TVar(currScope.NewTVar None u.expr.span)

                currScope.constr.Add
                    { expect = TRef ptr
                      actual = this.TypeOfExpr scope u.expr
                      span = u.span }

                ptr
        | Assign(_) -> failwith "Not Implemented"
        | Field f ->
            let key = f.prop.sym

            let rec findStruct scope =
                let last = Array.last scope
                let tySeq = last.ty |> Seq.map (|KeyValue|) |> Seq.rev

                let find (_, ty) =
                    if binding.stru.ContainsKey ty then
                        let stru = binding.stru[ty]

                        match Map.tryFind key stru.field with
                        | Some t -> Some(t, Some(stru))
                        | None -> None
                    else
                        None

                match Seq.tryPick find tySeq with
                | Some s -> s
                | None ->
                    if scope.Length > 1 then
                        findStruct scope[.. scope.Length - 2]
                    else
                        error.Add(UndefinedField(f.span, key))
                        TNever, None

            let field, stru = findStruct scope

            match stru with
            | Some s ->
                currScope.constr.Add
                    { expect = TStruct s.name
                      actual = this.TypeOfExpr scope f.receiver
                      span = f.span }
            | None -> ()

            field

        | Index(_) -> failwith "Not Implemented"
        | Array(_) -> failwith "Not Implemented"
        | ArrayRepeat(_) -> failwith "Not Implemented"
        | StructLit(_) -> failwith "Not Implemented"
        | AST.Tuple s -> Array.map (this.TypeOfExpr scope) s.element |> Tuple
        | Closure(_) -> failwith "Not Implemented"
        | Path(_) -> failwith "Not Implemented"
        | Break _ -> TNever
        | Continue _ -> TNever
        | Return r ->
            let retTy =
                match (Array.last scope).retTy with
                | Some retTy -> retTy
                | None -> failwith "Unreachable"

            let ty =
                match r.value with
                | Some v -> this.TypeOfExpr scope v
                | None -> UnitType

            currScope.constr.Add
                { expect = retTy
                  actual = ty
                  span = r.span }

            TNever
        | Range(_) -> failwith "Not Implemented"
        | For(_) -> failwith "Not Implemented"
        | While(_) -> failwith "Not Implemented"
        | TryReturn(_) -> failwith "Not Implemented"

    member internal this.InferBlock (scope: Scope[]) (b: Block) =
        let blockScope = this.NewScope (Array.last scope).retTy
        let scope = Array.append scope [| blockScope |]

        let typeof _ stmt =
            match stmt with
            | DeclStmt _ -> failwith "Not Implemented"
            | ExprStmt e -> this.TypeOfExpr scope e

        let ty = Array.fold typeof UnitType b.stmt

        this.Unify blockScope

        this.ResolveTy ty

    member internal this.InferFn (scope: Scope[]) (f: Fn) =
        let fnTy =
            match binding.var[f.name] with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        let fnScope = this.NewScope(Some fnTy.ret)

        for (idx, p) in f.param |> Array.indexed do
            this.ProcessDeclPat fnScope p.pat fnTy.param[idx]

        let newScope = Array.append scope [| fnScope |]

        let ret = this.InferBlock newScope f.body

        fnScope.constr.Add
            { expect = fnTy.ret
              actual = ret
              span = f.name.span }

        this.Unify fnScope

        binding.var[f.name] <-
            match this.ResolveTy binding.var[f.name] with
            | TFn f -> TFn(f.Generalize (Array.last scope).id)
            | _ -> failwith "Unreachable"

    member this.Infer m =
        let topLevel = this.NewScope None

        for { decl = decl } in m.item do
            this.HoistDeclName topLevel decl

        let scope = [| Scope.Prelude; topLevel |]

        for { decl = decl } in m.item do
            this.HoistDecl scope decl

        for { decl = decl } in m.item do
            match decl with
            | FnDecl f -> this.InferFn scope f
            | Let _ -> failwith "Not Implemented"
            | Const _ -> failwith "Not Implemented"
            | StructDecl _
            | EnumDecl _
            | TypeDecl _ -> ()
            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        this.Unify topLevel

    member this.GetTypes = binding

    member this.GetError = error
