/// Perform HM type inference on AST
module AST.TypeInfer

open System.Collections.Generic
// TODO: ADT
// TODO: trait and type alias
// TODO: operator overloading
// TODO: pattern match and destructing
// TODO: closure

open AST.AST
open AST.Type

type Error =
    | Undefined of Id
    | UndefinedField of Span * string
    | UndefinedVariant of Id * string
    | DuplicateDefinition of Id
    | DuplicateField of Id
    | DuplicateVariant of Id
    | LoopInDefintion of Id * Id
    | PrivateInPublic of Id * Id
    | TypeMismatch of Type * Type * Span
    | ArgumentCountMismatch of int * int * Span
    | CalleeNotCallable of Type * Span
    | CannotAssign of Id * Span

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
      mutable varId: int }

    member this.AddTy(id: Id) = this.ty[id.sym] <- id

    member this.AddVar(id: Id) = this.var[id.sym] <- id

    member this.newTVar sym span =
        let tvar =
            { scope = this.id
              id = this.varId
              sym = sym
              span = span }

        this.varId <- this.varId + 1

        tvar

    static member Empty id =
        { ty = Dictionary()
          var = Dictionary()
          mut = HashSet()
          constr = ResizeArray()
          id = id
          varId = 0 }

    static member Prelude =
        let env =
            { ty = Dictionary()
              var = Dictionary()
              mut = HashSet()
              constr = ResizeArray()
              id = 0
              varId = 0 }

        for p in primitive do
            let name = p.str
            env.ty[p.str] <- { sym = name; span = Span.dummy }

        env

type Context(moduleMap) =
    let mutable scopeId = 0

    let tyMap =
        let ty = Dictionary<Id, Type>()

        for t in primitive do
            let id = { sym = t.str; span = Span.dummy }

            ty[id] <- Primitive t

        ty

    let binding = Dictionary<Id, Type>()

    let error = ResizeArray<Error>()

    member internal this.newScope =
        scopeId <- scopeId + 1
        Scope.Empty scopeId

    member internal this.GetVarFromEnv id env =
        if Array.length env = 0 then
            error.Add(Undefined id)
            TNever
        else
            let last = Array.last env

            if last.var.ContainsKey id.sym then
                binding[last.var[id.sym]]
            else
                this.GetVarFromEnv id env[0 .. (Array.length env - 2)]

    member internal this.ProcessTy (scope: Scope[]) ty =
        let rec resolve (id: Id) (e: Scope[]) =
            let len = e.Length

            if len = 0 then
                TNever
            else
                let last = e[len - 1]

                if last.ty.ContainsKey id.sym then
                    let id = last.ty[id.sym]

                    // may recursive
                    if e.Length = scope.Length then TNever else tyMap[id]
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
        | EnumDecl e ->
            if scope.ty.ContainsKey e.name.sym then
                error.Add(DuplicateDefinition e.name)

            scope.AddTy e.name
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

                let newTVar = currScope.newTVar sym p.span

                match p.ty with
                | Some ty ->
                    let ty = this.ProcessTy scope ty

                    scope[1].constr.Add
                        { expect = ty
                          actual = TVar newTVar
                          span = p.span }

                | None -> ()

                TVar newTVar

            let param = Array.map paramTy f.param

            // fake ident for return type
            let ret = TVar(currScope.newTVar None f.span)

            match f.retTy with
            | Some ty ->
                scope[1].constr.Add
                    { expect = this.ProcessTy scope ty
                      actual = ret
                      span = f.name.span }
            | None -> ()

            binding[f.name] <- TFn { param = param; ret = ret }

        | StructDecl s ->
            if s.tyParam.Length > 0 then
                failwith "Not Implemented"

            let processField m (field: StructFieldDef) =
                let name = field.name.sym

                if Map.containsKey name m then
                    error.Add(DuplicateField field.name)

                Map.add name (this.ProcessTy scope field.ty) m

            let field = Array.fold processField Map.empty s.field

            let strct = { name = s.name; field = field }

            tyMap[s.name] <- TStruct strct

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

            tyMap[e.name] <- TEnum enum

        | TypeDecl t -> tyMap[t.name] <- this.ProcessTy scope t.ty

        | Use(_) -> failwith "Not Implemented"
        | Trait(_) -> failwith "Not Implemented"
        | Impl(_) -> failwith "Not Implemented"

    member internal this.TypeOfExpr (scope: Scope[]) e =
        let currScope = Array.last scope

        match e with
        | Binary b ->
            let l = this.TypeOfExpr scope b.left
            let r = this.TypeOfExpr scope b.right

            scope[1].constr.Add
                { expect = Primitive(Int(true, I32))
                  actual = l
                  span = b.left.span }

            scope[1].constr.Add
                { expect = Primitive(Int(true, I32))
                  actual = r
                  span = b.right.span }

            match b.op with
            | Arithmetic _ -> Primitive(Int(true, I32))
            | EqEq
            | NotEq
            | Lt
            | Gt
            | LtEq
            | GtEq -> Primitive Bool
            | Pipe -> failwith "Not Implemented"
            | As -> failwith "Not Implemented"
        | Id v -> this.GetVarFromEnv v scope
        | SelfExpr(_) -> failwith "Not Implemented"
        | LitExpr(l, _) ->
            match l with
            | AST.Int _ -> Primitive(Int(true, I32))
            | AST.Bool _ -> Primitive Bool
            | AST.Char _ -> Primitive Char
            | AST.Float _ -> Primitive F64
            | AST.String _ -> failwith "Not Implemented"
            | AST.NegInt _ -> failwith "Unreachable"
        | If i ->
            let cond, span =
                match i.cond with
                | BoolCond b -> this.TypeOfExpr scope b, b.span
                | LetCond(_) -> failwith "Not Implemented"

            scope[1].constr.Add
                { expect = Primitive Bool
                  actual = cond
                  span = span }

            let then_ = this.InferBlock i.then_ scope

            for br in i.elseif do
                let cond, span =
                    match i.cond with
                    | BoolCond b -> this.TypeOfExpr scope b, b.span
                    | LetCond(_) -> failwith "Not Implemented"

                scope[1].constr.Add
                    { expect = Primitive Bool
                      actual = cond
                      span = span }

                let elseif = this.InferBlock br.block scope

                scope[1].constr.Add
                    { expect = then_
                      actual = elseif
                      span = i.span }

            match i.else_ with
            | Some else_ ->
                let else_ = this.InferBlock else_ scope

                scope[1].constr.Add
                    { expect = then_
                      actual = else_
                      span = i.span }
            | None ->
                scope[1].constr.Add
                    { expect = then_
                      actual = UnitType
                      span = i.span }

            then_
        | Block(_) -> failwith "Not Implemented"
        | Call c ->
            let callee = this.TypeOfExpr scope c.callee
            let arg = Array.map (this.TypeOfExpr scope) c.arg
            let ret = TVar(currScope.newTVar None c.span)

            scope[1].constr.Add
                { expect = TFn { param = arg; ret = ret }
                  actual = callee
                  span = c.span }

            ret
        | Unary u ->
            match u.op with
            | Not ->
                scope[1].constr.Add
                    { expect = Primitive Bool
                      actual = this.TypeOfExpr scope u.expr
                      span = u.span }

                Primitive Bool
            | Neg ->
                scope[1].constr.Add
                    { expect = Primitive(Int(true, I32))
                      actual = this.TypeOfExpr scope u.expr
                      span = u.span }

                Primitive(Int(true, I32))
            | Ref -> TRef(this.TypeOfExpr scope u.expr)
            | Deref ->
                let ptr = TVar(currScope.newTVar None u.expr.span)

                scope[1].constr.Add
                    { expect = TRef ptr
                      actual = this.TypeOfExpr scope u.expr
                      span = u.span }

                ptr
        | Assign(_) -> failwith "Not Implemented"
        | Field f ->
            let key = f.prop.sym

            let rec findStruct env =
                let last = Array.last env
                let tySeq = last.ty |> Seq.map (|KeyValue|) |> Seq.rev

                let find (_, ty) =
                    if tyMap.ContainsKey ty then
                        match tyMap[ty] with
                        | TStruct f ->
                            match Map.tryFind key f.field with
                            | Some t -> Some(t, Some(f))
                            | None -> None
                        | _ -> None
                    else
                        None

                match Seq.tryPick find tySeq with
                | Some s -> s
                | None ->
                    if env.Length > 1 then
                        findStruct env[.. env.Length - 2]
                    else
                        error.Add(UndefinedField(f.span, key))
                        TNever, None

            let field, stru = findStruct scope

            match stru with
            | Some s ->
                scope[1].constr.Add
                    { expect = TStruct s
                      actual = this.TypeOfExpr scope f.receiver
                      span = f.span }
            | None -> ()

            field

        | Index(_) -> failwith "Not Implemented"
        | Array(_) -> failwith "Not Implemented"
        | ArrayRepeat(_) -> failwith "Not Implemented"
        | StructLit(_) -> failwith "Not Implemented"
        | AST.Tuple(_) -> failwith "Not Implemented"
        | Closure(_) -> failwith "Not Implemented"
        | Path(_) -> failwith "Not Implemented"
        | Break _ -> TNever
        | Continue _ -> TNever
        | Return(_) -> failwith "Not Implemented"
        | Range(_) -> failwith "Not Implemented"
        | For(_) -> failwith "Not Implemented"
        | While(_) -> failwith "Not Implemented"
        | TryReturn(_) -> failwith "Not Implemented"
        | Match(_) -> failwith "Not Implemented"

    member internal this.InferBlock (b: Block) env =
        let typeof _ stmt =
            match stmt with
            | DeclStmt _ -> failwith "Not Implemented"
            | ExprStmt e -> this.TypeOfExpr env e

        Array.fold typeof UnitType b.stmt

    member internal this.InferFn (scope: Scope[]) (f: Fn) =
        let fnScope = this.newScope

        let fnTy =
            match binding[f.name] with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        for (idx, p) in f.param |> Array.indexed do
            match p.pat with
            | IdPat i ->
                fnScope.var[i.sym] <- i
                binding[i] <- fnTy.param[idx]
            | LitPat(_, _) -> failwith "Not Implemented"
            | TuplePat(_) -> failwith "Not Implemented"
            | ArrayPat(_) -> failwith "Not Implemented"
            | AsPat(_) -> failwith "Not Implemented"
            | PathPat(_) -> failwith "Not Implemented"
            | EnumPat(_) -> failwith "Not Implemented"
            | StructPat(_) -> failwith "Not Implemented"
            | OrPat(_) -> failwith "Not Implemented"
            | RestPat(_) -> failwith "Not Implemented"
            | CatchAllPat(_) -> failwith "Not Implemented"
            | RangePat(_) -> failwith "Not Implemented"
            | SelfPat(_) -> failwith "Not Implemented"
            | RefSelfPat(_) -> failwith "Not Implemented"

        let newScope = Array.append scope [| fnScope |]

        let ret = this.InferBlock f.body newScope

        scope[1].constr.Add
            { expect = fnTy.ret
              actual = ret
              span = f.name.span }

    member this.Infer m =
        let topLevel = this.newScope

        for { decl = decl } in m.item do
            this.HoistDeclName topLevel decl

        let scope = [| Scope.Prelude; topLevel |]

        for { decl = decl } in m.item do
            this.HoistDecl scope decl

        for { decl = decl } in m.item do
            match decl with
            | FnDecl f -> this.InferFn scope f
            | Let(_) -> failwith "Not Implemented"
            | Const(_) -> failwith "Not Implemented"
            | StructDecl(_)
            | EnumDecl(_)
            | TypeDecl(_) -> ()
            | Use(_) -> failwith "Not Implemented"
            | Trait(_) -> failwith "Not Implemented"
            | Impl(_) -> failwith "Not Implemented"

        this.ResolveConstraint topLevel

    member internal this.ResolveConstraint scope =
        let mapping = Dictionary<Var, Type>()

        let rec resolve ty =
            match ty with
            | TVar tvar ->
                if mapping.ContainsKey tvar then
                    resolve mapping[tvar]
                else
                    TVar tvar
            | TFn f ->
                TFn
                    { param = Array.map resolve f.param
                      ret = resolve f.ret }
            | Primitive p -> Primitive p
            | TRef r -> TRef(resolve r)
            | TStruct s -> TStruct s
            | TEnum(_) -> failwith "Not Implemented"
            | Tuple(_) -> failwith "Not Implemented"
            | TNever -> failwith "Not Implemented"

        let rec unify c =
            match c.expect, c.actual with
            | p1, p2 when p1 = p2 -> ()
            | TVar id, ty
            | ty, TVar id ->
                let ty = resolve ty

                if mapping.ContainsKey id then
                    let oldTy = mapping[id]

                    unify
                        { expect = ty
                          actual = oldTy
                          span = c.span }

                    mapping[id] <- resolve oldTy
                else
                    mapping[id] <- ty

            | TFn t1, TFn t2 ->
                if t1.param.Length <> t2.param.Length then
                    error.Add(TypeMismatch(c.expect, c.actual, c.span))
                else
                    for (idx, p1) in (Array.indexed t1.param) do
                        unify
                            { expect = p1
                              actual = t2.param[idx]
                              span = c.span }

                    unify
                        { expect = t1.ret
                          actual = t2.ret
                          span = c.span }
            | TRef t1, TRef t2 ->
                unify
                    { expect = t1
                      actual = t2
                      span = c.span }
            | TNever, _
            | _, TNever -> ()
            | _, _ -> error.Add(TypeMismatch(c.expect, c.actual, c.span))

        for c in scope.constr do
            unify c

        for id in binding.Keys do
            binding[id] <- resolve binding[id]

    member this.GetTypes = binding

    member this.GetError = error
