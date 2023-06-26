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
    | UndefinedField of Id * string
    | UndefinedMember of Id * string
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

type Env =
    { ty: Dictionary<string, Id>
      var: Dictionary<string, Id>
      mut: HashSet<string> }

    member this.AddTy id = this.ty[id.sym] <- id

    member this.AddVar id = this.var[id.sym] <- id

    static member Empty =
        { ty = Dictionary()
          var = Dictionary()
          mut = HashSet() }

    static member Prelude =
        let env =
            { ty = Dictionary()
              var = Dictionary()
              mut = HashSet() }

        for p in primitive do
            let name = p.str
            env.ty[p.str] <- { sym = name; span = Span.dummy }

        env

type internal Constraint =
    { expect: Type
      actual: Type
      span: Span }

type Context(moduleMap) =
    let tyMap =
        let ty = Dictionary<Id, Type>()

        for t in primitive do
            let id = { sym = t.str; span = Span.dummy }

            ty[id] <- Primitive t

        ty

    let binding = Dictionary<Id, Type>()

    let constra = ResizeArray<Constraint>()

    let error = ResizeArray<Error>()

    member internal this.GetVarFromEnv id env =
        if Array.length env = 0 then
            error.Add(Undefined id)
            Never
        else
            let last = Array.last env

            if last.var.ContainsKey id.sym then
                binding[last.var[id.sym]]
            else
                this.GetVarFromEnv id env[0 .. (Array.length env - 2)]

    member internal this.ProcessTy (env: Env[]) ty =
        let rec resolve id (e: Env[]) =
            let len = e.Length

            if len = 0 then
                Never
            else
                let last = e[len - 1]

                if last.ty.ContainsKey id.sym then
                    let id = last.ty[id.sym]

                    // may recursive
                    if e.Length = env.Length then
                        TVar last.ty[id.sym]
                    else
                        tyMap[id]
                else
                    resolve id e[0 .. (len - 2)]

        match ty with
        | NeverType _ -> Never
        | TypeId i -> resolve i env
        | TupleType t -> Tuple(Array.map (this.ProcessTy env) t.element)
        | RefType r -> TRef(this.ProcessTy env r.ty)
        | LitType(_, _) -> failwith "Not Implemented"
        | ArrayType(_) -> failwith "Not Implemented"
        | InferedType(_) -> failwith "Not Implemented"
        | FnType(_) -> failwith "Not Implemented"
        | PathType(_) -> failwith "Not Implemented"
        | TypeInst(_) -> failwith "Not Implemented"

    member internal this.HoistDeclName d (env: Env) =
        match d with
        | Let _
        | Const _ -> ()
        | FnDecl f -> env.AddVar f.name
        | StructDecl s -> env.AddTy s.name
        | EnumDecl e -> env.AddTy e.name
        | TypeDecl t -> env.AddTy t.name
        | Use(_) -> failwith "Not Implemented"
        | Trait(_) -> failwith "Not Implemented"
        | Impl(_) -> failwith "Not Implemented"

    member internal this.HoistDecl d env =
        match d with
        | Let _
        | Const _ -> ()
        | FnDecl f ->
            let paramTy (p: Param) =
                match p.pat with
                | IdPat i ->
                    match p.ty with
                    | Some ty ->
                        let ty = this.ProcessTy env ty
                        binding[i] <- ty

                        constra.Add
                            { expect = ty
                              actual = TVar i
                              span = p.span }

                    | None -> binding[i] <- TVar i

                    TVar i
                | _ -> failwith "Not Implemented"

            let param = Array.map paramTy f.param

            // fake ident for return type
            let ret = TVar { sym = ""; span = f.name.span }

            match f.retTy with
            | Some ty ->
                constra.Add
                    { expect = this.ProcessTy env ty
                      actual = ret
                      span = f.name.span }
            | None -> ()

            binding[f.name] <- TFn { param = param; ret = ret }

        | StructDecl s ->
            if s.tyParam.Length > 0 then
                failwith "Not Implemented"

            if (Array.last env).ty.ContainsKey s.name.sym then
                error.Add(DuplicateDefinition s.name)

            let addKey m (field: StructFieldDef) =
                let name = field.name.sym

                if Map.containsKey name m then
                    error.Add(DuplicateField field.name)

                Map.add name (this.ProcessTy env field.ty) m

            let field = Array.fold addKey Map.empty s.field

            let strct = { name = s.name; field = field }

            tyMap[s.name] <- Struct strct

        | EnumDecl e ->
            if e.tyParam.Length > 0 then
                failwith "Not Implemented"

            if (Array.last env).ty.ContainsKey e.name.sym then
                error.Add(DuplicateDefinition e.name)

            let addKey m (variant: EnumVariantDef) =
                let name = variant.name.sym

                if Map.containsKey name m then
                    error.Add(DuplicateField variant.name)

                let payload = Array.map (this.ProcessTy env) variant.payload

                Map.add name payload m

            let variant = Array.fold addKey Map.empty e.variant

            let enum = { name = e.name; variant = variant }

            tyMap[e.name] <- Enum enum

        | TypeDecl t ->
            if (Array.last env).ty.ContainsKey t.name.sym then
                error.Add(DuplicateDefinition t.name)

            tyMap[t.name] <- this.ProcessTy env t.ty

        | Use(_) -> failwith "Not Implemented"
        | Trait(_) -> failwith "Not Implemented"
        | Impl(_) -> failwith "Not Implemented"

    member internal this.TypeOfExpr env (e: Expr) =
        match e with
        | Binary b ->
            let l = this.TypeOfExpr env b.left
            let r = this.TypeOfExpr env b.right

            constra.Add
                { expect = Primitive(Int(true, I32))
                  actual = l
                  span = b.left.span }

            constra.Add
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
        | Id v -> this.GetVarFromEnv v env
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
                | BoolCond b -> this.TypeOfExpr env b, b.span

            constra.Add
                { expect = Primitive Bool
                  actual = cond
                  span = span }

            let then_ = this.InferBlock i.then_ env

            match i.else_ with
            | Some else_ ->
                let else_ = this.InferBlock else_ env

                constra.Add
                    { expect = then_
                      actual = else_
                      span = i.span }
            | None ->
                constra.Add
                    { expect = then_
                      actual = UnitType
                      span = i.span }

            then_
        | Block(_) -> failwith "Not Implemented"
        | Call c ->
            let callee = this.TypeOfExpr env c.callee
            let arg = Array.map (this.TypeOfExpr env) c.arg
            let ret = TVar { sym = ""; span = c.callee.span }

            constra.Add
                { expect = TFn { param = arg; ret = ret }
                  actual = callee
                  span = c.span }

            ret
        | Unary u ->
            match u.op with
            | Not ->
                constra.Add
                    { expect = Primitive Bool
                      actual = this.TypeOfExpr env u.expr
                      span = u.span }

                Primitive Bool
            | Neg ->
                constra.Add
                    { expect = Primitive(Int(true, I32))
                      actual = this.TypeOfExpr env u.expr
                      span = u.span }

                Primitive(Int(true, I32))
            | Ref -> TRef(this.TypeOfExpr env u.expr)
            | Deref ->
                let ptr = TVar { sym = ""; span = u.expr.span }

                constra.Add
                    { expect = TRef ptr
                      actual = this.TypeOfExpr env u.expr
                      span = u.span }

                ptr
        | Assign(_) -> failwith "Not Implemented"
        | Field(_) -> failwith "Not Implemented"
        | Index(_) -> failwith "Not Implemented"
        | Array(_) -> failwith "Not Implemented"
        | ArrayRepeat(_) -> failwith "Not Implemented"
        | StructLit(_) -> failwith "Not Implemented"
        | AST.Tuple(_) -> failwith "Not Implemented"
        | Closure(_) -> failwith "Not Implemented"
        | Path(_) -> failwith "Not Implemented"
        | Break(_) -> failwith "Not Implemented"
        | Continue(_) -> failwith "Not Implemented"
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

    member internal this.InferFn (f: Fn) env =
        let fnEnv = Env.Empty

        for p in f.param do
            match p.pat with
            | IdPat i -> fnEnv.var[i.sym] <- i
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

        let env = Array.append env [| fnEnv |]

        let ret = this.InferBlock f.body env

        let param =
            Array.map
                (fun (p: Param) ->
                    match p.pat with
                    | IdPat i -> binding[i])
                f.param

        constra.Add
            { expect = TVar f.name
              actual = TFn { param = param; ret = ret }
              span = f.name.span }

    member this.Infer m =
        let topLevel = Env.Empty

        for { decl = decl } in m.item do
            this.HoistDeclName decl topLevel

        let env = [| Env.Prelude; topLevel |]

        for { decl = decl } in m.item do
            this.HoistDecl decl env

        for { decl = decl } in m.item do
            match decl with
            | FnDecl f -> this.InferFn f env
            | Let(_) -> failwith "Not Implemented"
            | Const(_) -> failwith "Not Implemented"
            | StructDecl(_) -> failwith "Not Implemented"
            | EnumDecl(_) -> failwith "Not Implemented"
            | TypeDecl(_) -> failwith "Not Implemented"
            | Use(_) -> failwith "Not Implemented"
            | Trait(_) -> failwith "Not Implemented"
            | Impl(_) -> failwith "Not Implemented"

        this.ResolveConstraint

    member this.GetTypes = binding

    member this.GetError = error

    member this.ResolveConstraint =
        let mapping = Dictionary<Id, Type>()

        let rec resolve ty =
            match ty with
            | TVar id -> if mapping.ContainsKey id then mapping[id] else TVar id
            | TFn f ->
                TFn
                    { param = Array.map resolve f.param
                      ret = resolve f.ret }
            | Primitive p -> Primitive p
            | TRef r -> TRef(resolve r)
            | Struct(_) -> failwith "Not Implemented"
            | Enum(_) -> failwith "Not Implemented"
            | Tuple(_) -> failwith "Not Implemented"
            | Never -> failwith "Not Implemented"

        let rec unify c =
            match c.expect, c.actual with
            | TVar id, ty
            | ty, TVar id -> mapping[id] <- resolve ty
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
            | p1, p2 ->
                if p1 <> p2 then
                    error.Add(TypeMismatch(c.expect, c.actual, c.span))

        for c in constra do
            unify c

        for id in mapping.Keys do
            if binding.ContainsKey id then
                binding[id] <- resolve mapping[id]

        constra.Clear()
