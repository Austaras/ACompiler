module AST.AST

type Span =
    { first: int
      last: int }

    static member dummy = { first = 0; last = 0 }
    static member Make first last = { first = first; last = last }

type Lit =
    | String of string
    | Char of char
    | Int of uint
    | Float of double
    | Bool of bool

type Id = { sym: string; span: Span }

type UseItem =
    | All of Option<string>
    | Item of Id[]

type UnaryOp =
    | Neg
    | Not
    | Ref
    | Deref

type ArithmeticOp =
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | BitOr
    | BitAnd
    | BitXor
    | LogicalOr
    | LogicalAnd
    | Shl
    | Shr

    member this.mayShortCircut = this = LogicalOr || this = LogicalAnd

type BinaryOp =
    | Arithmetic of ArithmeticOp
    | EqEq
    | NotEq
    | Lt
    | Gt
    | LtEq
    | GtEq
    | Pipe
    | As

    member this.mayShortCircut =
        match this with
        | Arithmetic a -> a.mayShortCircut
        | _ -> false

    member this.precedence =
        match this with
        | As -> 10
        | Arithmetic Mul
        | Arithmetic Div
        | Arithmetic Mod -> 9
        | Arithmetic Add
        | Arithmetic Sub -> 8
        | Arithmetic Shl
        | Arithmetic Shr -> 7
        | Arithmetic BitAnd -> 6
        | Arithmetic BitXor -> 5
        | Arithmetic BitOr -> 4
        | EqEq
        | NotEq
        | Lt
        | Gt
        | LtEq
        | GtEq -> 3
        | Arithmetic LogicalAnd -> 2
        | Arithmetic LogicalOr -> 1
        | Pipe -> 0

type Visibility =
    | Public
    | Private
    | Internal

type PathSegment =
    | PathId of Id
    | Self
    | Package

type Path = { seg: PathSegment[]; span: Span }

type Call =
    { callee: Expr
      arg: Expr[]
      type_arg: Expr[]
      span: Span }

    member this.is_method_call =
        match this.callee with
        | Field { prop = FieldName _ } -> true
        | _ -> false

and If =
    { cond: Expr
      then_: Block
      else_: Option<Block>
      span: Span }

and Unary = { op: UnaryOp; expr: Expr; span: Span }

and Assign =
    { assignee: Expr
      op: Option<ArithmeticOp>
      value: Expr
      span: Span }

and Binary =
    { left: Expr
      op: BinaryOp
      right: Expr
      span: Span }

and Prop =
    | FieldName of Id
    | TupleName of uint
    | Computed of Expr

and Field =
    { receiver: Expr
      prop: Prop
      span: Span }

and Block = { stmt: Stmt[]; span: Span }

and Expr =
    | Id of Id
    | Lit of Lit * Span
    | If of If
    | Block of Block
    | Call of Call
    | Unary of Unary
    | Assign of Assign
    | Binary of Binary
    | Field of Field
    | ArrLit
    | StructLit
    | TupleLit
    | Path of Path
    | Break of Span
    | Continue of Span
    | Return of Span
    | For of For
    | While of While

    member this.span =
        match this with
        | Id i -> i.span
        | Lit(_, s) -> s
        | If i -> i.span
        | Block b -> b.span
        | Call c -> c.span
        | Unary u -> u.span
        | Assign a -> a.span
        | Binary b -> b.span
        | Field f -> f.span
        | Path p -> p.span
        | Break b -> b
        | Continue c -> c
        | Return r -> r

and Let =
    { id: Id
      mut: bool
      type_: Option<Expr>
      value: Expr }

and Fn = { id: Id; param: Id[]; body: Block }

and Type = { id: Id }

and For = { var: Id; iter: Expr; body: Block }

and While = { cond: Expr; body: Block }

and Use =
    { span: Span
      source: PathSegment[]
      item: UseItem }

and Decl =
    | Let of Let
    | Fn of Fn
    | Type of Type
    | Use of Use
    | Impl of Impl

and Stmt =
    | ExprStmt of Expr
    | DeclStmt of Decl

and ImplDecl =
    | AssocValue of Let
    | Method of Fn

and ImplItem =
    { vis: Visibility
      decl: ImplDecl
      span: Span }

and Impl =
    { trait_name: Option<Id>
      type_name: Id
      item: ImplDecl[] }

and ModuleItem =
    { vis: Visibility
      decl: Decl
      span: Span }
