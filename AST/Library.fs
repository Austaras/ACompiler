module AST.AST

type Span =
    { first: int
      last: int }

    static member dummy = { first = 0; last = 0 }
    static member make first last = { first = first; last = last }

type Lit =
    | String of string
    | Char of char
    | Int of uint
    | Float of double
    | Bool of bool

type Id = { sym: string; span: Span }

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
    | Pow
    | Exp
    | BitOr
    | BitAnd
    | BitXor
    | LogicalOr
    | LogicalAnd
    | Shl
    | Shr

    member this.may_short_circut = this = LogicalOr || this = LogicalAnd

type BinaryOp =
    | Arithmetic of ArithmeticOp
    | EqEq
    | NotEq
    | Lt
    | Gt
    | LtEq
    | GtEq
    | Pipe

    member this.may_short_circut =
        this = Arithmetic LogicalOr || this = Arithmetic LogicalAnd

type Call =
    { callee: Expr
      arg: Expr[]
      type_arg: Expr[]
      span: Span }

and If =
    { cond: Expr
      then_: Block
      else_: Option<Block>
      span: Span }

and Block = { stmt: Stmt[]; span: Span }

and Expr =
    | Id of Id
    | LitExpr of Lit
    | IfExpr of If
    | BlockExpr of Block
    | CallExpr of Call

and Let =
    { id: Id
      mut: bool
      type_: Option<Expr>
      value: Expr }

and Fn = { id: Id; param: Id[]; body: Block }

and Type = { id: Id }

and Stmt =
    | ExprStmt of Expr
    | Let of Let
    | Fn of Fn
    | Type of Type
    | Break of Span
    | Continue of Span
    | Return of Span
