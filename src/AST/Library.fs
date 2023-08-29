module AST.AST

type Span =
    { first: int
      last: int }

    static member dummy = { first = 0; last = 0 }
    static member Make first last = { first = first; last = last }

    member this.WithFirst first = { this with first = first }

    member this.WithLast last = { this with last = last }

    member this.ShrinkFirst i = { this with first = this.first + i }
    member this.ShrinkLast i = { this with last = this.last - i }

type Pos =
    { line: int
      column: int }

    static member FromSpan lines span =
        let rec fromSpan lines line column =
            if Array.length lines = 0 then
                failwith "not in lines"
            else if column < lines[0] then
                { line = line; column = column }
            else
                let newColumn = column - lines[0]

                if newColumn = 0 then
                    { line = line + 1; column = 0 }
                else
                    fromSpan lines[1..] (line + 1) newColumn

        fromSpan lines 0 span

type Lit =
    | String of string
    | Char of char
    | Int of uint
    /// only used in const generic
    | NegInt of uint
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

type PathPrefix =
    | Self
    | LowSelf
    | Package

type PathPat =
    { prefix: Option<PathPrefix>
      seg: Id[]
      span: Span }

type Path =
    { prefix: Option<PathPrefix>
      seg: (Id * Type[])[]
      span: Span }

and FnType =
    { param: Type[]
      typeParam: TypeParam[]
      ret: Type
      span: Span }

and RefType = { ty: Type; span: Span }

and ArrayType =
    { ele: Type
      len: Option<uint>
      span: Span }

and TupleType = { element: Type[]; span: Span }

and TypeParam =
    { id: Id
      const_: bool
      bound: Path[]
      span: Span }

and Type =
    | TypeId of Id
    | PathType of Path
    | TupleType of TupleType
    | LitType of Lit * Span
    | NeverType of Span
    | RefType of RefType
    | ArrayType of ArrayType
    | InferedType of Span
    | FnType of FnType

    member this.span =
        match this with
        | TypeId i -> i.span
        | PathType p -> p.span
        | TupleType t -> t.span
        | LitType(_, s) -> s
        | NeverType s -> s
        | RefType r -> r.span
        | ArrayType a -> a.span
        | InferedType s -> s
        | FnType f -> f.span

type SeqPat = { element: Pat[]; span: Span }

and AsPat = { pat: Pat; id: Id; span: Span }

and EnumPat =
    { name: PathPat
      content: Pat[]
      span: Span }

and OrPat = { pat: Pat[]; span: Span }

and KeyValuePat = { id: Id; pat: Pat; span: Span }

and FieldPat =
    | ShorthandPat of Id
    | KeyValuePat of KeyValuePat
    | RestFieldPat of Span

    member this.span =
        match this with
        | ShorthandPat i -> i.span
        | KeyValuePat k -> k.span
        | RestFieldPat s -> s

and RangePat =
    { from: Option<Pat>
      to_: Option<Pat>
      span: Span }

and StructPat =
    { name: PathPat
      field: FieldPat[]
      span: Span }

and Pat =
    | LitPat of Lit * Span
    | IdPat of Id
    | TuplePat of SeqPat
    | ArrayPat of SeqPat
    | AsPat of AsPat
    | PathPat of PathPat
    | EnumPat of EnumPat
    | StructPat of StructPat
    | OrPat of OrPat
    | RestPat of Span
    | CatchAllPat of Span
    | RangePat of RangePat
    | SelfPat of Span
    | RefSelfPat of Span

    member this.span =
        match this with
        | LitPat(_, s) -> s
        | IdPat i -> i.span
        | TuplePat t -> t.span
        | ArrayPat a -> a.span
        | AsPat a -> a.span
        | PathPat p -> p.span
        | EnumPat e -> e.span
        | StructPat s -> s.span
        | OrPat o -> o.span
        | RestPat s -> s
        | CatchAllPat s -> s
        | RangePat r -> r.span
        | SelfPat s -> s
        | RefSelfPat s -> s

    member this.ExtractId = [||]

type Param =
    { pat: Pat
      ty: Option<Type>
      span: Span }

type Call =
    { callee: Expr
      arg: Expr[]
      span: Span }

    member this.isMethodCall =
        match this.callee with
        | Field _ -> true
        | _ -> false

and LetCond = { pat: Pat; value: Expr; span: Span }

and Cond =
    | BoolCond of Expr
    | LetCond of LetCond

and Elseif =
    { cond: Cond; block: Block; span: Span }

and If =
    { cond: Cond
      then_: Block
      elseif: Elseif[]
      else_: Option<Block>
      span: Span }

and Unary = { op: UnaryOp; expr: Expr; span: Span }

and Assign =
    { place: Expr
      op: Option<ArithmeticOp>
      value: Expr
      span: Span }

and Binary =
    { left: Expr
      op: BinaryOp
      right: Expr
      span: Span }

and Field =
    { receiver: Expr; prop: Id; span: Span }

and Index =
    { container: Expr
      index: Expr
      span: Span }

and Block = { stmt: Stmt[]; span: Span }

and ArrayRepeat =
    { element: Expr
      repeat: Expr
      span: Span }

and Seq = { element: Expr[]; span: Span }

and RangeExpr =
    { from: Option<Expr>
      to_: Option<Expr>
      exclusive: bool
      span: Span }

and KeyValueField =
    { name: string
      value: Expr
      span: Span }

and StructField =
    | ShorthandField of Id
    | KeyValueField of KeyValueField
    | RestField of Span * Expr

    member this.span =
        match this with
        | ShorthandField i -> i.span
        | KeyValueField k -> k.span
        | RestField(s, _) -> s

and StructLit =
    { ty: Path
      field: StructField[]
      span: Span }

and For =
    { var: Pat
      iter: Expr
      body: Block
      span: Span }

and While = { cond: Cond; body: Block; span: Span }

and TryReturn = { base_: Expr; span: Span }

and Closure =
    { typeParam: TypeParam[]
      param: Param[]
      ret: Option<Type>
      body: Expr
      span: Span }

and MatchBranch =
    { pat: Pat
      guard: Option<Expr>
      expr: Expr
      span: Span }

and Match =
    { expr: Expr
      branch: MatchBranch[]
      span: Span }

and Return = { value: Option<Expr>; span: Span }

and Expr =
    | Id of Id
    | SelfExpr of Span
    | LitExpr of Lit * Span
    | If of If
    | Block of Block
    | Call of Call
    | Unary of Unary
    | Assign of Assign
    | Binary of Binary
    | Field of Field
    | Index of Index
    | Array of Seq
    | ArrayRepeat of ArrayRepeat
    | StructLit of StructLit
    | Tuple of Seq
    | Closure of Closure
    | Path of Path
    | Break of Span
    | Continue of Span
    | Return of Return
    | Range of RangeExpr
    | For of For
    | While of While
    /// question mark expression
    | TryReturn of TryReturn
    | Match of Match

    member this.span =
        match this with
        | Id i -> i.span
        | LitExpr(_, s) -> s
        | SelfExpr s -> s
        | If i -> i.span
        | Block b -> b.span
        | Call c -> c.span
        | Unary u -> u.span
        | Assign a -> a.span
        | Binary b -> b.span
        | Field f -> f.span
        | Index i -> i.span
        | Array t
        | Tuple t -> t.span
        | StructLit s -> s.span
        | Closure c -> c.span
        | ArrayRepeat a -> a.span
        | Path p -> p.span
        | Break b -> b
        | Continue c -> c
        | Return r -> r.span
        | Range r -> r.span
        | For f -> f.span
        | While w -> w.span
        | TryReturn t -> t.span
        | Match m -> m.span

    member this.IsPlace =
        match this with
        | Id _
        | Field _
        | Unary { op = Deref }
        | Index _ -> true
        | _ -> false

and Let =
    { pat: Pat
      mut: bool
      ty: Option<Type>
      value: Expr
      span: Span }

and Const =
    { pat: Pat
      ty: Option<Type>
      value: Expr
      span: Span }

and Fn =
    { name: Id
      typeParam: TypeParam[]
      param: Param[]
      retTy: Option<Type>
      body: Block
      span: Span }

and UsePath =
    { span: Span; seg: Id[]; item: UseItem }

and UseItem =
    | UseAll of Span
    | UseSelf of Span
    | UseItem of Id
    | UsePath of UsePath[]

and Use =
    { span: Span
      prefix: Option<PathPrefix>
      seg: Id[]
      item: UseItem[] }

and TypeDecl = { name: Id; ty: Type; span: Span }

and StructFieldDef =
    { vis: Visibility
      name: Id
      ty: Type
      span: Span }

and StructDecl =
    { name: Id
      tyParam: TypeParam[]
      field: StructFieldDef[]
      span: Span }

and EnumVariantDef =
    { name: Id
      payload: Type[]
      span: Span }

and EnumDecl =
    { name: Id
      tyParam: TypeParam[]
      variant: EnumVariantDef[]
      span: Span }

and TraitMethod =
    { name: Id
      typeParam: TypeParam[]
      param: Param[]
      ret: Type
      defaultImpl: Option<Block>
      span: Span }

and TraitType =
    { name: Id
      defaultTy: Option<Type>
      span: Span }

and TraitValue =
    { name: Id
      ty: Type
      defaultValue: Option<Expr>
      span: Span }

and TraitItem =
    | TraitMethod of TraitMethod
    | TraitType of TraitType
    | TraitValue of TraitValue

and Trait =
    { name: Id
      typeParam: TypeParam[]
      item: TraitItem[]
      span: Span }

and ImplDecl =
    | AssocType of TypeDecl
    | AssocValue of Const
    | Method of Fn

    member this.span =
        match this with
        | AssocType t -> t.span
        | AssocValue c -> c.span
        | Method m -> m.span

and ImplItem =
    { vis: Visibility
      item: ImplDecl
      span: Span }

and Impl =
    { trait_: Option<Path>
      typeParam: TypeParam[]
      type_: Type
      item: ImplItem[]
      span: Span }

and Decl =
    | Let of Let
    | Const of Const
    | FnDecl of Fn
    | StructDecl of StructDecl
    | EnumDecl of EnumDecl
    | TypeDecl of TypeDecl
    | Use of Use
    | Trait of Trait
    | Impl of Impl

    member this.span =
        match this with
        | Let l -> l.span
        | Const c -> c.span
        | FnDecl f -> f.span
        | StructDecl s -> s.span
        | EnumDecl e -> e.span
        | TypeDecl t -> t.span
        | Use u -> u.span
        | Trait t -> t.span
        | Impl i -> i.span

and Stmt =
    | ExprStmt of Expr
    | DeclStmt of Decl

type ModuleItem =
    { vis: Visibility
      decl: Decl
      span: Span }

type Module = { item: ModuleItem[]; span: Span }
