module AST.AST

open Common.Span

type Lit =
    | String of string
    | Char of char
    | Int of uint
    /// only used in const generic
    | NegInt of uint
    | Float of double
    | Bool of bool

type Id = { Sym: string; Span: Span }

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
    { Prefix: Option<PathPrefix>
      Seg: Id[]
      Span: Span }

type Path =
    { Prefix: Option<PathPrefix>
      Seg: (Id * Type[])[]
      Span: Span }

and FnType =
    { Param: Type[]
      TyParam: TypeParam[]
      Ret: Type
      Span: Span }

and RefType = { Ty: Type; Span: Span }

and ArrayType =
    { Ele: Type
      Len: Option<uint>
      Span: Span }

and TupleType = { Ele: Type[]; Span: Span }

and TypeParam =
    { Id: Id
      Const: bool
      Bound: Path[]
      Span: Span }

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
        | TypeId i -> i.Span
        | PathType p -> p.Span
        | TupleType t -> t.Span
        | LitType(_, s) -> s
        | NeverType s -> s
        | RefType r -> r.Span
        | ArrayType a -> a.Span
        | InferedType s -> s
        | FnType f -> f.Span

type SeqPat = { Ele: Pat[]; Span: Span }

and AsPat = { Pat: Pat; Id: Id; Span: Span }

and EnumPat =
    { Name: PathPat
      Payload: Pat[]
      Span: Span }

and OrPat = { Pat: Pat[]; Span: Span }

and KeyValuePat = { Id: Id; Pat: Pat; Span: Span }

and FieldPat =
    | ShorthandPat of Id
    | KeyValuePat of KeyValuePat
    | RestFieldPat of Span

    member this.Span =
        match this with
        | ShorthandPat i -> i.Span
        | KeyValuePat k -> k.Span
        | RestFieldPat s -> s

and RangePat =
    { From: Option<Pat>
      To: Option<Pat>
      Span: Span }

and StructPat =
    { Id: PathPat
      Field: FieldPat[]
      Span: Span }

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

    member this.Span =
        match this with
        | LitPat(_, s) -> s
        | IdPat i -> i.Span
        | TuplePat t -> t.Span
        | ArrayPat a -> a.Span
        | AsPat a -> a.Span
        | PathPat p -> p.Span
        | EnumPat e -> e.Span
        | StructPat s -> s.Span
        | OrPat o -> o.Span
        | RestPat s -> s
        | CatchAllPat s -> s
        | RangePat r -> r.Span
        | SelfPat s -> s
        | RefSelfPat s -> s

type Param =
    { Pat: Pat
      Ty: Option<Type>
      Span: Span }

type Call =
    { Callee: Expr
      Arg: Expr[]
      Span: Span }

    member this.isMethodCall =
        match this.Callee with
        | Field _ -> true
        | _ -> false

and LetCond = { Pat: Pat; Value: Expr; Span: Span }

and Cond =
    | BoolCond of Expr
    | LetCond of LetCond

and Elseif =
    { Cond: Cond; Block: Block; Span: Span }

and If =
    { Cond: Cond
      Then: Block
      ElseIf: Elseif[]
      Else: Option<Block>
      Span: Span }

and Unary = { Op: UnaryOp; Expr: Expr; Span: Span }

and Assign =
    { Place: Expr
      Op: Option<ArithmeticOp>
      Value: Expr
      Span: Span }

and Binary =
    { Left: Expr
      Op: BinaryOp
      Right: Expr
      Span: Span }

and Field =
    { Receiver: Expr; Prop: Id; Span: Span }

and Index =
    { Container: Expr
      Idx: Expr
      Span: Span }

and Block = { Stmt: Stmt[]; Span: Span }

and ArrayRepeat = { Ele: Expr; Count: Expr; Span: Span }

and Seq = { element: Expr[]; span: Span }

and RangeExpr =
    { From: Option<Expr>
      To: Option<Expr>
      Exclusive: bool
      Span: Span }

and KeyValueField =
    { Name: string
      Value: Expr
      Span: Span }

and StructField =
    | ShorthandField of Id
    | KeyValueField of KeyValueField
    | RestField of Span * Expr

    member this.Span =
        match this with
        | ShorthandField i -> i.Span
        | KeyValueField k -> k.Span
        | RestField(s, _) -> s

and StructLit =
    { Ty: Path
      Field: StructField[]
      Span: Span }

and For =
    { Var: Pat
      Iter: Expr
      Body: Block
      Span: Span }

and While = { Cond: Cond; Body: Block; Span: Span }

and TryReturn = { Base: Expr; Span: Span }

and Closure =
    { Param: Param[]
      Ret: Option<Type>
      Body: Expr
      Span: Span }

and MatchBranch =
    { Pat: Pat
      Guard: Option<Expr>
      Expr: Expr
      Span: Span }

and Match =
    { expr: Expr
      branch: MatchBranch[]
      span: Span }

and Return = { Value: Option<Expr>; Span: Span }

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

    member this.Span =
        match this with
        | Id i -> i.Span
        | LitExpr(_, s) -> s
        | SelfExpr s -> s
        | If i -> i.Span
        | Block b -> b.Span
        | Call c -> c.Span
        | Unary u -> u.Span
        | Assign a -> a.Span
        | Binary b -> b.Span
        | Field f -> f.Span
        | Index i -> i.Span
        | Array t
        | Tuple t -> t.span
        | StructLit s -> s.Span
        | Closure c -> c.Span
        | ArrayRepeat a -> a.Span
        | Path p -> p.Span
        | Break b -> b
        | Continue c -> c
        | Return r -> r.Span
        | Range r -> r.Span
        | For f -> f.Span
        | While w -> w.Span
        | TryReturn t -> t.Span
        | Match m -> m.span

    member this.IsPlace =
        match this with
        | Id _
        | Field _
        | Unary { Op = Deref }
        | Index _ -> true
        | _ -> false

and Let =
    { Pat: Pat
      Mut: bool
      Ty: Option<Type>
      Value: Expr
      Span: Span }

and Const =
    { Pat: Pat
      Ty: Option<Type>
      Value: Expr
      Span: Span }

and Fn =
    { Name: Id
      TyParam: TypeParam[]
      Param: Param[]
      Ret: Option<Type>
      Body: Block
      Span: Span }

and UsePath =
    { Span: Span; Seg: Id[]; Item: UseItem }

and UseItem =
    | UseAll of Span
    | UseSelf of Span
    | UseItem of Id
    | UsePath of UsePath[]

and Use =
    { Span: Span
      Prefix: Option<PathPrefix>
      Seg: Id[]
      Item: UseItem[] }

and TypeDecl = { Name: Id; Ty: Type; Span: Span }

and StructFieldDef =
    { Vis: Visibility
      Name: Id
      Ty: Type
      Span: Span }

and StructDecl =
    { Id: Id
      TyParam: TypeParam[]
      Field: StructFieldDef[]
      Span: Span }

and EnumVariantDef = { Id: Id; Payload: Type[]; span: Span }

and EnumDecl =
    { Id: Id
      TyParam: TypeParam[]
      Variant: EnumVariantDef[]
      Span: Span }

and TraitMethod =
    { Id: Id
      TyParam: TypeParam[]
      Param: Param[]
      Ret: Option<Type>
      DefaultImpl: Option<Block>
      Span: Span }

and TraitType =
    { Id: Id
      Bound: Path[]
      DefaultTy: Option<Type>
      Span: Span }

and TraitValue =
    { Id: Id
      Ty: Type
      DefaultValue: Option<Expr>
      Span: Span }

and TraitItem =
    | TraitMethod of TraitMethod
    | TraitType of TraitType
    | TraitValue of TraitValue

and Trait =
    { Id: Id
      TyParam: TypeParam[]
      Super: Path[]
      Item: TraitItem[]
      Span: Span }

and ImplDecl =
    | AssocType of TypeDecl
    | AssocValue of Const
    | Method of Fn

    member this.Span =
        match this with
        | AssocType t -> t.Span
        | AssocValue c -> c.Span
        | Method m -> m.Span

and ImplItem =
    { Vis: Visibility
      Item: ImplDecl
      Span: Span }

and Impl =
    { Trait: Option<Path>
      TyParam: TypeParam[]
      Type: Type
      Item: ImplItem[]
      Span: Span }

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

    member this.Span =
        match this with
        | Let l -> l.Span
        | Const c -> c.Span
        | FnDecl f -> f.Span
        | StructDecl s -> s.Span
        | EnumDecl e -> e.Span
        | TypeDecl t -> t.Span
        | Use u -> u.Span
        | Trait t -> t.Span
        | Impl i -> i.Span

and Stmt =
    | ExprStmt of Expr
    | DeclStmt of Decl

type ModuleItem =
    { Vis: Visibility
      Decl: Decl
      Span: Span }

type Module = { Item: ModuleItem[]; Span: Span }
