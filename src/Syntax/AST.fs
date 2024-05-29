module Syntax.AST

open Common.Span

type Lit =
    | String of string
    | Char of char
    | Int of uint64
    | Float of double
    | Bool of bool

type Id = { Sym: string; Span: Span }

type Literal = { Value: Lit; Span: Span }

type UnaryOp =
    | Neg
    | Not
    | Ref
    | Deref

    member this.ToString =
        match this with
        | Neg -> "-"
        | Not -> "!"
        | Ref -> "&"
        | Deref -> "*"

type ArithOp =
    | Add
    | Sub
    | Mul
    | Div
    | Rem
    | BitOr
    | BitAnd
    | BitXor
    | Shl
    | Shr

    member this.ToString =
        match this with
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | Div -> "/"
        | Rem -> "%"
        | BitOr -> "|"
        | BitAnd -> "&"
        | BitXor -> "^"
        | Shl -> "<<"
        | Shr -> ">>"

type LogicOp =
    | And
    | Or

    member this.ToString =
        match this with
        | And -> "&&"
        | Or -> "||"

type CmpOp =
    | EqEq
    | NotEq
    | Lt
    | Gt
    | LtEq
    | GtEq

    member this.ToString =
        match this with
        | EqEq -> "=="
        | NotEq -> "!="
        | Lt -> "<"
        | Gt -> ">"
        | LtEq -> "<="
        | GtEq -> ">="

type BinaryOp =
    | Arith of ArithOp
    | Logic of LogicOp
    | Cmp of CmpOp
    | Pipe

    member this.ToString =
        match this with
        | Arith a -> a.ToString
        | Logic l -> l.ToString
        | Cmp c -> c.ToString
        | Pipe -> "|>"

type Visibility =
    | Public
    | Private
    | Internal

    member this.ToString =
        match this with
        | Public -> "public"
        | Private -> "private"
        | Internal -> "internal"

type PathPrefix =
    | Self
    | LowSelf
    | Package

    member this.ToString =
        match this with
        | Self -> "Self"
        | LowSelf -> "self"
        | Package -> "package"

type PathPat =
    { Prefix: Option<PathPrefix>
      Seg: Id[]
      Span: Span }

type Path =
    { Prefix: Option<PathPrefix>
      Seg: (Id * Type[])[]
      Span: Span }

and FnType =
    { Param: Type[]; Ret: Type; Span: Span }

and ExtraType = { Ty: Type; Span: Span }

and ArrayType =
    { Ele: Type
      Len: Option<Type>
      Span: Span }

and TupleType = { Ele: Type[]; Span: Span }

and TyParam =
    { Id: Id
      Const: bool
      Bound: Path[]
      Span: Span }

and Type =
    | IdType of Id
    | PathType of Path
    | LitType of Literal
    | NeverType of Span
    | NegType of ExtraType
    | RefType of ExtraType
    | TupleType of TupleType
    | ArrayType of ArrayType
    | InferedType of Span
    | FnType of FnType

    member this.Span =
        match this with
        | IdType i -> i.Span
        | PathType p -> p.Span
        | TupleType t -> t.Span
        | LitType l -> l.Span
        | NeverType s -> s
        | NegType r -> r.Span
        | RefType r -> r.Span
        | ArrayType a -> a.Span
        | InferedType s -> s
        | FnType f -> f.Span

    member this.WithSpan span =
        match this with
        | IdType i -> IdType { i with Span = span }
        | PathType p -> PathType { p with Span = span }
        | TupleType t -> TupleType { t with Span = span }
        | LitType l -> LitType { l with Span = span }
        | NeverType _ -> NeverType span
        | NegType r -> NegType { r with Span = span }
        | RefType r -> RefType { r with Span = span }
        | ArrayType a -> ArrayType { a with Span = span }
        | InferedType _ -> InferedType span
        | FnType f -> FnType { f with Span = span }

type SeqPat = { Ele: Pat[]; Span: Span }

and AsPat = { Pat: Pat; Id: Id; Span: Span }

and EnumPat =
    { Variant: PathPat
      Payload: Pat[]
      Span: Span }

and OrPat = { Pat: Pat[]; Span: Span }

and KeyValuePat = { Id: Id; Pat: Pat; Span: Span }

and FieldPat =
    | ShorthandPat of Id
    | KeyValuePat of KeyValuePat

    member this.Span =
        match this with
        | ShorthandPat i -> i.Span
        | KeyValuePat k -> k.Span

and RangePat =
    { From: Option<Pat>
      To: Option<Pat>
      Span: Span }

and StructPat =
    { Struct: PathPat
      Field: FieldPat[]
      Span: Span }

and Pat =
    | IdPat of Id
    | LitPat of Literal
    | TuplePat of SeqPat
    | ArrayPat of SeqPat
    | AsPat of AsPat
    | PathPat of PathPat
    | EnumPat of EnumPat
    | StructPat of StructPat
    | OrPat of OrPat
    | CatchAllPat of Span
    | RangePat of RangePat
    | SelfPat of Span
    | RefSelfPat of Span

    member this.Span =
        match this with
        | LitPat l -> l.Span
        | IdPat i -> i.Span
        | TuplePat t -> t.Span
        | ArrayPat a -> a.Span
        | AsPat a -> a.Span
        | PathPat p -> p.Span
        | EnumPat e -> e.Span
        | StructPat s -> s.Span
        | OrPat o -> o.Span
        | CatchAllPat s -> s
        | RangePat r -> r.Span
        | SelfPat s -> s
        | RefSelfPat s -> s

    member this.WithSpan span =
        match this with
        | LitPat l -> LitPat { l with Span = span }
        | IdPat i -> IdPat { i with Span = span }
        | TuplePat t -> TuplePat { t with Span = span }
        | ArrayPat a -> ArrayPat { a with Span = span }
        | AsPat a -> AsPat { a with Span = span }
        | PathPat p -> PathPat { p with Span = span }
        | EnumPat e -> EnumPat { e with Span = span }
        | StructPat s -> StructPat { s with Span = span }
        | OrPat o -> OrPat { o with Span = span }
        | RangePat r -> RangePat { r with Span = span }
        | CatchAllPat _ -> CatchAllPat span
        | SelfPat _ -> SelfPat span
        | RefSelfPat _ -> RefSelfPat span

    member this.Name =
        match this with
        | IdPat i -> i.Sym
        | _ -> ""

type Param =
    { Pat: Pat
      Ty: Option<Type>
      Span: Span }

type Call<'a> = { Callee: 'a; Arg: 'a[]; Span: Span }

and LetCond = { Pat: Pat; Value: Expr; Span: Span }

and Cond =
    | BoolCond of Expr
    | LetCond of LetCond

    member this.Span =
        match this with
        | BoolCond b -> b.Span
        | LetCond l -> l.Span

and Elseif =
    { Cond: Cond; Block: Block; Span: Span }

and If =
    { Cond: Cond
      Then: Block
      ElseIf: Elseif[]
      Else: Option<Block>
      Span: Span }

and Unary =
    { Op: UnaryOp; Value: Expr; Span: Span }

and Assign =
    { Place: Expr
      Op: Option<ArithOp>
      Value: Expr
      Span: Span }

and Binary =
    { Left: Expr
      Op: BinaryOp
      Right: Expr
      Span: Span }

and As = { Value: Expr; Ty: Type; Span: Span }

and Field =
    { Receiver: Expr
      Field: Id
      Span: Span }

and TupleAccess =
    { Receiver: Expr
      Index: uint64 * Span
      Span: Span }

and Index =
    { Container: Expr
      Index: Expr
      Span: Span }

and Block = { Stmt: Stmt[]; Span: Span }

and ArrayRepeat = { Ele: Expr; Len: Expr; Span: Span }

and Seq = { Ele: Expr[]; Span: Span }

and RangeExpr =
    { From: Option<Expr>
      To: Option<Expr>
      Exclusive: bool
      Span: Span }

and KeyValueField = { Name: Id; Value: Expr; Span: Span }

and RestField = { Value: Expr; Span: Span }

and StructField =
    | ShorthandField of Id
    | KeyValueField of KeyValueField
    | RestField of RestField

    member this.Span =
        match this with
        | ShorthandField i -> i.Span
        | KeyValueField k -> k.Span
        | RestField s -> s.Span

and StructLit =
    { Struct: Path
      Field: StructField[]
      Span: Span }

and For =
    { Pat: Pat
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
    { Value: Expr
      Branch: MatchBranch[]
      Span: Span }

and Return = { Value: Option<Expr>; Span: Span }

and Expr =
    | Id of Id
    | SelfExpr of Span
    | LitExpr of Literal
    | If of If
    | Block of Block
    | Call of Call<Expr>
    | As of As
    | Unary of Unary
    | Assign of Assign
    | Binary of Binary
    | Field of Field
    | TupleAccess of TupleAccess
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
        | LitExpr l -> l.Span
        | SelfExpr s -> s
        | If i -> i.Span
        | Block b -> b.Span
        | Call c -> c.Span
        | As a -> a.Span
        | Unary u -> u.Span
        | Assign a -> a.Span
        | Binary b -> b.Span
        | Field f -> f.Span
        | TupleAccess t -> t.Span
        | Index i -> i.Span
        | Array t
        | Tuple t -> t.Span
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
        | Match m -> m.Span

    member this.WithSpan span =
        match this with
        | Id i -> Id { i with Span = span }
        | LitExpr l -> LitExpr { l with Span = span }
        | SelfExpr _ -> SelfExpr span
        | If i -> If { i with Span = span }
        | Block b -> Block { b with Span = span }
        | Call c -> Call { c with Span = span }
        | As a -> As { a with Span = span }
        | Unary u -> Unary { u with Span = span }
        | Assign a -> Assign { a with Span = span }
        | Binary b -> Binary { b with Span = span }
        | Field f -> Field { f with Span = span }
        | TupleAccess t -> TupleAccess { t with Span = t.Span }
        | Index i -> Index { i with Span = span }
        | Array t -> Array { t with Span = span }
        | Tuple t -> Tuple { t with Span = span }
        | StructLit s -> StructLit { s with Span = span }
        | Closure c -> Closure { c with Span = span }
        | ArrayRepeat a -> ArrayRepeat { a with Span = span }
        | Path p -> Path { p with Span = span }
        | Break _ -> Break span
        | Continue _ -> Continue span
        | Return r -> Return { r with Span = span }
        | Range r -> Range { r with Span = span }
        | For f -> For { f with Span = span }
        | While w -> While { w with Span = span }
        | TryReturn t -> TryReturn { t with Span = span }
        | Match m -> Match { m with Span = span }

and Let =
    { Pat: Pat
      Mut: bool
      Ty: Option<Type>
      Value: Expr
      Span: Span }

and Const =
    { Name: Id
      Ty: Option<Type>
      Value: Expr
      Span: Span }

and Fn =
    { Name: Id
      TyParam: TyParam[]
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
    | UseMany of Span * UsePath[]

    member this.Span =
        match this with
        | UseAll a -> a
        | UseSelf s -> s
        | UseItem i -> i.Span
        | UseMany(s, _) -> s

and Use =
    { Span: Span
      Prefix: Option<PathPrefix>
      Seg: Id[]
      Item: UseItem }

and TypeDecl = { Name: Id; Ty: Type; Span: Span }

and StructFieldDef =
    { Vis: Visibility
      Name: Id
      Ty: Type
      Span: Span }

and StructDecl =
    { Name: Id
      TyParam: TyParam[]
      Field: StructFieldDef[]
      Span: Span }

and EnumVariantDef =
    { Name: Id
      Payload: Type[]
      Tag: Option<Expr>
      Span: Span }

and EnumDecl =
    { Name: Id
      TyParam: TyParam[]
      Variant: EnumVariantDef[]
      Span: Span }

and TraitMethod =
    { Name: Id
      Param: Param[]
      Ret: Option<Type>
      Default: Option<Block>
      Span: Span }

and TraitType =
    { Name: Id
      Bound: Path[]
      DefaultTy: Option<Type>
      Span: Span }

and TraitValue =
    { Id: Id
      Ty: Type
      DefaultValue: Option<Expr>
      Span: Span }

and TraitMember =
    | TraitMethod of TraitMethod
    | TraitType of TraitType
    | TraitValue of TraitValue

    member this.Span =
        match this with
        | TraitMethod t -> t.Span
        | TraitType t -> t.Span
        | TraitValue t -> t.Span

and TraitItem =
    { Attr: Attr[]
      Member: TraitMember
      Span: Span }

and Trait =
    { Name: Id
      TyParam: TyParam[]
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
      Attr: Attr[]
      Item: ImplDecl
      Span: Span }

and Impl =
    { Trait: Option<Path>
      TyParam: TyParam[]
      Ty: Type
      Item: ImplItem[]
      Span: Span }

and Attr =
    | IdAttr of Id
    | LitAttr of Literal
    | CallAttr of Call<Attr>

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

    member this.Span =
        match this with
        | ExprStmt e -> e.Span
        | DeclStmt d -> d.Span

type ModuleItem =
    { Vis: Visibility
      Attr: Attr[]
      Decl: Decl
      Span: Span }

type Module = { Item: ModuleItem[]; Span: Span }
