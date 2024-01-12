module Parser.Common

open Common.Span
open AST.AST

type Pair =
    | Paren
    | Bracket
    | Curly

type Delimiter =
    | CR
    | LF
    | Semi

type Reserved =
    | IF
    | ELSE
    | MATCH
    | FOR
    | IN
    | WHILE
    | CONTINUE
    | BREAK
    | RETURN
    | FUNCTION
    | LET
    | MUTABLE
    | CONST
    | TYPE
    | TRAIT
    | IMPL
    | USE
    | PUBLIC
    | INTERNAL
    | STRUCT
    | ENUM
    | SELF
    | LOWSELF
    | PACKAGE

type CommentKind =
    | SingleLine
    | MultiLine

type TokenData =
    | Open of Pair
    | Close of Pair
    | Colon
    | ColonColon
    | Tilde
    | Comma
    | Arrow
    | FatArrow
    | Dot
    | DotDot
    | DotDotCaret
    | Delimiter of Delimiter
    | Lit of Lit
    | Not
    | Eq
    | Question
    | Operator of BinaryOp
    | AssignOp of ArithOp
    | Identifier of string
    | Reserved of Reserved
    | Comment of CommentKind * string
    | Underline

type Token = { Data: TokenData; Span: Span }

type Error =
    | UnexpectedToken of Token * string
    | UnexpectedManyToken of Span * string
    | IncompleteAtEnd of string
    | IncompletePair of Token
    | IncompletePath of Span
    | InvalidLValue of Expr
    | OutOfLoop of Token
    | OutOfFn of Span
    | SelfOutOfDecl of Span
    | OutofMethod of Span
    | IncompleteTypeBound of Span
    | UnexpectedConstType of Token
    | EmptyEnum of Span
    | EmptyTypeInst of Span
    | EmptyTypeParam of Span
    | TooManyRestPat of Span[]
    | InvalidRestPat of Span
    | InvalidRangePat of Token
    | InvalidTrait of Span
    | InclusiveNoEnd of Span
    | RestAtStructEnd of Span
    | VisibilityNotAllowed of Token
    | TopLevelExpr of Span
    | NeedDelimiter of Span
    | ConstPat of Span
    | PubTypeAnnotation of Span
    | IncompleteExp of Span
    | IncompleteEscapeSeq of Span
    | IncompleteMultilineComment of Span
    | UnrecognizablePattern of Span * char
    | Unmatched of Span * char
    | MissingIntContent of Span
    | MissingExpContent of Span
    | CharEmpty of Span
    | CharTooMany of Span
    | UnknownNumberPrefix of Span * char

exception internal ParserExp of Error

type internal Context =
    { InLoop: bool
      InFn: bool
      InCond: bool
      InMethod: bool
      InTrait: bool
      InImpl: bool
      InDecl: bool
      InTypeInst: bool }

    static member Normal =
        { InLoop = false
          InFn = false
          InCond = false
          InTrait = false
          InImpl = false
          InMethod = false
          InDecl = false
          InTypeInst = false }

    static member Fn =
        { InLoop = false
          InFn = true
          InCond = false
          InTrait = false
          InImpl = false
          InMethod = false
          InDecl = false
          InTypeInst = false }

    member this.EnterFn =
        { this with
            InFn = true
            InLoop = false }

let canStartPat i =
    match i with
    | Lit _
    | Identifier _
    | Reserved PACKAGE
    | Reserved SELF
    | Open Paren
    | Open Bracket
    | DotDot -> true
    | _ -> false

let rec isRestPat p =
    match p with
    | AsPat a -> isRestPat a.Pat
    | OrPat o -> Array.exists isRestPat o.Pat
    | RangePat r -> r.From = None && r.To = None
    | _ -> false

let internal canStartExpr token =
    match token with
    | Lit _
    | Identifier _
    | Open _
    | Operator(Arith Sub | Arith Mul | Arith BitAnd | Arith BitOr | Logic Or)
    | Not
    | Reserved(PACKAGE | SELF | LOWSELF | IF | MATCH | FOR | WHILE | RETURN | BREAK | CONTINUE)
    | DotDot
    | DotDotCaret -> true
    | _ -> false

let precedence op =
    match op with
    | As -> 10
    | Arith Mul
    | Arith Div
    | Arith Rem -> 9
    | Arith Add
    | Arith Sub -> 8
    | Arith Shl
    | Arith Shr -> 7
    | Arith BitAnd -> 6
    | Arith BitXor -> 5
    | Arith BitOr -> 4
    | Cmp _ -> 3
    | Logic And -> 2
    | Logic Or -> 1
    | Pipe -> 0

let isPlace expr =
    match expr with
    | Id _
    | Field _
    | Unary { Op = Deref }
    | Index _ -> true
    | _ -> false

let toPrefix kw =
    match kw with
    | SELF -> Self
    | LOWSELF -> LowSelf
    | PACKAGE -> Package
    | _ -> failwith "Unreachable"
