module Parser.Parser

open System.Collections.Generic

open Util.Util
open Common.Span
open AST
open AST
open Lexer

open Parser.Common

type internal Parser(lexer: Lexer, error: ResizeArray<Error>) =
    let mutable ctx = Context.Normal

    member _.LtGt parser error =
        let res = ResizeArray()

        let rec repeat () =
            match lexer.Peek() with
            | Some { Data = Operator(Cmp Gt); Span = span } ->
                lexer.Consume()
                res.ToArray(), span
            | _ ->
                let item = parser ()

                res.Add item

                match lexer.Peek() with
                | Some { Data = Comma } ->
                    lexer.Consume()
                    repeat ()
                | Some { Data = Operator(Cmp Gt); Span = span } ->
                    lexer.Consume()
                    res.ToArray(), span
                | Some token -> raise (ParserExp(UnexpectedToken(token, error)))
                | None -> raise (ParserExp(IncompleteAtEnd error))

        repeat ()

    member _.CommaSeq parser limiter =
        let res = ResizeArray()

        let rec repeat () =
            match lexer.Peek() with
            | Some { Data = data; Span = span } when data = limiter ->
                lexer.Consume()
                res.ToArray(), span
            | _ ->
                let item = parser ()

                res.Add item

                let next = lexer.Read "comma sequence"

                match next.Data with
                | Comma -> repeat ()
                | data when data = limiter -> res.ToArray(), next.Span
                | _ -> raise (ParserExp(NeedDelimiter(next.Span)))

        repeat ()

    member _.StructLike parser =
        let res = ResizeArray()

        let rec skipDelimiter () =
            lexer.Consume()

            match lexer.PeekInline() with
            | Some { Data = Delimiter _ } -> skipDelimiter ()
            | _ -> ()

        let rec repeat () =
            match lexer.Peek() with
            | Some { Data = data; Span = span } when data = Close Curly ->
                lexer.Consume()
                res.ToArray(), span
            | _ ->
                let item = parser ()
                res.Add item

                match lexer.PeekInline() with
                | Some { Data = Delimiter _ } ->
                    skipDelimiter ()
                    repeat ()

                | Some { Data = Comma } ->
                    lexer.Consume()
                    repeat ()

                | Some { Data = data; Span = span } when data = Close Curly ->
                    lexer.Consume()
                    res.ToArray(), span

                | Some token -> raise (ParserExp(UnexpectedToken(token, "Struct Like")))
                | None -> raise (ParserExp(IncompleteAtEnd("Struct Like")))

        repeat ()

    member _.ManyItem parser limiter =
        let res = ResizeArray()

        let rec skipDelimiter () =
            match lexer.PeekInline() with
            | Some { Data = Delimiter _ } ->
                lexer.Consume()
                skipDelimiter ()
            | _ -> ()

        let rec repeat () =
            match lexer.Peek() with
            | Some { Data = data; Span = span } when Some data = limiter ->
                lexer.Consume()
                res.ToArray(), span
            | Some _ ->
                let item = parser ()
                res.Add item

                skipDelimiter ()

                repeat ()
            | None ->
                match limiter with
                | Some _ -> raise (ParserExp(IncompleteAtEnd("Many Item")))
                | None -> res.ToArray(), Span.dummy

        repeat ()

    member this.PatPath path =
        let rec repeat (path: PathPat) =
            match lexer.Peek() with
            | Some { Data = ColonColon } ->
                lexer.Consume()

                let id = lexer.ReadId "Path Pattern Segments"

                let path: PathPat =
                    { Prefix = path.Prefix
                      Seg = Array.append path.Seg [| id |]
                      Span = path.Span.WithLast id.Span }

                repeat path
            | _ -> path

        let rec field () =
            match lexer.Read "Struct Pattern Field" with
            | { Data = Identifier sym; Span = span } ->
                let id = { Sym = sym; Span = span }

                match lexer.Peek() with
                | Some { Data = Colon } ->
                    lexer.Consume()
                    let pat = this.Pat()

                    KeyValuePat
                        { Id = id
                          Pat = pat
                          Span = id.Span.WithLast pat.Span }

                | _ -> ShorthandPat id

            | token -> raise (ParserExp(UnexpectedToken(token, "Struct Pattern Field")))

        let path = repeat path

        match lexer.Peek() with
        | Some { Data = Open Paren } ->
            lexer.Consume()

            if path.Seg.Length = 0 then
                error.Add(IncompletePath path.Span)

            let payload, last = this.CommaSeq this.Pat (Close Paren)

            EnumPat
                { Variant = path
                  Payload = payload
                  Span = path.Span.WithLast last }

        | Some { Data = Open Curly } ->
            lexer.Consume()

            if path.Prefix <> Some Self && path.Seg.Length = 0 then
                error.Add(IncompletePath path.Span)

            let field, last = this.StructLike field

            StructPat
                { Struct = path
                  Field = field
                  Span = path.Span.WithLast last }

        | _ ->
            if path.Prefix = None && path.Seg.Length = 1 then
                IdPat path.Seg[0]
            else if path.Prefix = Some LowSelf && path.Seg.Length = 0 then
                SelfPat path.Span
            else
                if path.Seg.Length = 0 then
                    error.Add(IncompletePath path.Span)

                PathPat path

    member this.PatPrefix() =
        let { Data = data; Span = span } as token = lexer.Read "Pattern"

        match data with
        | Identifier sym ->
            let id = { Sym = sym; Span = span }

            let path: PathPat =
                { Prefix = None
                  Seg = [| id |]
                  Span = span }

            this.PatPath path

        | Reserved(SELF | LOWSELF | PACKAGE as kw) ->
            if not ctx.InDecl && kw = SELF then
                error.Add(SelfOutOfDecl span)

            let path: PathPat =
                { Prefix = Some(toPrefix kw)
                  Seg = [||]
                  Span = span }

            this.PatPath path

        | Lit l -> LitPat { Value = l; Span = span }
        | DotDot ->
            let to_, span =
                match lexer.Peek() with
                | Some { Data = data } when canStartPat data ->
                    let pat = this.PatPrefix()

                    Some pat, span.WithLast pat.Span
                | _ -> None, span

            RangePat { From = None; To = to_; Span = span }

        | Underline -> CatchAllPat span
        | Open Paren ->
            let ele, last = this.CommaSeq this.Pat (Close Paren)

            let span = span.WithLast last

            if ele.Length = 1 then
                ele[0].WithSpan span
            else
                TuplePat { Ele = ele; Span = span }

        | Open Bracket ->
            let ele, last = this.CommaSeq this.Pat (Close Paren)

            let span = span.WithLast last

            let rest = Array.filter isRestPat ele

            if rest.Length > 1 then
                error.Add(rest |> Array.map _.Span |> TooManyRestPat)

            ArrayPat { Ele = ele; Span = span }

        | Operator(Arith BitAnd) ->
            let self = lexer.Expect (Reserved LOWSELF) "ref self"

            RefSelfPat(span.WithLast self)

        | _ -> raise (ParserExp(UnexpectedToken(token, "Pattern")))

    member this.PatRange pat =
        match lexer.Peek() with
        | Some { Data = DotDot; Span = span } ->
            lexer.Consume()

            let (to_: Option<Pat>), span =
                match lexer.Peek() with
                | Some { Data = data } when canStartPat data ->
                    let to_ = this.PatPrefix()
                    let to_ = this.PatRange to_

                    Some to_, pat.Span.WithLast to_.Span
                | _ -> None, pat.Span.WithLast span

            RangePat
                { From = Some pat
                  To = to_
                  Span = span }
        | _ -> pat

    member this.PatAs pat =
        match lexer.Peek() with
        | Some { Data = Reserved AS } ->
            lexer.Consume()

            let id = lexer.ReadId "As Pattern Name"

            let pat =
                AsPat
                    { Pat = pat
                      Id = id
                      Span = pat.Span.WithLast id.Span }

            this.PatAs pat
        | _ -> pat

    member this.PatOr pat =
        let res = ResizeArray()
        res.Add pat

        let rec repeat () =
            match lexer.Peek() with
            | Some { Data = Operator(Arith BitOr) } ->
                lexer.Consume()

                let pat = this.PatPrefix()
                let pat = this.PatRange pat
                let pat = this.PatAs pat

                res.Add pat

                repeat ()
            | _ -> ()

        repeat ()

        if res.Count = 1 then
            res[0]
        else
            let last = res[res.Count - 1]

            OrPat
                { Pat = res.ToArray()
                  Span = pat.Span.WithLast last.Span }

    member this.Pat() =
        let pat = this.PatPrefix()
        let pat = this.PatRange pat
        let pat = this.PatAs pat
        this.PatOr pat

    member this.Path (first: Either<Id, PathPrefix * Span>) turbofish =
        let tryInst (span: Span) =
            lexer.Consume()

            let old = ctx
            ctx <- { ctx with InTypeInst = true }

            let g, last = this.LtGt this.Type "Generic Parameter"

            if g.Length = 0 then
                error.Add(EmptyTypeInst(span.WithLast last))

            ctx <- old

            g, last

        let seg = ResizeArray()

        let rec tryInstTurboFish (id: Id) =
            if turbofish then
                match lexer.PeekInline() with
                | Some({ Data = ColonColon }) ->
                    lexer.Consume()

                    match lexer.Peek() with
                    | Some { Data = Operator(Cmp Lt); Span = span } ->
                        let inst, last = tryInst span
                        seg.Add(id, inst)

                        last
                    | Some { Data = Identifier sym; Span = span } ->
                        lexer.Consume()

                        let newId = { Sym = sym; Span = span }

                        seg.Add(id, [||])

                        tryInstTurboFish newId

                    | Some token -> raise (ParserExp(UnexpectedToken(token, "Path Segment")))
                    | None -> raise (ParserExp(IncompleteAtEnd "Path Segment"))
                | _ ->
                    seg.Add(id, [||])

                    id.Span
            else
                match lexer.Peek() with
                | Some { Data = Operator(Cmp Lt); Span = span } ->
                    let inst, last = tryInst span

                    seg.Add(id, inst)
                    last
                | _ ->
                    seg.Add(id, [||])
                    id.Span

        let prefix, span =
            match first with
            | Left id -> None, id.Span.WithLast(tryInstTurboFish id)
            | Right(prefix, span) -> Some prefix, span

        let rec follow (span: Span) =
            match lexer.PeekInline() with
            | Some { Data = ColonColon } ->
                lexer.Consume()

                let id =
                    match lexer.Read "Path Segment" with
                    | { Data = Identifier sym; Span = span } -> { Sym = sym; Span = span }
                    | token -> raise (ParserExp(UnexpectedToken(token, "Path Segment")))

                let span = span.WithLast(tryInstTurboFish id)

                follow span
            | _ -> span

        let span = follow span

        { Prefix = prefix
          Seg = seg.ToArray()
          Span = span }

    member this.Type() =
        let { Data = data; Span = span } as token = lexer.Read "Type"

        match data with
        | Identifier sym ->
            let id = { Sym = sym; Span = span }
            let path = this.Path (Left id) false

            if path.Prefix = None && path.Seg.Length = 1 && (snd path.Seg[0]).Length = 0 then
                IdType id
            else
                PathType path

        | Reserved(SELF | LOWSELF | PACKAGE as kw) ->
            if not ctx.InDecl && kw = SELF then
                error.Add(SelfOutOfDecl span)

            let prefix = toPrefix kw

            let path = this.Path (Right(prefix, span)) false

            if path.Seg.Length = 0 && prefix <> Self then
                error.Add(IncompletePath path.Span)

            PathType path

        | Lit l ->
            if not ctx.InTypeInst then
                error.Add(UnexpectedConstType token)

            LitType { Value = l; Span = span }
        | Not -> NeverType span
        | Underline -> InferedType span
        | Operator(Arith Sub) ->
            if not ctx.InTypeInst then
                error.Add(UnexpectedConstType token)

            let ty = this.Type()

            NegType
                { Ty = ty
                  Span = span.WithLast ty.Span }
        | Operator(Arith BitAnd) ->
            let ty = this.Type()

            RefType
                { Ty = ty
                  Span = span.WithLast ty.Span }

        | Open Paren ->
            let ele, paren = this.CommaSeq this.Type (Close Paren)

            let span = span.WithLast paren

            if ele.Length = 1 then
                ele[0].WithSpan span
            else
                TupleType { Ele = ele; Span = span }

        | Open Bracket ->
            let ele = this.Type()

            match lexer.Peek() with
            | Some { Data = Delimiter Semi } ->
                lexer.Consume()

                let len = this.Type()

                let bracket = lexer.Expect (Close Bracket) "Array type"

                ArrayType
                    { Ele = ele
                      Len = Some len
                      Span = span.WithLast bracket }
            | None -> raise (ParserExp(IncompleteAtEnd "Array Type"))
            | _ ->
                let bracket = lexer.Expect (Close Bracket) "Array type"

                ArrayType
                    { Ele = ele
                      Len = None
                      Span = span.WithLast bracket }

        | Operator(Arith BitOr) ->
            let param, _ = this.CommaSeq this.Type data

            let _ = lexer.Expect Arrow "Function Type"

            let ret = this.Type()

            FnType
                { Param = param
                  Ret = ret
                  Span = span.WithLast ret.Span }

        | _ -> raise (ParserExp(UnexpectedToken(token, "Type")))

    member this.Param closure =
        let pat =
            if closure then
                let pat = this.PatPrefix()
                let pat = this.PatRange pat
                this.PatAs pat
            else
                this.Pat()

        match lexer.Peek() with
        | Some { Data = Colon } ->
            lexer.Consume()

            let ty = this.Type()

            { Pat = pat
              Ty = Some ty
              Span = pat.Span.WithLast ty.Span }

        | _ ->
            { Pat = pat
              Ty = None
              Span = pat.Span }

    member this.ExprPath (first: Either<Id, PathPrefix * Span>) canCurly =
        let path = this.Path first true

        let field () =
            let { Data = data; Span = span } as token = lexer.Read "Struct Field"

            match data with
            | Identifier sym ->
                let id = { Sym = sym; Span = span }

                match lexer.Peek() with
                | Some { Data = Colon } ->
                    lexer.Consume()
                    let value = this.Expr()

                    KeyValueField
                        { Name = id
                          Value = value
                          Span = span.WithLast value.Span }

                | _ -> ShorthandField id

            | DotDot ->
                let value = this.Expr()

                RestField
                    { Value = value
                      Span = span.WithLast value.Span }

            | _ -> raise (ParserExp(UnexpectedToken(token, "Struct Field")))

        match lexer.PeekInline() with
        | Some { Data = Open Curly } when canCurly ->
            lexer.Consume()
            let field, last = this.StructLike field

            StructLit
                { Struct = path
                  Field = field
                  Span = path.Span.WithLast last }

        | _ ->
            if path.Prefix = None && path.Seg.Length = 1 && (snd path.Seg[0]).Length = 0 then
                Id(fst path.Seg[0])
            else if path.Prefix = Some LowSelf && path.Seg.Length = 0 then
                SelfExpr path.Span
            else
                if path.Seg.Length = 0 then
                    error.Add(IncompletePath path.Span)

                Path path

    member this.ExprRange (token: Token) canCurly (from: Option<Expr>) =
        let exclusive =
            match token.Data with
            | DotDot -> false
            | DotDotCaret -> true
            | _ -> failwith "Unreachable"

        let first = from |> Option.map _.Span |> Option.defaultValue token.Span

        let (to_: Expr option), last =
            match lexer.Peek() with
            | Some { Data = data } when canStartExpr data ->
                let to_ = this.ExprPrefix canCurly
                let to_ = this.ExprRepeat -1 canCurly to_

                Some to_, to_.Span
            | _ -> None, token.Span

        Range
            { From = from
              Exclusive = exclusive
              To = to_
              Span = first.WithLast last }

    member this.Cond() =
        match lexer.Peek() with
        | Some { Data = Reserved LET; Span = span } ->
            lexer.Consume()

            let pat = this.Pat()
            let _ = lexer.Expect Eq "Let Condition"
            let value = this.ExprPrefix false
            let value = this.ExprRepeat -100 false value

            LetCond
                { Pat = pat
                  Value = value
                  Span = span.WithLast value.Span }
        | Some { Data = data } when canStartExpr data ->
            let value = this.ExprPrefix false
            let value = this.ExprRepeat -100 false value
            BoolCond value
        | Some token -> raise (ParserExp(UnexpectedToken(token, "Condition")))
        | None -> raise (ParserExp(IncompleteAtEnd "Condition"))

    member this.ExprPrefix canCurly =
        let { Data = data; Span = span } as token = lexer.Read "expression prefix"

        let expr =
            match data with
            | Lit l -> LitExpr { Value = l; Span = span }
            | Identifier i ->
                let id = { Sym = i; Span = span }
                this.ExprPath (Left id) canCurly

            | Reserved(PACKAGE | SELF | LOWSELF as kw) ->
                if not ctx.InDecl && kw = SELF then
                    error.Add(SelfOutOfDecl span)

                let prefix = toPrefix kw
                this.ExprPath (Right(prefix, span)) canCurly

            | Open Paren ->
                let (ele: Expr[]), paren = this.CommaSeq (this.Expr) (Close Paren)
                let span = span.WithLast paren

                if ele.Length = 1 then
                    ele[0].WithSpan span
                else
                    Tuple { Ele = ele; Span = span }

            | Open Bracket ->
                match lexer.Peek() with
                | None -> raise (ParserExp(IncompletePair token))
                | Some { Data = Close Bracket; Span = last } ->
                    lexer.Consume()

                    Array
                        { Ele = [||]
                          Span = span.WithLast last }
                | _ ->
                    let first = this.Expr()

                    let next = lexer.Read "array expression"

                    match next.Data with
                    | Close Bracket ->
                        Array
                            { Ele = [| first |]
                              Span = span.WithLast next.Span }
                    | Comma ->
                        let rest, last = this.CommaSeq this.Expr (Close Bracket)
                        let ele = Array.append [| first |] rest

                        Array { Ele = ele; Span = span.WithLast last }
                    | Delimiter Semi ->
                        let count = this.Expr()
                        let last = lexer.Expect (Close Bracket) "array expression"

                        ArrayRepeat
                            { Ele = first
                              Len = count
                              Span = span.WithLast last }
                    | _ -> raise (ParserExp(UnexpectedToken(next, "array expression")))

            | Open Curly when canCurly -> Block(this.Block span)

            | Operator(Arith(Sub | Mul | BitAnd))
            | Not ->
                let value = this.ExprPrefix canCurly

                let op =
                    match data with
                    | Operator(Arith Sub) -> Neg
                    | Operator(Arith Mul) -> Deref
                    | Operator(Arith BitAnd) -> Ref
                    | Not -> AST.Not
                    | _ -> failwith "Unreachable"

                Unary
                    { Op = op
                      Value = value
                      Span = span.WithLast value.Span }

            | DotDot
            | DotDotCaret -> this.ExprRange token canCurly None

            | Operator(Arith BitOr) ->
                let old = ctx
                ctx <- ctx.EnterFn

                let param, _ = this.CommaSeq (fun () -> this.Param true) (Operator(Arith BitOr))

                let ret = this.RetTy()

                let body = this.Expr()

                ctx <- old

                Closure
                    { Param = param
                      Ret = ret
                      Body = body
                      Span = span.WithLast body.Span }

            | Reserved BREAK ->
                if not ctx.InLoop then
                    error.Add(OutOfLoop token)

                Break span

            | Reserved CONTINUE ->
                if not ctx.InLoop then
                    error.Add(OutOfLoop token)

                Continue span

            | Reserved RETURN ->
                if not ctx.InFn then
                    error.Add(OutOfFn span)

                match lexer.Peek() with
                | Some { Data = data } when canStartExpr data ->
                    let value = this.Expr()
                    Return { Value = Some value; Span = span }

                | _ -> Return { Value = None; Span = span }

            | Reserved IF ->
                let cond = this.Cond()

                let curly = lexer.Expect (Open Curly) "If Expression Body"

                let then_ = this.Block curly

                let elseIf = ResizeArray()

                let rec repeat (else_) =
                    match lexer.Peek() with
                    | Some { Data = Reserved ELSE; Span = span } ->
                        lexer.Consume()

                        match lexer.Peek() with
                        | Some { Data = Reserved IF } ->
                            lexer.Consume()
                            let cond = this.Cond()

                            let curly = lexer.Expect (Open Curly) "If Expression Body"

                            let block = this.Block curly

                            elseIf.Add
                                { Cond = cond
                                  Block = block
                                  Span = span.WithLast block.Span }

                            repeat else_
                        | Some { Data = Open Curly; Span = span } ->
                            lexer.Consume()

                            this.Block span |> Some
                        | Some token -> raise (ParserExp(UnexpectedToken(token, "If Else")))
                        | None -> else_

                    | _ -> else_

                let else_ = repeat None

                let last =
                    match else_ with
                    | Some else_ -> else_.Span
                    | None ->
                        if elseIf.Count > 0 then
                            elseIf[elseIf.Count - 1].Span
                        else
                            then_.Span

                If
                    { Cond = cond
                      ElseIf = elseIf.ToArray()
                      Else = else_
                      Then = then_
                      Span = span.WithLast last }

            | Reserved MATCH ->
                let value = this.ExprPrefix false
                let value = this.ExprRepeat -100 false value

                let _ = lexer.Expect (Open Curly) "Match Body"

                let branch () =
                    let pat = this.Pat()

                    let guard =
                        match lexer.Peek() with
                        | Some { Data = Reserved IF } ->
                            lexer.Consume()

                            this.Expr() |> Some
                        | _ -> None

                    let _ = lexer.Expect FatArrow "Match Branch"

                    let expr = this.Expr()

                    { Pat = pat
                      Guard = guard
                      Expr = expr
                      Span = pat.Span.WithLast expr.Span }

                let branch, last = this.StructLike branch

                Match
                    { Value = value
                      Branch = branch
                      Span = span.WithLast last }

            | Reserved WHILE ->
                let cond = this.Cond()

                let curly = lexer.Expect (Open Curly) "While Expression Body"

                let old = ctx
                ctx <- { ctx with InLoop = true }
                let body = this.Block curly
                ctx <- old

                While
                    { Cond = cond
                      Body = body
                      Span = span.WithLast body.Span }

            | Reserved FOR ->
                let pat = this.Pat()

                let _ = lexer.Expect (Reserved IN) "For In"

                let iter = this.ExprPrefix false
                let iter = this.ExprRepeat -100 false iter

                let old = ctx
                ctx <- { ctx with InLoop = true }

                let curly = lexer.Expect (Open Curly) "For Expression Body"
                let body = this.Block curly
                ctx <- old

                For
                    { Pat = pat
                      Iter = iter
                      Body = body
                      Span = span.WithLast body.Span }

            | _ -> raise (ParserExp(UnexpectedToken(token, "expression prefix")))

        this.ExprPostfix expr

    member this.ExprPostfix expr =
        match lexer.PeekPost() with
        | Some { Data = Dot } ->
            lexer.Consume()

            match lexer.Read "field access expression" with
            | { Data = Identifier sym; Span = span } ->
                let field =
                    Field
                        { Receiver = expr
                          Field = { Sym = sym; Span = span }
                          Span = expr.Span.WithLast span }

                this.ExprPostfix field

            | { Data = Lit(Int i); Span = span } ->
                let access =
                    TupleAccess
                        { Receiver = expr
                          Index = (i, span)
                          Span = expr.Span.WithLast span }

                this.ExprPostfix access

            | token -> raise (ParserExp(UnexpectedToken(token, "field access expression")))

        | Some { Data = Open Paren } ->
            lexer.Consume()

            let arg, paren = this.CommaSeq this.Expr (Close Paren)

            let call =
                Call
                    { Callee = expr
                      Arg = arg
                      Span = expr.Span.WithLast paren }

            this.ExprPostfix call

        | Some { Data = Open Bracket } ->
            lexer.Consume()

            let index = this.Expr()

            let bracket = lexer.Expect (Close Bracket) "index expression"

            let index =
                Index
                    { Container = expr
                      Index = index
                      Span = expr.Span.WithLast bracket }

            this.ExprPostfix index

        | Some { Data = Question; Span = span } ->
            lexer.Consume()

            let tryReturn =
                TryReturn
                    { Base = expr
                      Span = expr.Span.WithLast span }

            this.ExprPostfix tryReturn

        | Some { Data = Reserved AS; Span = span } ->
            lexer.Consume()

            let ty = this.Type()

            let as_ =
                As
                    { Value = expr
                      Ty = ty
                      Span = expr.Span.WithLast ty.Span }

            this.ExprPostfix as_

        | _ -> expr

    member this.ExprPrec (prec: int) (canCurly: bool) (expr: Expr) =
        match lexer.PeekOp() with
        | Some { Data = Operator op } when prec < precedence op ->
            lexer.Consume()

            let right = this.ExprPrefix canCurly
            let right = this.ExprPrec (precedence op) canCurly right

            Binary
                { Left = expr
                  Op = op
                  Right = right
                  Span = expr.Span.WithLast right.Span }

        | Some({ Data = DotDot | DotDotCaret } as token) when prec <= -1 ->
            lexer.Consume()

            this.ExprRange token canCurly (Some expr)

        | Some { Data = Eq | AssignOp _ as data } when prec <= -2 ->
            lexer.Consume()

            let op =
                match data with
                | Eq -> None
                | AssignOp a -> Some a
                | _ -> failwith "Unreachable"

            let value = this.ExprPrefix canCurly
            let value = this.ExprRepeat -2 canCurly value

            if not (isPlace expr) then
                error.Add(InvalidLValue expr)

            Assign
                { Place = expr
                  Op = op
                  Value = value
                  Span = expr.Span.WithLast value.Span }

        | _ -> expr

    member this.ExprRepeat (prec: int) canCurly (expr: Expr) =
        match lexer.PeekOp() with
        | Some { Data = Operator op } when prec < precedence op ->
            let res = this.ExprPrec prec canCurly expr
            this.ExprRepeat prec canCurly res

        | Some { Data = DotDot | DotDotCaret } when prec <= -1 ->
            let res = this.ExprPrec prec canCurly expr
            this.ExprRepeat prec canCurly res

        | Some { Data = Eq | AssignOp _ } when prec <= -2 ->
            let res = this.ExprPrec prec canCurly expr
            this.ExprRepeat prec canCurly res

        | _ -> expr

    member this.Expr() =
        let expr = this.ExprPrefix true
        this.ExprRepeat -100 true expr

    member this.Block(start: Span) =
        let stm, last = this.ManyItem this.Stmt (Some(Close Curly))

        { Stmt = stm
          Span = start.WithLast last }

    member this.TypeBound() =
        let res = ResizeArray()

        let rec bound () =
            match lexer.Peek() with
            | Some { Data = Identifier sym; Span = span } ->
                lexer.Consume()

                let id = { Sym = sym; Span = span }
                let path = this.Path (Left id) false
                res.Add path

                match lexer.Peek() with
                | Some { Data = Operator(Arith Add)
                         Span = add } ->
                    lexer.Consume()

                    match lexer.Peek() with
                    | Some { Data = Identifier _ | Reserved(SELF | LOWSELF | PACKAGE) } -> bound ()
                    | _ -> error.Add(IncompletePath add)
                | _ -> ()
            | Some { Data = Reserved(SELF | LOWSELF | PACKAGE as kw)
                     Span = span } ->
                lexer.Consume()

                let prefix = toPrefix kw
                let path = this.Path (Right(prefix, span)) false
                res.Add path

                match lexer.Peek() with
                | Some { Data = Operator(Arith Add)
                         Span = add } ->
                    lexer.Consume()

                    match lexer.Peek() with
                    | Some { Data = Identifier _ | Reserved(SELF | LOWSELF | PACKAGE) } -> bound ()
                    | _ -> error.Add(IncompletePath add)
                | _ -> ()
            | _ -> ()

        match lexer.Peek() with
        | Some { Data = Colon; Span = span } ->
            lexer.Consume()
            bound ()

            if res.Count = 0 then
                error.Add(IncompleteTypeBound span)

            res.ToArray()
        | _ -> [||]

    member this.TypeParam() =

        let const_ =
            match lexer.Peek() with
            | Some { Data = Reserved CONST } -> true
            | _ -> false

        let id = lexer.ReadId "Type Parameter Name"

        let bound = this.TypeBound()

        let span =
            if bound.Length > 0 then
                id.Span.WithLast (Array.last bound).Span
            else
                id.Span

        { Id = id
          Const = const_
          Bound = bound
          Span = span }

    member this.TypeParamList msg =
        match lexer.Peek() with
        | Some { Data = Operator(Cmp Lt); Span = span } ->
            lexer.Consume()
            let g, last = this.LtGt this.TypeParam msg

            if g.Length = 0 then
                error.Add(EmptyTypeParam(span.WithLast last))

            g, Some last
        | _ -> [||], None

    member this.RetTy() =
        match lexer.Peek() with
        | Some { Data = Arrow } ->
            lexer.Consume()
            this.Type() |> Some
        | _ -> None

    member _.Vis() =
        match lexer.Peek() with
        | Some { Data = Reserved PUBLIC; Span = span } ->
            lexer.Consume()
            Public, Some span
        | Some { Data = Reserved INTERNAL
                 Span = span } ->
            lexer.Consume()
            Internal, Some span
        | _ -> Private, None

    member this.Use (first: Span) (prefix: Either<Id, PathPrefix * Span>) =
        let rec item (seg: Stack<Id>) =
            match lexer.Peek() with
            | Some { Data = ColonColon } ->
                lexer.Consume()
                subItem seg
            | _ ->
                if seg.Count = 0 then
                    seg.ToArray(), UseSelf Span.dummy
                else
                    let last = seg.Pop()

                    seg.ToArray(), UseItem last

        and subItem (seg: Stack<Id>) =
            let { Data = data; Span = span } as token = lexer.Read "Use Segment"

            match data with
            | Identifier sym ->
                let id = { Sym = sym; Span = span }
                seg.Push id
                item seg
            | Operator(Arith Mul) -> seg.ToArray(), UseAll span
            | Reserved LOWSELF -> seg.ToArray(), UseSelf span
            | Open Curly ->
                let parser () =
                    let seg, item = subItem (Stack())

                    let first = Array.tryHead seg |> Option.map _.Span |> Option.defaultValue item.Span

                    { Seg = seg
                      Item = item
                      Span = first.WithLast item.Span }

                let item, last = this.CommaSeq parser (Close Curly)

                let span = span.WithLast last

                seg.ToArray(), UseMany(span, item)
            | _ -> raise (ParserExp(UnexpectedToken(token, "Use Segment")))

        match prefix with
        | Left id ->
            let stack = Stack()
            stack.Push id
            let seg, item = item stack

            Use
                { Prefix = None
                  Seg = seg
                  Item = item
                  Span = first.WithLast item.Span }
        | Right(prefix, span) ->
            let seg, item = item (Stack())

            if seg.Length = 0 then
                error.Add(IncompletePath span)

            Use
                { Prefix = Some prefix
                  Seg = seg
                  Item = item
                  Span = first.WithLast item.Span }

    member this.Decl() =
        let { Data = data; Span = span } as token = lexer.Read "Declaration"

        match data with
        | Reserved LET ->
            let mut =
                match lexer.Peek() with
                | Some { Data = Reserved MUTABLE } ->
                    lexer.Consume()
                    true
                | _ -> false

            let pat = this.Pat()

            let ty =
                match lexer.Peek() with
                | Some { Data = Colon } ->
                    lexer.Consume()

                    this.Type() |> Some

                | _ -> None

            let _ = lexer.Expect Eq "Let Declaration"

            let value = this.Expr()

            Let
                { Mut = mut
                  Pat = pat
                  Ty = ty
                  Value = value
                  Span = span.WithLast value.Span }

        | Reserved FUNCTION ->
            let old = ctx
            ctx <- ctx.EnterFn

            let id = lexer.ReadId "Function Name"

            let tyParam, _ = this.TypeParamList "Function Type Parameter"

            let _ = lexer.Expect (Open Paren) "Function Parameter"

            let param, _ = this.CommaSeq (fun () -> this.Param false) (Close Paren)

            let ret = this.RetTy()

            let blockStart = lexer.Expect (Open Curly) "Function Body"

            let body = this.Block blockStart

            ctx <- old

            FnDecl
                { Name = id
                  TyParam = tyParam
                  Param = param
                  Ret = ret
                  Body = body
                  Span = span.WithLast body.Span }

        | Reserved STRUCT ->
            let name = lexer.ReadId "Struct Name"

            let tyParam, last = this.TypeParamList "Struct Type Parameter"
            let last = Option.defaultValue name.Span last

            let field () =
                let vis, span = this.Vis()

                let name = lexer.ReadId "Struct Field"
                let _ = lexer.Expect Colon "Struct Field"
                let ty = this.Type()

                let span = Option.defaultValue name.Span span

                { Vis = vis
                  Name = name
                  Ty = ty
                  Span = span.WithLast ty.Span }

            let old = ctx
            ctx <- { ctx with InDecl = true }

            let field, last =
                match lexer.PeekInline() with
                | Some { Data = Open Curly } ->
                    lexer.Consume()

                    this.StructLike field
                | _ -> [||], last

            ctx <- old

            StructDecl
                { Name = name
                  TyParam = tyParam
                  Field = field
                  Span = span.WithLast last }

        | Reserved ENUM ->
            let name = lexer.ReadId "Enum Name"

            let tyParam, _ = this.TypeParamList "Enum Type Parameter"

            let variant () =
                let name = lexer.ReadId "Variant Name"

                let payload, last =
                    match lexer.PeekInline() with
                    | Some { Data = Open Paren } ->
                        lexer.Consume()

                        this.CommaSeq this.Type (Close Paren)
                    | _ -> [||], name.Span

                let value, last =
                    match lexer.PeekInline() with
                    | Some { Data = Eq } ->
                        lexer.Consume()

                        let value = this.Expr()

                        Some value, value.Span

                    | _ -> None, last

                { Name = name
                  Payload = payload
                  Tag = value
                  Span = name.Span.WithLast last }

            let old = ctx
            ctx <- { ctx with InDecl = true }

            let variant, last =
                let first = lexer.Expect (Open Curly) "Enum Variant"

                let v, last = this.StructLike variant

                if v.Length = 0 then
                    error.Add(EmptyEnum(first.WithLast last))

                v, last

            ctx <- old

            EnumDecl
                { Name = name
                  TyParam = tyParam
                  Variant = variant
                  Span = span.WithLast last }

        | Reserved TRAIT ->
            let name = lexer.ReadId "Trait Name"

            let tyParam, last = this.TypeParamList "Trait Type Parameter"
            let last = Option.defaultValue name.Span last

            let super = this.TypeBound()

            let item () =
                match lexer.Peek() with
                | Some { Data = Reserved TYPE; Span = span } ->
                    lexer.Consume()
                    let name = lexer.ReadId "Trait Type Name"

                    let bound = this.TypeBound()

                    let defaultTy =
                        match lexer.PeekInline() with
                        | Some { Data = Eq } ->
                            lexer.Consume()
                            this.Type() |> Some
                        | _ -> None

                    let last =
                        match defaultTy with
                        | Some d -> d.Span
                        | None ->
                            if bound.Length > 0 then
                                (Array.last bound).Span
                            else
                                name.Span

                    TraitType
                        { Name = name
                          Bound = bound
                          DefaultTy = defaultTy
                          Span = span.WithLast last }

                | Some { Data = Reserved FUNCTION
                         Span = span } ->
                    lexer.Consume()
                    let name = lexer.ReadId "Trait Method Name"

                    let _ = lexer.Expect (Open Paren) "Trait Method Parameter"

                    let param, last = this.CommaSeq (fun () -> this.Param false) (Close Paren)

                    let ret = this.RetTy()

                    let impl =
                        match lexer.PeekInline() with
                        | Some { Data = Open Curly; Span = span } ->
                            lexer.Consume()

                            this.Block span |> Some
                        | _ -> None

                    let last =
                        impl
                        |> Option.map _.Span
                        |> Option.orElse (ret |> Option.map _.Span)
                        |> Option.defaultValue last

                    TraitMethod
                        { Name = name
                          Param = param
                          Ret = ret
                          Default = impl
                          Span = span.WithLast last }

                | Some token -> raise (ParserExp(UnexpectedToken(token, "Trait Item")))
                | None -> raise (ParserExp(IncompleteAtEnd "Trait Item"))

            let old = ctx
            ctx <- { ctx with InDecl = true }

            let item, last =
                match lexer.PeekInline() with
                | Some { Data = Open Curly } ->
                    lexer.Consume()

                    this.ManyItem item (Some(Close Curly))
                | _ -> [||], last

            ctx <- old

            Trait
                { Name = name
                  TyParam = tyParam
                  Super = super
                  Item = item
                  Span = span.WithLast last }

        | Reserved IMPL ->
            let tyParam, last = this.TypeParamList "Trait Type Parameter"
            let last = Option.defaultValue span last

            let first = this.Type()

            let ty, t =
                match lexer.Peek() with
                | Some { Data = Reserved FOR } ->
                    lexer.Consume()

                    let second = this.Type()

                    let t =
                        match first with
                        | IdType i ->
                            Some
                                { Prefix = None
                                  Seg = [| i, [||] |]
                                  Span = i.Span }
                        | PathType t -> Some t
                        | _ ->
                            error.Add(InvalidTrait first.Span)
                            None

                    second, t
                | _ -> first, None

            let item () =
                let vis, first = this.Vis()

                let item =
                    match lexer.Peek() with
                    | Some { Data = Reserved TYPE; Span = span } ->
                        lexer.Consume()
                        let name = lexer.ReadId "Impl Type Name"

                        let _ = lexer.Expect Eq "Impl Type"

                        let ty = this.Type()

                        AssocType
                            { Name = name
                              Ty = ty
                              Span = span.WithLast ty.Span }

                    | Some { Data = Reserved FUNCTION
                             Span = span } ->
                        lexer.Consume()
                        let name = lexer.ReadId "Method Name"

                        let tyParam, _ = this.TypeParamList "Method Type Parameter"

                        let _ = lexer.Expect (Open Paren) "Method Parameter"

                        let param, last = this.CommaSeq (fun () -> this.Param false) (Close Paren)

                        let ret = this.RetTy()

                        let curly = lexer.Expect (Open Curly) "Method Body"

                        let body = this.Block curly

                        Method
                            { Name = name
                              TyParam = tyParam
                              Param = param
                              Ret = ret
                              Body = body
                              Span = span.WithLast body.Span }

                    | Some token -> raise (ParserExp(UnexpectedToken(token, "Trait Item")))
                    | None -> raise (ParserExp(IncompleteAtEnd "Trait Item"))

                let first = Option.defaultValue item.Span first

                { Vis = vis
                  Item = item
                  Span = first.WithLast item.Span }

            let old = ctx
            ctx <- { ctx with InDecl = true }

            let item, last =
                match lexer.PeekInline() with
                | Some { Data = Open Curly } ->
                    lexer.Consume()

                    this.ManyItem item (Some(Close Curly))
                | _ -> [||], last

            ctx <- old

            Impl
                { TyParam = tyParam
                  Ty = ty
                  Trait = t
                  Item = item
                  Span = span.WithLast last }

        | Reserved USE ->
            let { Data = data; Span = first } = lexer.Read "Use Path"

            match data with
            | Reserved(PACKAGE | SELF | LOWSELF as kw) ->
                if not ctx.InDecl && kw = SELF then
                    error.Add(SelfOutOfDecl span)

                lexer.Consume()
                let prefix = toPrefix kw

                this.Use span (Right(prefix, first))

            | Identifier sym ->
                lexer.Consume()
                let id = { Sym = sym; Span = span }

                this.Use span (Left id)
            | _ -> raise (ParserExp(UnexpectedToken(token, "Use Item")))

        | _ -> raise (ParserExp(UnexpectedToken(token, "Declaration")))

    member this.Stmt() =
        match lexer.Peek() with
        | Some { Data = Reserved(LET | CONST | FUNCTION | IMPL | TRAIT | TYPE | STRUCT | ENUM | USE) } ->
            this.Decl() |> DeclStmt
        | Some { Data = data } when canStartExpr data -> this.Expr() |> ExprStmt
        | Some token -> raise (ParserExp(UnexpectedToken(token, "Statment")))
        | None -> raise (ParserExp(IncompleteAtEnd "Statment"))

    member this.ModuleItem() =
        let vis, span = this.Vis()

        let item = this.Stmt()

        let span = span |> Option.defaultValue item.Span
        let span = span.WithLast item.Span

        let item =
            match item with
            | DeclStmt d -> d
            | ExprStmt e ->
                error.Add(TopLevelExpr e.Span)

                Let
                    { Pat = CatchAllPat Span.dummy
                      Mut = false
                      Ty = None
                      Value = e
                      Span = Span.dummy }

        { Vis = vis; Decl = item; Span = span }

    member this.ParseModule() =
        let item, _ = this.ManyItem this.ModuleItem None

        { Item = item
          Span = Span.Make 0 (lexer.Len - 1) }

/// A hand written recursive descent parser produces AST without paren
///
/// There should be a CST somewhere, but at the time it's omitted
let parse (input: string) =
    let error = ResizeArray()

    try
        let lexer = Lexer(input, error)
        let parser = Parser(lexer, error)

        let m = parser.ParseModule()

        if error.Count > 0 then
            Error(error.ToArray(), Some m)
        else
            Ok m
    with ParserExp e ->
        error.Add e

        Error(error.ToArray(), None)
