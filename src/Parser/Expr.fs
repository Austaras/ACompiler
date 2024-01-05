module Parser.Expr

open Common.Span
open AST.AST
open Lexer

open Parser.Common
open Parser.Pat
open Parser.Type

let mutable internal parseBlock =
    fun (ctx: Context) (input: Token[]) -> failwith "Uninit"

let internal canStartExpr token =
    match token with
    | Lit _
    | Identifier _
    | Paren Open
    | Bracket Open
    | Curly Open
    | Operator(Arith Sub | Arith Mul | Arith BitAnd | Arith BitOr | Logic Or | Cmp Gt)
    | Not
    | Reserved(PACKAGE | SELF | LOWSELF | IF | MATCH | FOR | WHILE | RETURN | BREAK | CONTINUE)
    | DotDot
    | DotDotCaret -> true
    | _ -> false

let internal maybeStruct ctx input =
    if ctx.inCond then
        None
    else
        match peekInline input with
        | Some({ Data = Curly Open }, i) -> Some i
        | _ -> None

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

let internal rangeCtor (from: Option<Expr>) (to_: Option<Expr>) exclusive span =
    let first =
        match from with
        | Some e -> e.Span.First
        | None -> span.First

    let last =
        match to_ with
        | Some e -> e.Span.Last
        | None -> span.Last

    Range
        { From = from
          To = to_
          Exclusive = exclusive
          Span = Span.Make first last }

let internal parseParam (ctx: Context) input =
    match parsePat ctx.InDecl input with
    | Error e -> Error e
    | Ok p ->
        match peek p.rest with
        | Some({ Data = Colon }, i) ->
            match peek p.rest[i..] with
            | None -> p.FatalError(IncompleteAtEnd("type annotation"))
            | _ ->
                match parseType ctx p.rest[i..] with
                | Error e -> p.MergeFatalError e
                | Ok ty ->
                    let param =
                        { Pat = p.data
                          Ty = Some ty.data
                          Span = ty.data.Span.WithFirst p.data.Span.First }

                    Ok
                        { data = param
                          error = Array.append p.error ty.error
                          rest = ty.rest }
        | _ ->
            Ok
                { data =
                    { Pat = p.data
                      Ty = None
                      Span = p.data.Span }
                  error = p.error
                  rest = p.rest }

let rec internal parseStructField ctx input =
    match peek input with
    | Some({ Data = Identifier sym; Span = span }, i) ->
        let id = { Sym = sym; Span = span }

        match peekWith input[i..] Colon with
        | Some(_, j) ->
            match parseExpr ctx input[i + j ..] with
            | Error e -> Error e
            | Ok(v: State<Expr>) ->
                Ok
                    { data =
                        KeyValueField
                            { Name = id
                              Value = v.data
                              Span = v.data.Span.WithFirst span.First }
                      error = v.error
                      rest = v.rest }
        | None ->
            Ok
                { data = ShorthandField id
                  error = [||]
                  rest = input[i..] }

    | Some({ Data = DotDot; Span = span }, i) ->
        match parseExpr ctx input[i..] with
        | Error e -> Error e
        | Ok(v: State<Expr>) ->
            let span = span.WithLast v.data.Span.Last

            Ok
                { data = RestField(span, v.data)
                  error = v.error
                  rest = v.rest }

    | Some(token, _) -> Error [| UnexpectedToken(token, "struct pattern field") |]
    | None -> Error [| IncompleteAtEnd "struct pattern field" |]

and internal parseStruct ctx (state: State<Path>) =
    let field =
        parseCommaSeq state.rest (parseStructField ctx) (Curly Close) "struct pattern field"

    match field with
    | Ok(field, curly) ->
        let str =
            { Ty = state.data
              Field = field.data
              Span = state.data.Span.WithLast curly.Span.Last }

        let isRest (idx, f) =
            match f with
            | RestField _ when idx <> (Array.length field.data) - 1 -> true
            | _ -> false

        let toError (_, f: StructField) = RestAtStructEnd f.Span

        let restError = Array.indexed field.data |> Array.filter isRest |> Array.map toError

        Ok
            { data = StructLit str
              error = Array.concat [ state.error; field.error; restError ]
              rest = field.rest }
    | Error e -> Error e

and internal parsePath (ctx: Context) (state: State<Path>) =
    let rec parsePath (state: State<Path>) =
        match peek state.rest with
        | Some({ Data = Identifier sym; Span = span }, i) ->
            let id = { Sym = sym; Span = span }

            let curr = state.rest[i..]

            let error = state.error

            match peek curr with
            | Some({ Data = ColonColon }, i) ->
                let curr = curr[i..]

                match peek curr with
                | Some({ Data = Operator(Cmp Lt | Arith Shl) }, i) ->
                    let generic =
                        parseLtGt curr[i - 1 ..] (parseType ctx.InTypeInst) "type instantiation"

                    match generic with
                    | Error e -> state.MergeFatalError e
                    | Ok g ->
                        let ty, last = g.data

                        let newExpr =
                            { state.data with
                                Seg = Array.append state.data.Seg [| id, ty |]
                                Span = state.data.Span.WithLast last.Last }

                        parsePath
                            { data = newExpr
                              error = Array.append error g.error
                              rest = g.rest }

                | _ ->
                    let newExpr =
                        { state.data with
                            Seg = Array.append state.data.Seg [| id, [||] |]
                            Span = state.data.Span.WithLast span.Last }

                    parsePath
                        { data = newExpr
                          rest = curr
                          error = error }
            | _ ->
                let newExpr =
                    { state.data with
                        Seg = Array.append state.data.Seg [| id, [||] |]
                        Span = state.data.Span.WithLast span.Last }

                Ok
                    { data = newExpr
                      rest = curr
                      error = error }

        | _ -> Ok state

    match parsePath state with
    | Error e -> Error e
    | Ok s ->
        let state =
            if
                s.data.Prefix = None
                && s.data.Seg.Length = 1
                && Array.length (snd s.data.Seg[0]) = 0
            then

                { data = Id(fst s.data.Seg[0])
                  error = s.error
                  rest = s.rest }
            else
                let error =
                    if s.data.Seg.Length = 0 then
                        Array.append s.error [| IncompletePath s.data.Span |]
                    else
                        s.error

                { data = Path s.data
                  error = error
                  rest = s.rest }

        match maybeStruct ctx s.rest with
        | Some i ->
            parseStruct
                ctx
                { data = s.data
                  error = state.error
                  rest = s.rest[i..] }

        | None -> Ok state

and internal rangeParser ctx input =
    match peek input with
    | None -> None
    | Some({ Data = data }, _) when canStartExpr data -> Some(parseWithPrec -1 ctx input)
    | Some(_, _) -> None

and internal parseClosure ctx (input: Token[]) =
    let op = input[0]
    let first = op.Span.First

    let param =
        match op.Data with
        | Operator(Arith BitOr) ->
            let param =
                parseCommaSeq input[1..] (parseParam ctx) (Operator(Arith BitOr)) "function type parameter"

            match param with
            | Ok(s, _) -> Ok s
            | Error e -> Error e
        | Operator(Logic Or) ->
            Ok
                { data = [||]
                  error = [||]
                  rest = input[1..] }
        | _ -> failwith "unreachable"

    match param with
    | Ok param ->
        let ret =
            match peek param.rest with
            | Some({ Data = Arrow }, i) ->
                match parseType ctx param.rest[i..] with
                | Ok ret ->
                    Ok
                        { data = Some ret.data
                          error = Array.append param.error ret.error
                          rest = ret.rest }
                | Error e -> Error e
            | Some(_, _) ->
                Ok
                    { data = None
                      error = param.error
                      rest = param.rest }
            | None -> param.FatalError(IncompleteAtEnd "closure")

        match ret with
        | Error e -> Error e
        | Ok ret ->
            match parseExpr Context.InFn ret.rest with
            | Error e -> ret.MergeFatalError e
            | Ok(body: State<Expr>) ->
                let closure =
                    { Param = param.data
                      Ret = ret.data
                      Body = body.data
                      Span = Span.Make first body.data.Span.Last }

                Ok
                    { data = Closure closure
                      error = Array.concat [ param.error; ret.error; body.error ]
                      rest = body.rest }
    | Error e -> Error e

and internal parseCond (ctx: Context) input =
    match peekWith input (Reserved LET) with
    | Some(span, i) ->
        match parsePat ctx.NotInDecl input[i..] with
        | Error e -> Error e
        | Ok pat ->
            match consume pat.rest Eq "if let condition" with
            | Error e -> pat.FatalError e
            | Ok(_, i) ->
                match parseExpr ctx.InCond pat.rest[i..] with
                | Error e -> pat.MergeFatalError e
                | Ok expr ->
                    let cond =
                        { Pat = pat.data
                          Value = expr.data
                          Span = span.WithLast expr.data.Span.Last }

                    let error = Array.append pat.error expr.error

                    Ok
                        { data = LetCond cond
                          error = error
                          rest = expr.rest }
    | None ->
        match parseExpr ctx.InCond input with
        | Error e -> Error e
        | Ok expr ->
            Ok
                { data = BoolCond expr.data
                  error = expr.error
                  rest = expr.rest }

and internal parseMatchBranch (ctx: Context) state =
    match peek state.rest with
    | None -> Error [| IncompleteAtEnd "match expression" |]
    | Some({ Data = Curly Close; Span = span }, i) -> Ok({ state with rest = state.rest[i..] }, span)
    | _ ->
        match parsePat ctx.NotInDecl state.rest with
        | Error e -> Error e
        | Ok pat ->
            let guard, pat =
                match peekWith pat.rest (Reserved IF) with
                | None -> None, Ok pat
                | Some(_, i) ->
                    match parseExpr ctx pat.rest[i..] with
                    | Error e -> None, Error e
                    | Ok guard ->
                        Some guard.data,
                        Ok
                            { pat with
                                error = Array.append pat.error guard.error
                                rest = guard.rest }

            match pat with
            | Error e -> Error e
            | Ok pat ->
                match consume pat.rest FatArrow "match branch" with
                | Error e -> pat.FatalError e
                | Ok(_, i) ->
                    match parseExpr ctx pat.rest[i..] with
                    | Error e -> pat.MergeFatalError e
                    | Ok res ->
                        let branch =
                            { Pat = pat.data
                              Expr = res.data
                              Guard = guard
                              Span = pat.data.Span.WithLast res.data.Span.Last }

                        let newState =
                            { data = Array.append state.data [| branch |]
                              error = Array.concat [ pat.error; res.error ]
                              rest = res.rest }

                        match res.data with
                        | Block _ ->
                            let i =
                                match peekWith newState.rest Comma with
                                | Some(_, i) -> i
                                | None -> 0

                            parseMatchBranch
                                ctx
                                { newState with
                                    rest = newState.rest[i..] }
                        | _ ->
                            match peek res.rest with
                            | Some({ Data = Curly Close }, _) -> parseMatchBranch ctx newState
                            | Some({ Data = Comma }, i) ->
                                parseMatchBranch
                                    ctx
                                    { newState with
                                        rest = newState.rest[i..] }

                            | Some(token, _) -> newState.FatalError(UnexpectedToken(token, "match branch"))
                            | None -> newState.FatalError(IncompleteAtEnd "match branch")

and internal parsePrefix ctx input =
    match peek input with
    | Some({ Data = Lit l; Span = span }, i) ->
        Ok
            { data = LitExpr(l, span)
              error = [||]
              rest = input[i..] }
    | Some({ Data = Underline; Span = span }, i) ->
        Ok
            { data = Id { Sym = "_"; Span = span }
              error = [||]
              rest = input[i..] }
    | Some({ Data = Reserved(PACKAGE | LOWSELF | SELF as kw)
             Span = span },
           i) ->
        let prefix =
            match kw with
            | PACKAGE -> Package
            | LOWSELF -> LowSelf
            | SELF -> Self
            | _ -> failwith "unreachable"

        let path =
            { Prefix = Some prefix
              Seg = [||]
              Span = span }

        let path =
            { data = path
              error = [||]
              rest = input[i..] }

        match peekWith path.rest ColonColon with
        | Some(_, i) -> parsePath ctx { path with rest = path.rest[i..] }
        | None ->
            match prefix with
            | LowSelf ->
                Ok
                    { data = SelfExpr span
                      error = if ctx.inMethod then [||] else [| OutofMethod span |]
                      rest = input[i..] }
            | Package ->
                Ok
                    { data = Path path.data
                      error = [| IncompletePath span |]
                      rest = path.rest }
            | Self ->
                let error =
                    if ctx.inTrait || ctx.inImpl then
                        [||]
                    else
                        [| OutofMethod span |]

                match maybeStruct ctx path.rest with
                | Some i ->
                    parseStruct
                        ctx
                        { data = path.data
                          error = error
                          rest = path.rest[i..] }
                | None ->
                    Ok
                        { data = Path path.data
                          error = error
                          rest = path.rest }
    | Some({ Data = Identifier _; Span = span }, _) ->
        let path =
            { Prefix = None
              Seg = [||]
              Span = span }

        let newState =
            { data = path
              error = [||]
              rest = input }

        parsePath ctx newState

    | Some({ Data = Paren Open; Span = span }, i) ->
        let first = span.First
        let input = input[i..]
        let ctx = ctx.NotInCond

        match parseCommaSeq input (parseExpr ctx) (Paren Close) "parenthesis expression" with
        | Error e -> Error e
        | Ok(state, paren) ->
            match state.data.Length with
            | 1 ->
                Ok
                    { data = state.data[0]
                      error = state.error
                      rest = state.rest }
            | _ ->
                let span = paren.Span.WithFirst first
                let expr = { Ele = state.data; span = span }

                Ok
                    { data = Tuple expr
                      error = state.error
                      rest = state.rest }

    | Some({ Data = Bracket Open; Span = span } as token, i) ->
        let first = span.First
        let input = input[i..]
        let ctx = ctx.NotInCond

        match peek input with
        | None -> Error([| IncompletePair token |])
        | Some({ Data = Bracket Close; Span = span }, i) ->
            let span = span.WithFirst first

            Ok
                { data = Array { Ele = [||]; span = span }
                  error = [||]
                  rest = input[i..] }
        | _ ->
            match parseExpr ctx input with
            | Error e -> Error e
            | Ok firstEle ->
                match peek firstEle.rest with
                | Some({ Data = Bracket Close; Span = span }, i) ->
                    let span = span.WithFirst first

                    Ok
                        { data =
                            Array
                                { Ele = [| firstEle.data |]
                                  span = span }
                          error = firstEle.error
                          rest = firstEle.rest[i..] }
                | Some({ Data = Delimiter Semi }, i) ->
                    match parseExpr ctx firstEle.rest[i..] with
                    | Error e -> Error e
                    | Ok repeat ->
                        match peek repeat.rest with
                        | Some({ Data = Bracket Close; Span = span }, i) ->
                            let span = span.WithFirst first

                            let expr =
                                { Ele = firstEle.data
                                  Count = repeat.data
                                  Span = span }

                            Ok
                                { data = ArrayRepeat expr
                                  error = Array.append firstEle.error repeat.error
                                  rest = firstEle.rest[i..] }
                        | _ -> Error(Array.concat [ firstEle.error; repeat.error; [| IncompletePair token |] ])
                | Some({ Data = Comma }, i) ->
                    match parseCommaSeq firstEle.rest[i..] (parseExpr ctx) (Bracket Close) "array expression" with
                    | Error e -> Error e
                    | Ok(rest, bracket) ->
                        let span = bracket.Span.WithFirst first

                        let expr =
                            { Ele = Array.append [| firstEle.data |] rest.data
                              span = span }

                        Ok
                            { data = Array expr
                              error = Array.append firstEle.error rest.error
                              rest = rest.rest }
                | Some(token, _) -> firstEle.FatalError(UnexpectedToken(token, "array expression"))
                | None -> firstEle.FatalError(IncompletePair token)

    | Some({ Data = Curly Open }, _) ->
        match parseBlock ctx input with
        | Error e -> Error e
        | Ok(b: State<Block>) ->
            Ok
                { data = Block b.data
                  error = b.error
                  rest = b.rest }

    | Some({ Data = Operator(Arith BitOr | Logic Or) }, i) -> parseClosure ctx input[i - 1 ..]

    | Some({ Data = Operator(Arith Sub | Arith Mul | Arith BitAnd as op)
             Span = span },
           i) ->
        let op =
            match op with
            | Arith Sub -> Neg
            | Arith Mul -> Deref
            | Arith BitAnd -> Ref
            | _ -> failwith "unreachable"

        match parseWithPrec 1000 ctx input[i..] with
        | Error e -> Error e
        | Ok(state: State<Expr>) ->
            let expr =
                { Op = op
                  Value = state.data
                  Span = Span.Make span.First state.data.Span.Last }

            Ok { state with data = Unary expr }

    | Some({ Data = Not; Span = span }, i) ->
        match parseWithPrec 1000 ctx input[i..] with
        | Error e -> Error e
        | Ok(state: State<Expr>) ->
            let expr =
                { Op = AST.AST.Not
                  Value = state.data
                  Span = Span.Make span.First state.data.Span.Last }

            Ok { state with data = Unary expr }

    | Some({ Data = Operator(Logic And)
             Span = span },
           i) ->
        match parseWithPrec 1000 ctx input[i..] with
        | Error e -> Error e
        | Ok(state: State<Expr>) ->
            let expr =
                { Op = Ref
                  Value = state.data
                  Span = Span.Make (span.First + 1) state.data.Span.Last }

            let expr =
                { Op = Ref
                  Value = Unary expr
                  Span = expr.Span.WithFirst span.First }

            Ok { state with data = Unary expr }

    | Some({ Data = DotDot | DotDotCaret } as op, i) ->
        parseRangeTo
            { data = None
              error = [||]
              rest = input[i..] }
            op
            (rangeParser ctx)
            rangeCtor

    | Some({ Data = Reserved IF; Span = span }, i) ->
        let rec parseElse (state: State<If>) =
            match peekWith state.rest (Reserved ELSE) with
            | Some(span, i) ->
                match peekWith state.rest[i..] (Reserved IF) with
                | Some(_, j) ->
                    match parseCond ctx state.rest[i + j ..] with
                    | Error e -> Error e
                    | Ok cond ->
                        match parseBlock ctx cond.rest with
                        | Error e -> Error e
                        | Ok(body: State<Block>) ->
                            let elif_ =
                                { Cond = cond.data
                                  Block = body.data
                                  Span = span.WithLast body.data.Span.Last }

                            let newState =
                                { data =
                                    { state.data with
                                        ElseIf = Array.append state.data.ElseIf [| elif_ |] }
                                  error = Array.concat [ state.error; cond.error; body.error ]
                                  rest = body.rest }

                            parseElse newState
                | None ->
                    match parseBlock ctx state.rest[i..] with
                    | Error e -> Error e
                    | Ok(e: State<Block>) ->
                        Ok
                            { data = If { state.data with Else = Some e.data }
                              error = Array.append state.error e.error
                              rest = e.rest }
            | None ->
                Ok
                    { data = If state.data
                      error = state.error
                      rest = state.rest }

        match parseCond ctx input[i..] with
        | Error e -> Error e
        | Ok cond ->
            match parseBlock ctx cond.rest with
            | Error e -> Error e
            | Ok then_ ->
                let expr =
                    { Cond = cond.data
                      Then = then_.data
                      ElseIf = [||]
                      Else = None
                      Span = span.WithLast then_.data.Span.Last }

                parseElse
                    { data = expr
                      error = Array.append cond.error then_.error
                      rest = then_.rest }

    | Some({ Data = Reserved FOR; Span = span }, i) ->
        match parsePat ctx.NotInDecl input[i..] with
        | Error e -> Error e
        | Ok pat ->
            match consume pat.rest (Reserved IN) "for loop in" with
            | Error e -> pat.FatalError e
            | Ok(_, i) ->
                match parseExpr ctx.InCond pat.rest[i..] with
                | Error e -> pat.MergeFatalError e
                | Ok value ->
                    let error = Array.append pat.error value.error

                    match parseBlock ctx.InLoop value.rest with
                    | Error e -> Error(Array.append error e)
                    | Ok block ->
                        let expr =
                            { Var = pat.data
                              Iter = value.data
                              Body = block.data
                              Span = span.WithLast block.data.Span.Last }

                        Ok
                            { data = For expr
                              error = Array.append error block.error
                              rest = block.rest }

    | Some({ Data = Reserved WHILE; Span = span }, i) ->
        match parseCond ctx input[i..] with
        | Error e -> Error e
        | Ok cond ->
            match parseBlock ctx.InLoop cond.rest with
            | Error e -> cond.MergeFatalError e
            | Ok block ->
                let expr =
                    { Cond = cond.data
                      Body = block.data
                      Span = span.WithLast block.data.Span.Last }

                Ok
                    { data = While expr
                      error = Array.append cond.error block.error
                      rest = block.rest }

    | Some({ Data = Reserved BREAK; Span = span } as token, i) ->
        let error = if ctx.inLoop then [| OutOfLoop token |] else [||]

        Ok
            { data = Break span
              error = error
              rest = input[i..] }

    | Some({ Data = Reserved CONTINUE
             Span = span } as token,
           i) ->
        let error = if ctx.inLoop then [| OutOfLoop token |] else [||]

        Ok
            { data = Continue span
              error = error
              rest = input[i..] }

    | Some({ Data = Reserved RETURN; Span = span }, i) ->
        let error = if ctx.inFn then [| OutOfFn span |] else [||]

        match peekInline input[i..] with
        | Some({ Data = data }, _) when canStartExpr data ->
            match parseExpr ctx input[i..] with
            | Error e -> Error e
            | Ok state ->
                let expr =
                    { Value = Some state.data
                      Span = state.data.Span.WithFirst span.First }

                Ok
                    { data = Return expr
                      error = state.error
                      rest = state.rest }
        | _ ->
            Ok
                { data = Return { Value = None; Span = span }
                  error = error
                  rest = input[i..] }

    | Some({ Data = Reserved MATCH; Span = span }, i) ->
        match parseExpr ctx.InCond input[i..] with
        | Error e -> Error e
        | Ok value ->
            match consume value.rest (Curly Open) "match expression" with
            | Error e -> value.FatalError e
            | Ok(_, i) ->
                let state =
                    { data = [||]
                      error = value.error
                      rest = value.rest[i..] }

                match parseMatchBranch ctx state with
                | Error e -> value.MergeFatalError e
                | Ok(branch, last) ->
                    let expr =
                        { Value = value.data
                          Branch = branch.data
                          Span = span.WithLast last.Last }

                    Ok
                        { data = Match expr
                          error = Array.append value.error branch.error
                          rest = branch.rest }

    | Some(token, _) ->
        match tryRecover canStartExpr (parsePrefix ctx) "expression" input with
        | Ok expr -> Ok expr
        | Error i -> Error [| UnexpectedManyToken(token.Span.WithLast input[i].Span.Last, "expression") |]
    | None -> Error [| IncompleteAtEnd "expression" |]

and internal parseFollow prec ctx (state: State<Expr>) =
    match peekInline state.rest with
    | None
    | Some({ Data = Delimiter Semi }, _) -> Ok state
    // <= because of right associativity
    | Some({ Data = Eq | AssignOp _ as data }, i) when prec <= -2 ->
        match peek state.rest[i..] with
        | None -> state.FatalError(Incomplete(state.data.Span, "assign expression"))
        | _ ->
            let assignee = state.data

            let op =
                match data with
                | Eq -> None
                | AssignOp op -> Some op
                | _ -> failwith "unreachable"

            let error =
                if assignee.IsPlace then
                    state.error
                else
                    Array.append state.error [| InvalidLValue assignee |]

            match parseWithPrec -2 ctx state.rest[i..] with
            | Error e -> Error e
            | Ok right ->
                let expr =
                    { Place = state.data
                      Op = op
                      Value = right.data
                      Span = Span.Make state.data.Span.First right.data.Span.Last }

                Ok
                    { data = Assign expr
                      error = error
                      rest = right.rest }
    | Some({ Data = DotDot | DotDotCaret } as op, i) when prec <= -1 ->
        parseRangeTo
            { data = Some state.data
              error = state.error
              rest = state.rest[i..] }
            op
            (rangeParser ctx)
            rangeCtor

    | Some({ Data = Operator op }, i) when prec < precedence op ->
        match peek state.rest[i..] with
        | None -> state.FatalError(Incomplete(state.data.Span, "binary expression"))
        | _ ->
            match parseWithPrec (precedence op) ctx state.rest[i..] with
            | Error e -> Error e
            | Ok right ->
                let span = Span.Make state.data.Span.First right.data.Span.Last

                let expr =
                    { Left = state.data
                      Op = op
                      Right = right.data
                      Span = span }

                Ok
                    { right with
                        data = Binary expr
                        error = Array.append state.error right.error }

    // first token of postfix must be in the same line to avoid ambiguity
    | _ -> parsePostfix ctx prec state

and internal parsePostfix ctx prec state =
    match peekInline state.rest with
    | Some({ Data = Dot }, i) ->
        match peek state.rest[i..] with
        | None -> state.FatalError(Incomplete(state.data.Span, "field access expression"))
        | Some({ Data = Identifier sym; Span = span }, j) ->
            let expr =
                { Receiver = state.data
                  Field = { Sym = sym; Span = span }
                  Span = Span.Make state.data.Span.First span.Last }

            parsePostfix
                ctx
                prec
                { state with
                    data = Field expr
                    rest = state.rest[i + j ..] }
        | Some(token, _) -> state.FatalError(UnexpectedToken(token, "field access"))

    | Some({ Data = Paren Open; Span = span }, i) ->
        let newCtx = ctx.NotInCond

        match peek state.rest with
        | None -> Error([| IncompletePair(Token.Make (Paren Close) span) |])
        | _ ->
            match parseCommaSeq state.rest[i..] (parseExpr newCtx) (Paren Close) "call arguments" with
            | Error e -> Error e
            | Ok(param, paren) ->
                let span = paren.Span.WithFirst state.data.Span.First

                let expr =
                    { Arg = param.data
                      Callee = state.data
                      Span = span }

                parsePostfix
                    ctx
                    prec
                    { data = Call expr
                      error = Array.append state.error param.error
                      rest = param.rest }

    | Some({ Data = Bracket Open } as token, i) ->
        let newCtx = ctx.NotInCond

        match peek state.rest[i..] with
        | None -> state.FatalError(IncompletePair token)
        | _ ->
            match parseExpr newCtx state.rest[i..] with
            | Error e -> Error e
            | Ok idx ->
                match consume idx.rest (Bracket Close) "index expression" with
                | Ok(span, i) ->
                    let expr =
                        { Container = state.data
                          Index = idx.data
                          Span = span.WithFirst state.data.Span.First }

                    parsePostfix
                        ctx
                        prec
                        { data = Index expr
                          error = Array.append state.error idx.error
                          rest = idx.rest[i..] }

                | Error e -> Error(Array.concat [ state.error; idx.error; [| e |] ])

    | Some({ Data = Question; Span = span }, i) ->
        let expr =
            { Base = state.data
              Span = state.data.Span.WithLast span.Last }

        let error = if ctx.inFn then [||] else [| OutOfFn span |]

        parsePostfix
            ctx
            prec
            { data = TryReturn expr
              error = Array.append state.error error
              rest = state.rest[i..] }

    | _ -> Ok state

and internal parseRecursive prec ctx state =
    match parseFollow prec ctx state with
    | Error e -> Error e
    | Ok newState ->
        match peek newState.rest with
        | Some({ Data = Operator op }, _) when prec < precedence op -> parseRecursive prec ctx newState
        | Some({ Data = DotDot | DotDotCaret }, _) when prec <= -1 -> parseRecursive prec ctx newState
        | Some({ Data = AssignOp _ | Eq }, _) when prec <= -2 -> parseRecursive prec ctx newState
        | _ -> Ok newState

and internal parseWithPrec prec ctx input =
    match parsePrefix ctx input with
    | Error e -> Error e
    | Ok state -> parseRecursive prec ctx state

and internal parseExpr = parseWithPrec -100
