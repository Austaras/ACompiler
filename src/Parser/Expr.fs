module Parser.Expr

open AST
open AST
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
    | Operator(Arithmetic Sub | Arithmetic Mul | Arithmetic BitAnd | Arithmetic BitOr | Arithmetic LogicalOr | Gt)
    | Not
    | Reserved(PACKAGE | SELF | LOWSELF | IF | MATCH | FOR | WHILE | RETURN | BREAK | CONTINUE)
    | DotDot
    | DotDotCaret -> true
    | _ -> false

let internal mayBeStruct ctx input =
    if ctx.inCond then
        None
    else
        match peekInline input with
        | Some({ data = Curly Open }, i) -> Some i
        | _ -> None

let rangeCtor (from: Option<Expr>) (to_: Option<Expr>) exclusive span =
    let first =
        match from with
        | Some e -> e.span.first
        | None -> span.first

    let last =
        match to_ with
        | Some e -> e.span.last
        | None -> span.last

    Range
        { from = from
          to_ = to_
          exclusive = exclusive
          span = Span.Make first last }

let rec internal parseStructField ctx input =
    match peek input with
    | Some({ data = Identifier sym; span = span }, i) ->
        let id = { sym = sym; span = span }

        match peekWith input[i..] Colon with
        | Some(_, j) ->
            match parseExpr ctx input[i + j ..] with
            | Error e -> Error e
            | Ok(v: State<Expr>) ->
                Ok
                    { data =
                        KeyValueField
                            { name = id.sym
                              value = v.data
                              span = v.data.span.WithFirst span.first }
                      error = v.error
                      rest = v.rest }
        | None ->
            Ok
                { data = ShorthandField id
                  error = [||]
                  rest = input[i..] }

    | Some({ data = DotDot; span = span }, i) ->
        match parseExpr ctx input[i..] with
        | Error e -> Error e
        | Ok(v: State<Expr>) ->
            let span = span.WithLast v.data.span.last

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
            { ty = state.data
              field = field.data
              span = state.data.span.WithLast curly.span.last }

        let isRest (idx, f) =
            match f with
            | RestField _ when idx <> (Array.length field.data) - 1 -> true
            | _ -> false

        let toError (_, f: StructField) = RestAtStructEnd f.span

        let restError = Array.indexed field.data |> Array.filter isRest |> Array.map toError

        Ok
            { data = StructLit str
              error = Array.concat [ state.error; field.error; restError ]
              rest = field.rest }
    | Error e -> Error e

and internal parsePath (ctx: Context) (state: State<Path>) =
    let rec parsePath (state: State<Path>) =
        match peek state.rest with
        | Some({ data = Identifier sym; span = span }, i) ->
            let id = { sym = sym; span = span }

            let curr = state.rest[i..]

            let error =
                if sym = "_" then
                    Array.append state.error [| InvalidCatchAll span |]
                else
                    state.error

            match peek curr with
            | Some({ data = ColonColon }, i) ->
                let curr = curr[i..]

                match peek curr with
                | Some({ data = Operator Lt | Operator(Arithmetic Shl) }, i) ->
                    let generic =
                        parseLtGt curr[i - 1 ..] (parseType ctx.InTypeInst) "type instantiation"

                    match generic with
                    | Error e -> state.MergeFatalError e
                    | Ok g ->
                        let ty, last = g.data

                        let newExpr =
                            { state.data with
                                seg = Array.append state.data.seg [| id, ty |]
                                span = state.data.span.WithLast last.last }

                        parsePath
                            { data = newExpr
                              error = Array.append error g.error
                              rest = g.rest }

                | _ ->
                    let newExpr =
                        { state.data with
                            seg = Array.append state.data.seg [| id, [||] |]
                            span = state.data.span.WithLast span.last }

                    parsePath
                        { data = newExpr
                          rest = curr
                          error = error }
            | _ ->
                let newExpr =
                    { state.data with
                        seg = Array.append state.data.seg [| id, [||] |]
                        span = state.data.span.WithLast span.last }

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
                s.data.prefix = None
                && s.data.seg.Length = 1
                && Array.length (snd s.data.seg[0]) = 0
            then

                { data = Id(fst s.data.seg[0])
                  error = s.error
                  rest = s.rest }
            else
                let error =
                    if s.data.seg.Length = 0 then
                        Array.append s.error [| IncompletePath s.data.span |]
                    else
                        s.error

                { data = Path s.data
                  error = error
                  rest = s.rest }

        match mayBeStruct ctx s.rest with
        | Some i ->
            let res =
                parseStruct
                    ctx
                    { data = s.data
                      error = state.error
                      rest = s.rest[i..] }

            match res with
            | Ok { data = Path _ } -> Ok state
            | r -> r
        | None -> Ok state

and internal rangeParser ctx input =
    match peek input with
    | None -> None
    | Some({ data = data }, _) when canStartExpr data -> Some(parseWithPrec -1 ctx input)
    | Some(_, _) -> None

and internal parseClosure ctx typeParam (input: Token[]) =
    let op = input[0]
    let first = op.span.first

    let param =
        match op.data with
        | Operator(Arithmetic BitOr) ->
            let param =
                parseCommaSeq input[1..] (parseParam ctx) (Operator(Arithmetic BitOr)) "function type parameter"

            match param with
            | Ok(s, _) -> Ok s
            | Error e -> Error e
        | Operator(Arithmetic LogicalOr) ->
            Ok
                { data = [||]
                  error = [||]
                  rest = input[1..] }
        | _ -> failwith "unreachable"

    match param with
    | Ok param ->
        let ret =
            match peek param.rest with
            | Some({ data = Arrow }, i) ->
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
                    { typeParam = typeParam
                      param = param.data
                      ret = ret.data
                      body = body.data
                      span = Span.Make first body.data.span.last }

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
                        { pat = pat.data
                          value = expr.data
                          span = span.WithLast expr.data.span.last }

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
    | Some({ data = Curly Close; span = span }, i) -> Ok({ state with rest = state.rest[i..] }, span)
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
                            { pat = pat.data
                              expr = res.data
                              guard = guard
                              span = pat.data.span.WithLast res.data.span.last }

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
                            | Some({ data = Curly Close }, _) -> parseMatchBranch ctx newState
                            | Some({ data = Comma }, i) ->
                                parseMatchBranch
                                    ctx
                                    { newState with
                                        rest = newState.rest[i..] }

                            | Some(token, _) -> newState.FatalError(UnexpectedToken(token, "match branch"))
                            | None -> newState.FatalError(IncompleteAtEnd "match branch")

and internal parsePrefix ctx input =
    match peek input with
    | Some({ data = Lit l; span = span }, i) ->
        Ok
            { data = LitExpr(l, span)
              error = [||]
              rest = input[i..] }
    | Some({ data = Reserved(PACKAGE | LOWSELF | SELF as kw)
             span = span },
           i) ->
        let prefix =
            match kw with
            | PACKAGE -> Package
            | LOWSELF -> LowSelf
            | SELF -> Self
            | _ -> failwith "unreachable"

        let path =
            { prefix = Some prefix
              seg = [||]
              span = span }

        let path =
            { data = path
              error = [||]
              rest = input[i..] }

        match peekWith path.rest ColonColon with
        | Some(_, i) -> parsePath ctx { path with rest = path.rest[i..] }
        | None ->
            let error =
                match prefix with
                | LowSelf -> if ctx.inMethod then [||] else [| OutofMethod span |]
                | Self ->
                    if ctx.inTrait || ctx.inImpl then
                        [| IncompletePath span |]
                    else
                        [| OutofMethod span |]
                | Package -> [| IncompletePath span |]

            match prefix with
            | LowSelf ->
                Ok
                    { data = SelfExpr span
                      error = error
                      rest = input[i..] }
            | Package
            | Self ->
                Ok
                    { data = Path path.data
                      error = error
                      rest = path.rest }
    | Some({ data = Identifier _; span = span }, _) ->
        let path =
            { prefix = None
              seg = [||]
              span = span }

        let newState =
            { data = path
              error = [||]
              rest = input }

        parsePath ctx newState

    | Some({ data = Paren Open; span = span }, i) ->
        let first = span.first
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
                let span = paren.span.WithFirst first
                let expr = { element = state.data; span = span }

                Ok
                    { data = Tuple expr
                      error = state.error
                      rest = state.rest }

    | Some({ data = Bracket Open; span = span } as token, i) ->
        let first = span.first
        let input = input[i..]
        let ctx = ctx.NotInCond

        match peek input with
        | None -> Error([| IncompletePair token |])
        | Some({ data = Bracket Close; span = span }, i) ->
            let span = span.WithFirst first

            Ok
                { data = Array { element = [||]; span = span }
                  error = [||]
                  rest = input[i..] }
        | _ ->
            match parseExpr ctx input with
            | Error e -> Error e
            | Ok firstEle ->
                match peek firstEle.rest with
                | Some({ data = Bracket Close; span = span }, i) ->
                    let span = span.WithFirst first

                    Ok
                        { data =
                            Array
                                { element = [| firstEle.data |]
                                  span = span }
                          error = firstEle.error
                          rest = firstEle.rest[i..] }
                | Some({ data = Delimiter Semi }, i) ->
                    match parseExpr ctx firstEle.rest[i..] with
                    | Error e -> Error e
                    | Ok repeat ->
                        match peek repeat.rest with
                        | Some({ data = Bracket Close; span = span }, i) ->
                            let span = span.WithFirst first

                            let expr =
                                { element = firstEle.data
                                  repeat = repeat.data
                                  span = span }

                            Ok
                                { data = ArrayRepeat expr
                                  error = Array.append firstEle.error repeat.error
                                  rest = firstEle.rest[i..] }
                        | _ -> Error(Array.concat [ firstEle.error; repeat.error; [| IncompletePair token |] ])
                | Some({ data = Comma }, i) ->
                    match parseCommaSeq firstEle.rest[i..] (parseExpr ctx) (Bracket Close) "array expression" with
                    | Error e -> Error e
                    | Ok(rest, bracket) ->
                        let span = bracket.span.WithFirst first

                        let expr =
                            { element = Array.append [| firstEle.data |] rest.data
                              span = span }

                        Ok
                            { data = Array expr
                              error = Array.append firstEle.error rest.error
                              rest = rest.rest }
                | Some(token, _) -> firstEle.FatalError(UnexpectedToken(token, "array expression"))
                | None -> firstEle.FatalError(IncompletePair token)

    | Some({ data = Curly Open }, _) ->
        match parseBlock ctx input with
        | Error e -> Error e
        | Ok(b: State<Block>) ->
            Ok
                { data = Block b.data
                  error = b.error
                  rest = b.rest }

    | Some({ data = Operator(Lt | Arithmetic Shr) }, i) ->
        let typeParam =
            parseLtGt input[i - 1 ..] (parseTypeParam ctx) "closure type parameter"

        match typeParam with
        | Ok param ->
            let data, _ = param.data
            let closure = parseClosure ctx data param.rest

            match closure with
            | Ok c ->
                Ok
                    { c with
                        error = Array.append param.error c.error }
            | Error e -> param.MergeFatalError e
        | Error e -> Error e

    | Some({ data = Operator(Arithmetic(BitOr | LogicalOr)) }, i) -> parseClosure ctx [||] input[i - 1 ..]

    | Some({ data = Operator(Arithmetic Sub | Arithmetic Mul | Arithmetic BitAnd as op)
             span = span },
           i) ->
        let op =
            match op with
            | Arithmetic Sub -> Neg
            | Arithmetic Mul -> Deref
            | Arithmetic BitAnd -> Ref
            | _ -> failwith "unreachable"

        match parseWithPrec 1000 ctx input[i..] with
        | Error e -> Error e
        | Ok(state: State<Expr>) ->
            let expr =
                { op = op
                  expr = state.data
                  span = Span.Make span.first state.data.span.last }

            Ok { state with data = Unary expr }

    | Some({ data = Not; span = span }, i) ->
        match parseWithPrec 1000 ctx input[i..] with
        | Error e -> Error e
        | Ok(state: State<Expr>) ->
            let expr =
                { op = AST.Not
                  expr = state.data
                  span = Span.Make span.first state.data.span.last }

            Ok { state with data = Unary expr }

    | Some({ data = Operator(Arithmetic LogicalAnd)
             span = span },
           i) ->
        match parseWithPrec 1000 ctx input[i..] with
        | Error e -> Error e
        | Ok(state: State<Expr>) ->
            let expr =
                { op = Deref
                  expr = state.data
                  span = Span.Make (span.first + 1) state.data.span.last }

            let expr =
                { op = Deref
                  expr = Unary expr
                  span = expr.span.WithFirst span.first }

            Ok { state with data = Unary expr }

    | Some({ data = DotDot | DotDotCaret } as op, i) ->
        parseRangeTo
            { data = None
              error = [||]
              rest = input[i..] }
            op
            (rangeParser ctx)
            rangeCtor

    | Some({ data = Reserved IF; span = span }, i) ->
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
                                { cond = cond.data
                                  block = body.data
                                  span = span.WithLast body.data.span.last }

                            let newState =
                                { data =
                                    { state.data with
                                        elseif = Array.append state.data.elseif [| elif_ |] }
                                  error = Array.concat [ state.error; cond.error; body.error ]
                                  rest = body.rest }

                            parseElse newState
                | None ->
                    match parseBlock ctx state.rest[i..] with
                    | Error e -> Error e
                    | Ok(e: State<Block>) ->
                        Ok
                            { data = If { state.data with else_ = Some e.data }
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
                    { cond = cond.data
                      then_ = then_.data
                      elseif = [||]
                      else_ = None
                      span = span.WithLast then_.data.span.last }

                parseElse
                    { data = expr
                      error = Array.append cond.error then_.error
                      rest = then_.rest }

    | Some({ data = Reserved FOR; span = span }, i) ->
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
                            { var = pat.data
                              iter = value.data
                              body = block.data
                              span = span.WithLast block.data.span.last }

                        Ok
                            { data = For expr
                              error = Array.append error block.error
                              rest = block.rest }

    | Some({ data = Reserved WHILE; span = span }, i) ->
        match parseCond ctx input[i..] with
        | Error e -> Error e
        | Ok cond ->
            match parseBlock ctx.InLoop cond.rest with
            | Error e -> cond.MergeFatalError e
            | Ok block ->
                let expr =
                    { cond = cond.data
                      body = block.data
                      span = span.WithLast block.data.span.last }

                Ok
                    { data = While expr
                      error = Array.append cond.error block.error
                      rest = block.rest }

    | Some({ data = Reserved BREAK; span = span } as token, i) ->
        let error = if ctx.inLoop then [| OutOfLoop token |] else [||]

        Ok
            { data = Break span
              error = error
              rest = input[i..] }

    | Some({ data = Reserved CONTINUE
             span = span } as token,
           i) ->
        let error = if ctx.inLoop then [| OutOfLoop token |] else [||]

        Ok
            { data = Continue span
              error = error
              rest = input[i..] }

    | Some({ data = Reserved RETURN; span = span }, i) ->
        let error = if ctx.inFn then [| OutOfFn span |] else [||]

        match peekInline input[i..] with
        | Some({ data = data }, _) when canStartExpr data ->
            match parseExpr ctx input[i..] with
            | Error e -> Error e
            | Ok state ->
                let expr =
                    { value = Some state.data
                      span = state.data.span.WithFirst span.first }

                Ok
                    { data = Return expr
                      error = state.error
                      rest = state.rest }
        | _ ->
            Ok
                { data = Return { value = None; span = span }
                  error = error
                  rest = input[i..] }

    | Some({ data = Reserved MATCH; span = span }, i) ->
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
                        { expr = value.data
                          branch = branch.data
                          span = span.WithLast last.last }

                    Ok
                        { data = Match expr
                          error = Array.append value.error branch.error
                          rest = branch.rest }

    | Some(token, _) ->
        match tryRecover canStartExpr (parsePrefix ctx) "expression" input with
        | Ok expr -> Ok expr
        | Error i -> Error [| UnexpectedManyToken(token.span.WithLast input[i].span.last, "expression") |]
    | None -> Error [| IncompleteAtEnd "expression" |]

and internal parseFollow prec ctx (state: State<Expr>) =
    match peek state.rest with
    | None
    | Some({ data = Delimiter Semi }, _) -> Ok state
    // <= because of right associativity
    | Some({ data = Eq | AssignOp _ as data }, i) when prec <= -2 ->
        match peek state.rest[i..] with
        | None -> state.FatalError(Incomplete(state.data.span, "assign expression"))
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
                    { place = state.data
                      op = op
                      value = right.data
                      span = Span.Make state.data.span.first right.data.span.last }

                Ok
                    { data = Assign expr
                      error = error
                      rest = right.rest }
    | Some({ data = DotDot | DotDotCaret } as op, i) when prec <= -1 ->
        parseRangeTo
            { data = Some state.data
              error = state.error
              rest = state.rest[i..] }
            op
            (rangeParser ctx)
            rangeCtor

    | Some({ data = Operator op }, i) when prec < op.precedence ->
        match peek state.rest[i..] with
        | None -> state.FatalError(Incomplete(state.data.span, "binary expression"))
        | _ ->
            match parseWithPrec op.precedence ctx state.rest[i..] with
            | Error e -> Error e
            | Ok right ->
                let span = Span.Make state.data.span.first right.data.span.last

                let expr =
                    { left = state.data
                      op = op
                      right = right.data
                      span = span }

                Ok
                    { right with
                        data = Binary expr
                        error = Array.append state.error right.error }

    // first token of postfix must be in the same line to avoid ambiguity
    | _ -> parsePostfix ctx prec state

and internal parsePostfix ctx prec state =
    match peekInline state.rest with
    | Some({ data = Dot }, i) ->
        match peek state.rest[i..] with
        | None -> state.FatalError(Incomplete(state.data.span, "field access expression"))
        | Some({ data = Identifier sym; span = span }, j) ->
            let expr =
                { receiver = state.data
                  prop = { sym = sym; span = span }
                  span = Span.Make state.data.span.first span.last }

            parsePostfix
                ctx
                prec
                { state with
                    data = Field expr
                    rest = state.rest[i + j ..] }
        | Some(token, _) -> state.FatalError(UnexpectedToken(token, "field access"))

    | Some({ data = Paren Open; span = span }, i) ->
        let newCtx = ctx.NotInCond

        match peek state.rest with
        | None -> Error([| IncompletePair(Token.Make (Paren Close) span) |])
        | _ ->
            match parseCommaSeq state.rest[i..] (parseExpr newCtx) (Paren Close) "call arguments" with
            | Error e -> Error e
            | Ok(param, paren) ->
                let span = paren.span.WithFirst state.data.span.first

                let expr =
                    { arg = param.data
                      callee = state.data
                      span = span }

                parsePostfix
                    ctx
                    prec
                    { data = Call expr
                      error = Array.append state.error param.error
                      rest = param.rest }

    | Some({ data = Bracket Open } as token, i) ->
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
                        { container = state.data
                          index = idx.data
                          span = span.WithFirst state.data.span.first }

                    parsePostfix
                        ctx
                        prec
                        { data = Index expr
                          error = Array.append state.error idx.error
                          rest = idx.rest[i..] }

                | Error e -> Error(Array.concat [ state.error; idx.error; [| e |] ])

    | Some({ data = Question; span = span }, i) ->
        let expr =
            { base_ = state.data
              span = state.data.span.WithLast span.last }

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
        | Some({ data = Operator op }, _) when prec < op.precedence -> parseRecursive prec ctx newState
        | Some({ data = DotDot | DotDotCaret }, _) when prec <= -1 -> parseRecursive prec ctx newState
        | Some({ data = AssignOp _ | Eq }, _) when prec <= -2 -> parseRecursive prec ctx newState
        | _ -> Ok newState

and internal parseWithPrec prec ctx input =
    match parsePrefix ctx input with
    | Error e -> Error e
    | Ok state -> parseRecursive prec ctx state

and internal parseExpr = parseWithPrec -100
