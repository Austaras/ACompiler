module Parser.Parser

open AST
open Lexer

type Error =
    | LexError of Lexer.Error
    | UnexpectedToken of Lexer.Token * string
    | UnexpectedManyToken of AST.Span * string
    | Incomplete of AST.Span * string
    | IncompleteAtEnd of string
    | IncompletePair of Lexer.Token
    | IncompletePath of AST.Span
    | InvalidLValue of AST.Expr
    | OutOfLoop of Lexer.Token
    | OutOfFn of AST.Span
    | OutofMethod of AST.Span
    | ConstInType of Lexer.Token
    | EmptyEnum of AST.Span
    | EmptyTypeInst of AST.Span
    | TooManyRestPat of AST.Span
    | InvalidRangePat of Lexer.Token
    | InclusiveNoEnd of AST.Span
    | RestAtStructEnd of AST.Span
    | VisibilityNotAllowed of Lexer.Token
    | TopLevelExpr of AST.Span
    | NeedDelimiter of AST.Span
    | ConstPat of AST.Span
    | InvalidCatchAll of AST.Span

type internal Context =
    { inLoop: bool
      inFn: bool
      inCond: bool
      mayHaveVis: bool
      inMethod: bool
      inDecl: bool
      inTypeInst: bool }

    static member Normal =
        { inLoop = false
          inFn = false
          inCond = false
          mayHaveVis = true
          inMethod = false
          inDecl = false
          inTypeInst = false }

    static member InFn =
        { inLoop = false
          inFn = true
          inCond = false
          mayHaveVis = false
          inMethod = false
          inDecl = false
          inTypeInst = false }

    member this.InLoop = { this with inLoop = true }
    member this.InTypeInst = { this with inTypeInst = true }
    member this.InDecl = { this with inDecl = true }
    member this.NotInDecl = { this with inDecl = false }
    member this.InCond = { this with inCond = true }
    member this.NotInCond = { this with inCond = false }

type internal State<'T> =
    {
        data: 'T
        /// recoverable error
        error: Error[]
        rest: Lexer.Token[]
    }

    member this.FatalError e = Error(Array.append this.error [| e |])

    member this.MergeFatalError other = Error(Array.append this.error other)

open AST
open Lexer

let internal peek (input: Token[]) =
    let rec peek i =
        if i = input.Length then
            None
        else
            match input[i].data with
            | Comment _
            | Delimiter CR
            | Delimiter LF -> peek (i + 1)
            | _ -> Some(input[i], i + 1)

    peek 0

let peekInline (input: Token[]) =
    let rec peek i =
        if i = input.Length then
            None
        else
            match input[i].data with
            | Comment _ -> peek (i + 1)
            | _ -> Some(input[i], i + 1)

    peek 0

let peekWith input token =
    match peek input with
    | Some({ data = data; span = span }, i) when data = token -> Some(span, i)
    | _ -> None

let consume input token error =
    match peek input with
    | Some({ data = data; span = span }, i) when data = token -> Ok(span, i)
    | Some(token, _) -> Error(UnexpectedToken(token, error))
    | None -> Error(IncompleteAtEnd(error))

let internal tryRecover canStart parser msg (input: Token[]) =
    let rec tryRecover i unexpected =
        match peek input[i..] with
        | Some({ data = Delimiter Semi }, i) -> Error(i - 1)
        | Some({ data = data } as token, j) ->
            let i = i + j
            let unexpected = Array.append unexpected [| token |]

            if canStart data then
                match parser input[i - 1 ..] with
                | Ok o ->
                    let error =
                        if unexpected.Length = 1 then
                            UnexpectedToken(unexpected[0], msg)
                        else
                            UnexpectedManyToken(
                                Span.Make unexpected[0].span.first (Array.last unexpected).span.last,
                                msg
                            )

                    Ok
                        { o with
                            error = Array.append [| error |] o.error }
                | Error _ -> tryRecover i unexpected
            else
                tryRecover i unexpected
        | None -> Error(input.Length - 1)

    tryRecover 0 [||]

let internal parseCommaSeq (input: Lexer.Token[]) parser limiter error =
    let limiter =
        if limiter = Operator Gt then
            fun t ->
                match t with
                | Operator Gt
                | Operator GtEq
                | Operator(Arithmetic Shr)
                | AssignOp Shr -> true
                | _ -> false
        else
            fun t -> t = limiter

    let state =
        { data = [||]
          error = [||]
          rest = input }

    let rec parseRecursive (state: State<_>) =
        match peek state.rest with
        | Some(token, i) when limiter token.data -> Ok({ state with rest = state.rest[i..] }, token)
        | _ ->
            match parser state.rest with
            | Error e -> state.MergeFatalError e
            | Ok(newState: State<_>) ->
                let newState =
                    { data = Array.append state.data [| newState.data |]
                      error = Array.append state.error newState.error
                      rest = newState.rest }

                match peek newState.rest with
                | Some({ data = Comma }, i) ->
                    parseRecursive (
                        { newState with
                            rest = newState.rest[i..] }
                    )
                | Some(token, i) when limiter token.data ->
                    Ok(
                        { newState with
                            rest = newState.rest[i..] },
                        token
                    )
                | Some(_, i) ->
                    parseRecursive
                        { newState with
                            error = Array.append newState.error [| NeedDelimiter newState.rest[i - 1].span |] }
                | None -> newState.FatalError(IncompleteAtEnd "comma seq")

    match parseRecursive state with
    | Ok(s, p) -> Ok(s, p)
    | Error e ->
        let last = e.Length - 1

        match Array.last e with
        | IncompleteAtEnd _ -> Array.set e last (IncompleteAtEnd error)
        | UnexpectedToken(t, _) -> Array.set e last (UnexpectedToken(t, error))
        | _ -> ()

        Error e

/// parse from < to >
let internal parseLtGt (input: Token[]) parser error =
    let rest =
        match input[0].data with
        | Operator Lt -> input[1..]
        | Operator(Arithmetic Shl) ->
            Array.set
                input
                0
                { data = Operator Lt
                  span = input[0].span.ShrinkFirst 1 }

            input
        | _ -> failwith "unreachable"

    let param = parseCommaSeq rest parser (Operator Gt) error

    let rec splitAndMerge op (span: Span) (input: Token[]) =
        let canMerge =
            match op with
            | Operator Gt
            | Eq -> true
            | Operator GtEq -> false
            | _ -> failwith "unreachable"

        let span = span.ShrinkFirst 1

        if canMerge then
            let first, rest =
                let follow =
                    match Array.tryHead input with
                    | Some token when token.span.first - 1 = span.last -> Some token
                    | Some _ -> None
                    | None -> None

                match op, follow with
                // >> >
                | Operator Gt, (Some { data = Operator Gt; span = span }) ->
                    { data = Operator(Arithmetic Shr)
                      span = Span.Make (span.first - 1) (span.first) },
                    input[1..]
                // >> =
                | Operator Gt, (Some { data = Eq; span = span }) ->

                    { data = Operator GtEq
                      span = Span.Make (span.first - 1) (span.first) },
                    input[1..]
                // >> >=
                | Operator Gt, (Some { data = Operator GtEq; span = span }) ->
                    { data = AssignOp Shr
                      span = Span.Make (span.first - 1) (span.first) },
                    input[1..]
                // >> >>
                | Operator Gt,
                  (Some { data = Operator(Arithmetic Shr)
                          span = span }) ->
                    let first =
                        { data = Operator(Arithmetic Shr)
                          span = Span.Make (span.first - 1) (span.first) }

                    first, (splitAndMerge (Operator Gt) span input[1..])
                // >> >>=
                | Operator Gt, (Some { data = AssignOp Shr; span = span }) ->
                    let first =
                        { data = Operator(Arithmetic Shr)
                          span = Span.Make (span.first - 1) (span.first) }

                    first, (splitAndMerge (Operator GtEq) span input[1..])
                // >> =>
                | Operator Gt, (Some { data = FatArrow; span = span }) ->
                    let first =
                        { data = Operator GtEq
                          span = Span.Make (span.first - 1) (span.first) }

                    first, (splitAndMerge (Operator Gt) span input[1..])

                // >= =
                | Eq, (Some { data = Eq; span = span }) ->
                    { data = Operator EqEq
                      span = Span.Make (span.first - 1) (span.first) },
                    input[1..]
                // >= >
                | Eq, (Some { data = Operator Gt; span = span }) ->
                    { data = FatArrow
                      span = Span.Make (span.first - 1) (span.first) },
                    input[1..]
                // >= >=
                | Eq, (Some { data = Operator GtEq; span = span }) ->
                    let first =
                        { data = FatArrow
                          span = Span.Make (span.first - 1) (span.first) }

                    first, (splitAndMerge Eq span input[1..])
                // >= >>
                | Eq,
                  (Some { data = Operator(Arithmetic Shr)
                          span = span }) ->
                    let first =
                        { data = FatArrow
                          span = Span.Make (span.first - 1) (span.first) }

                    first, (splitAndMerge (Operator Gt) span input[1..])
                // >= >>=
                | Eq, (Some { data = AssignOp Shr; span = span }) ->
                    let first =
                        { data = FatArrow
                          span = Span.Make (span.first - 1) (span.first) }

                    first, (splitAndMerge (Operator GtEq) span input[1..])
                | _ -> { data = op; span = span }, input

            Array.insertAt 0 first rest
        else
            Array.insertAt 0 { data = op; span = span } input

    match param with
    | Ok(param, gt) ->
        let rest =
            match gt.data with
            | Operator Gt -> param.rest
            | Operator(Arithmetic Shr) -> splitAndMerge (Operator Gt) gt.span param.rest
            | Operator GtEq -> splitAndMerge Eq gt.span param.rest
            | AssignOp Shr -> splitAndMerge (Operator GtEq) gt.span param.rest
            | _ -> failwith "unreachable"

        let span = Span.Make gt.span.first (gt.span.first + 1)

        Ok
            { data = param.data, span
              error = param.error
              rest = rest }
    | Error e -> Error e

let internal parseRangeTo state op tryNext rangeCtor =
    let exclusive =
        match op.data with
        | DotDot -> false
        | DotDotCaret -> true
        | _ -> failwith "unreachable"

    match tryNext state.rest with
    | None ->
        let error =
            if exclusive then
                Array.append state.error [| InclusiveNoEnd op.span |]
            else
                state.error

        Ok
            { data = rangeCtor state.data None exclusive op.span
              error = error
              rest = state.rest }

    | Some(Error e) -> Error e
    | Some(Ok(s: State<_>)) ->
        let error = Array.append state.error s.error

        Ok
            { s with
                data = rangeCtor state.data (Some s.data) exclusive op.span
                error = error }

let internal parseId input msg =
    match peek input with
    | Some({ data = Identifier sym; span = span }, i) ->
        Ok
            { data = { sym = sym; span = span }
              error = [||]
              rest = input[i..] }
    | Some(token, _) -> Error(UnexpectedToken(token, msg))
    | None -> Error(IncompleteAtEnd msg)

let internal parsePath (state: State<PathType>) mapper error =
    let rec parsePath (state: State<PathType>) =
        match parseId state.rest error with
        | Ok id ->
            let newState: State<PathType> =
                { data =
                    { prefix = state.data.prefix
                      seg = Array.append state.data.seg [| id.data |]
                      span = state.data.span.WithLast id.data.span.last }
                  error = Array.append state.error id.error
                  rest = id.rest }

            match peekWith id.rest ColonColon with
            | Some(_, i) ->
                parsePath
                    { newState with
                        rest = newState.rest[i..] }
            | _ -> Ok newState
        | Error e -> state.FatalError e

    match parsePath state with
    | Error e -> Error e
    | Ok s -> mapper s

let rec internal parseType ctx input =
    let normalCtx = { ctx with inTypeInst = false }

    let parseClosure typeParam (input: Token[]) =
        let op = input[0]
        let first = op.span.first

        let param =
            match op.data with
            | Operator(Arithmetic BitOr) ->
                let param =
                    parseCommaSeq
                        input[1..]
                        (parseType normalCtx)
                        (Operator(Arithmetic BitOr))
                        "function type parameter"

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
            match peek param.rest with
            | Some({ data = Arrow }, i) ->
                match parseType normalCtx param.rest[i..] with
                | Ok ret ->
                    let ty =
                        { param = param.data
                          typeParam = typeParam
                          ret = ret.data
                          span = ret.data.span.WithFirst first }

                    Ok
                        { data = FnType ty
                          error = param.error
                          rest = ret.rest }
                | Error e -> Error e
            | Some(token, _) -> Error [| UnexpectedToken(token, "function type") |]
            | None -> Error [| IncompleteAtEnd "function type" |]
        | Error e -> Error e

    let mapPath (s: State<PathType>) =
        let path = s.data

        let data, error =
            if path.prefix = None && path.seg.Length = 1 then
                let ty =
                    if path.seg[0].sym = "_" then
                        InferedType path.seg[0].span
                    else
                        TypeId path.seg[0]

                ty, s.error
            else
                let isCatchAll id = id.sym = "_"
                let toError (id: Id) = InvalidCatchAll id.span
                PathType path, Array.append s.error (Array.filter isCatchAll path.seg |> Array.map toError)

        Ok
            { data = data
              error = error
              rest = s.rest }

    let prefix =
        match peek input with
        | Some({ data = Reserved(PACKAGE | SELF as kw)
                 span = span },
               i) ->
            let prefix, isSelf =
                match kw with
                | PACKAGE -> Package, false
                | SELF -> Self, true
                | _ -> failwith "unreachable"

            let path: State<PathType> =
                { data =
                    { prefix = Some prefix
                      seg = [||]
                      span = span }
                  error = [||]
                  rest = input[i..] }

            match consume path.rest ColonColon "path type" with
            | Error _ ->
                let error =
                    if isSelf then
                        if ctx.inMethod then [||] else [| OutofMethod span |]
                    else
                        [| IncompletePath span |]

                Ok
                    { data = PathType path.data
                      error = error
                      rest = path.rest }
            | Ok(_, i) -> parsePath { path with rest = path.rest[i..] } mapPath "path type"
        | Some({ data = Identifier _; span = span }, _) ->
            parsePath
                { data =
                    { prefix = None
                      seg = [||]
                      span = span }
                  error = [||]
                  rest = input }
                mapPath
                "path type"
        | Some({ data = Operator(Arithmetic Sub)
                 span = span },
               i) ->
            let first = span.first

            match peek input[i..] with
            | Some({ data = Lit(Int _ | Float _ as l)
                     span = span } as token,
                   j) ->

                let l =
                    match l with
                    | Int i -> NegInt i
                    | Float f -> Float -f
                    | _ -> failwith "unreachable"

                Ok
                    { data = LitType(l, span.WithFirst first)
                      error = if ctx.inTypeInst then [||] else [| ConstInType token |]
                      rest = input[i + j ..] }
            | Some(token, _) -> Error [| UnexpectedToken(token, "const generic") |]
            | None -> Error [| IncompleteAtEnd "const generic" |]

        | Some({ data = Lit l; span = span } as token, i) ->
            Ok
                { data = LitType(l, span)
                  error = if ctx.inTypeInst then [||] else [| ConstInType token |]
                  rest = input[i..] }

        | Some({ data = Not; span = span }, i) ->
            Ok
                { data = NeverType span
                  error = [||]
                  rest = input[i..] }

        | Some({ data = Paren Open; span = span }, i) ->
            let ele = parseCommaSeq input[i..] (parseType normalCtx) (Paren Close) "tuple type"

            match ele with
            | Ok(ele, paren) ->
                let ty =
                    if ele.data.Length = 1 then
                        ele.data[0]
                    else
                        TupleType
                            { element = ele.data
                              span = paren.span.WithFirst span.first }

                Ok
                    { data = ty
                      error = ele.error
                      rest = ele.rest }
            | Error e -> Error e

        | Some({ data = Bracket Open; span = span }, i) ->
            let first = span.first
            let ele = parseType normalCtx input[i..]

            match ele with
            | Ok ele ->
                let len =
                    match peek ele.rest with
                    | Some({ data = Delimiter Semi }, i) ->
                        match peek ele.rest[i..] with
                        | Some({ data = Lit(Int v) }, j) -> Ok(Some(v, i + j))

                        | Some(token, _) -> Error(UnexpectedToken(token, "array type length"))
                        | None -> Error(IncompleteAtEnd("array type"))
                    | _ -> Ok None

                match len with
                | Ok len ->
                    let len, i =
                        match len with
                        | Some(i, j) -> Some i, j
                        | None -> None, 0

                    match peek ele.rest[i..] with
                    | Some({ data = Bracket Close; span = span }, j) ->
                        let ty =
                            { ele = ele.data
                              len = len
                              span = span.WithFirst first }

                        Ok
                            { data = ArrayType ty
                              error = ele.error
                              rest = ele.rest[i + j ..] }

                    | Some(token, _) -> ele.FatalError(UnexpectedToken(token, "array type"))
                    | None -> ele.FatalError(IncompleteAtEnd "array type")
                | Error e -> Error [| e |]
            | Error e -> Error e

        | Some({ data = Operator(Lt | Arithmetic Shr) }, i) ->
            let typeParam =
                parseLtGt input[i - 1 ..] (parseTypeParam normalCtx) "closure type parameter"

            match typeParam with
            | Ok param ->
                let data, _ = param.data
                let closure = parseClosure data param.rest

                match closure with
                | Ok c ->
                    Ok
                        { c with
                            error = Array.append param.error c.error }
                | Error e -> param.MergeFatalError e
            | Error e -> Error e

        | Some({ data = Operator(Arithmetic(BitOr | LogicalOr)) }, i) -> parseClosure [||] input[i - 1 ..]

        | Some({ data = Operator(Arithmetic(BitAnd | LogicalAnd as op))
                 span = span },
               i) ->
            match parseType normalCtx input[i..] with
            | Error e -> Error e
            | Ok ty ->
                let expr =
                    match op with
                    | BitAnd ->
                        RefType
                            { ty = ty.data
                              span = ty.data.span.WithFirst span.first }
                    | LogicalAnd ->
                        let span = ty.data.span.WithFirst span.first

                        RefType
                            { ty =
                                RefType
                                    { ty = ty.data
                                      span = span.ShrinkFirst 1 }
                              span = span }
                    | _ -> failwith "unreachable"

                Ok { ty with data = expr }

        | Some(token, _) -> Error [| UnexpectedToken(token, "type") |]
        | None -> Error [| IncompleteAtEnd "type" |]

    let rec parseTypePostfix (state: State<Type>) =
        match peek state.rest with
        | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
            let curr = state.rest[i - 1 ..]

            let param = parseLtGt curr (parseType ctx.InTypeInst) "type instantiation"

            match param with
            | Ok(param) ->
                let data, span = param.data
                let error = Array.append state.error param.error

                let error =
                    if data.Length = 0 then
                        Array.append error [| EmptyTypeInst span |]
                    else
                        error

                let state =
                    { data =
                        TypeInst
                            { ty = state.data
                              arg = data
                              span = span.WithFirst state.data.span.first }
                      error = error
                      rest = param.rest }

                parseTypePostfix state
            | Error e -> Error e
        | _ -> Ok state

    match prefix with
    | Error e -> Error e
    | Ok p -> parseTypePostfix p

and internal parsePat (ctx: Context) input =
    let childCtx = ctx.NotInDecl

    let isRestPat i =
        match i with
        | RestPat _ -> true
        | _ -> false

    let canStartPat i =
        match i with
        | Lit _
        | Identifier _
        | Reserved PACKAGE
        | Reserved SELF
        | Paren Open
        | Bracket Open
        | DotDot -> true
        | _ -> false

    let rec parseRangeTo (from: State<Option<Pat>>) (span: Span) =
        let first =
            match from.data with
            | Some pat -> pat.span.first
            | None -> span.first

        match peek from.rest with
        | Some({ data = data }, _) when canStartPat data ->
            let to_ = parseRangeRec from.rest

            match to_ with
            | Error e -> from.MergeFatalError e
            | Ok(to_: State<Pat>) ->
                Ok
                    { data =
                        RangePat
                            { from = from.data
                              to_ = Some to_.data
                              span = Span.Make first to_.data.span.last }
                      error = to_.error
                      rest = to_.rest }

        | _ ->
            if from.data = None then
                Ok
                    { data = RestPat span
                      error = [||]
                      rest = from.rest }
            else
                Ok
                    { data =
                        RangePat
                            { from = from.data
                              to_ = None
                              span = span.WithFirst first }
                      error = [||]
                      rest = from.rest }

    and parseStructField input =
        match peek input with
        | Some({ data = Identifier sym; span = span }, i) ->
            let id = { sym = sym; span = span }

            match peekWith input[i..] Colon with
            | Some(_, j) ->
                match parsePat childCtx input[i + j ..] with
                | Error e -> Error e
                | Ok(v: State<Pat>) ->
                    Ok
                        { data =
                            KeyValuePat
                                { id = id
                                  pat = v.data
                                  span = v.data.span.WithFirst span.first }
                          error = v.error
                          rest = v.rest }
            | None ->
                Ok
                    { data = ShorthandPat id
                      error = [||]
                      rest = input[i..] }

        | Some({ data = DotDot; span = span }, i) ->
            Ok
                { data = RestFieldPat span
                  error = [||]
                  rest = input[i..] }

        | Some(token, _) -> Error [| UnexpectedToken(token, "struct pattern field") |]
        | None -> Error [| IncompleteAtEnd "struct pattern field" |]

    and parseStruct state =
        let field =
            parseCommaSeq state.rest parseStructField (Curly Close) "struct pattern field"

        match field with
        | Ok(field, paren) ->
            let pat =
                { name = state.data
                  field = field.data
                  span = state.data.span.WithLast paren.span.last }

            let isRest (idx, pat) =
                match pat with
                | RestFieldPat _ when idx <> (Array.length field.data) - 1 -> true
                | _ -> false

            let toError (_, pat: FieldPat) = RestAtStructEnd pat.span

            let restError = Array.indexed field.data |> Array.filter isRest |> Array.map toError

            Ok
                { data = StructPat pat
                  error = Array.concat [ state.error; field.error; restError ]
                  rest = field.rest }
        | Error e -> Error e

    and mapPath (s: State<PathType>) =
        let path = s.data

        let data, error =
            if path.prefix = None && path.seg.Length = 1 then
                let pat =
                    if path.seg[0].sym = "_" then
                        CatchAllPat path.seg[0].span
                    else
                        IdPat path.seg[0]

                pat, s.error
            else
                let isCatchAll id = id.sym = "_"
                let toError (id: Id) = InvalidCatchAll id.span
                PathPat path, Array.append s.error (Array.filter isCatchAll path.seg |> Array.map toError)

        let state =
            { data = data
              error = error
              rest = s.rest }

        match peek state.rest with
        | Some({ data = Paren Open }, i) ->
            let content =
                parseCommaSeq state.rest[i..] (parsePat childCtx) (Paren Close) "enum pattern content"

            match content with
            | Ok(content, paren) ->
                let pat =
                    { name = state.data
                      content = content.data
                      span = state.data.span.WithLast paren.span.last }

                Ok
                    { data = EnumPat pat
                      error = Array.append state.error content.error
                      rest = content.rest }
            | Error e -> Error e

        | Some({ data = Curly Open }, i) ->
            parseStruct
                { data = path
                  error = state.error
                  rest = state.rest[i..] }

        | _ -> Ok state

    and parsePrefix input =
        match peek input with
        | Some({ data = Reserved(LOWSELF)
                 span = span },
               i) ->
            Ok
                { data = SelfPat span
                  error = [||]
                  rest = input[i..] }

        | Some({ data = Reserved(PACKAGE | SELF as kw)
                 span = span },
               i) ->
            let prefix, isSelf =
                match kw with
                | PACKAGE -> Package, false
                | SELF -> Self, true
                | _ -> failwith "unreachable"

            let path: State<PathType> =
                { data =
                    { prefix = Some prefix
                      seg = [||]
                      span = span }
                  error = [||]
                  rest = input[i..] }

            match consume path.rest ColonColon "path pattern" with
            | Ok(_, i) -> parsePath { path with rest = path.rest[i..] } mapPath "path pattern"
            | Error _ ->
                let error =
                    if isSelf then
                        if ctx.inMethod then [||] else [| OutofMethod span |]
                    else
                        [| IncompletePath span |]

                if isSelf then
                    let res =
                        parseStruct
                            { data = path.data
                              error = error
                              rest = path.rest }

                    match res with
                    | Ok({ data = PathPat _ } as res) ->
                        Ok
                            { res with
                                error = Array.append error [| IncompletePath span |] }
                    | _ -> res
                else
                    Ok
                        { data = PathPat path.data
                          error = error
                          rest = path.rest }

        | Some({ data = Identifier _; span = span }, _) ->
            parsePath
                { data =
                    { prefix = None
                      seg = [||]
                      span = span }
                  error = [||]
                  rest = input }
                mapPath
                "path pattern"

        | Some({ data = Operator(Arithmetic Sub)
                 span = span },
               i) ->
            let first = span.first

            match peek input[i..] with
            | Some({ data = Lit(Int _ | Float _ as l)
                     span = span },
                   j) ->

                let l =
                    match l with
                    | Int i -> NegInt i
                    | Float f -> Float -f
                    | _ -> failwith "unreachable"

                Ok
                    { data = LitPat(l, span.WithFirst first)
                      error = [||]
                      rest = input[i + j ..] }
            | Some(token, _) -> Error [| UnexpectedToken(token, "literal pattern") |]
            | None -> Error [| IncompleteAtEnd "literal pattern" |]

        | Some({ data = Lit l; span = span }, i) ->
            Ok
                { data = LitPat(l, span)
                  error = [||]
                  rest = input[i..] }

        | Some({ data = DotDot; span = span }, i) ->
            parseRangeTo
                { data = None
                  error = [||]
                  rest = input[i..] }
                span

        | Some({ data = Paren Open; span = span }, i) ->
            let ele = parseCommaSeq input[i..] (parsePat childCtx) (Paren Close) "tuple pattern"

            match ele with
            | Ok(ele, paren) ->
                let pat, error =
                    if ele.data.Length = 1 then
                        ele.data[0], ele.error
                    else
                        let span = paren.span.WithFirst span.first

                        let error =
                            if (Array.filter isRestPat ele.data).Length > 1 then
                                Array.append ele.error [| TooManyRestPat span |]
                            else
                                ele.error

                        TuplePat { element = ele.data; span = span }, error

                Ok
                    { data = pat
                      error = error
                      rest = ele.rest }
            | Error e -> Error e

        | Some({ data = Bracket Open; span = span }, i) ->
            let ele =
                parseCommaSeq input[i..] (parsePat childCtx) (Bracket Close) "array pattern"

            match ele with
            | Ok(ele, bracket) ->
                let span = bracket.span.WithFirst span.first
                let pat = ArrayPat { element = ele.data; span = span }

                let error =
                    if (Array.filter isRestPat ele.data).Length > 1 then
                        Array.append ele.error [| TooManyRestPat span |]
                    else
                        ele.error

                Ok
                    { data = pat
                      error = error
                      rest = ele.rest }
            | Error e -> Error e

        | Some(token, _) -> Error [| UnexpectedToken(token, "pattern") |]
        | None -> Error [| IncompleteAtEnd "pattern" |]

    and parseRange state =
        match peek state.rest with
        | Some({ data = DotDot; span = span }, i) ->
            let res =
                parseRangeTo
                    { data = Some state.data
                      error = state.error
                      rest = state.rest[i..] }
                    span

            res
        | _ -> Ok state

    and parseRangeRec input =
        match parsePrefix input with
        | Error e -> Error e
        | Ok s -> parseRange s

    and parseAs state =
        match peek state.rest with
        | Some({ data = Operator As }, i) ->
            match peek state.rest[i..] with
            | Some({ data = Identifier sym; span = span }, j) ->
                let id = { sym = sym; span = span }

                let newState =
                    { data =
                        AsPat
                            { pat = state.data
                              id = id
                              span = span.WithFirst state.data.span.first }
                      error = state.error
                      rest = state.rest[i + j ..] }

                parseAs newState
            | Some(token, _) -> state.FatalError(UnexpectedToken(token, "as pattern"))
            | None -> state.FatalError(IncompleteAtEnd "as pattern")
        | _ -> Ok state

    and parseOr (state: State<Pat>) =
        let rec parseOr (state: State<Pat[]>) =
            match peek state.rest with
            | Some({ data = Operator(Arithmetic BitOr) }, i) ->
                match parseRecursive state.rest[i..] with
                | Ok(newState: State<_>) ->
                    Ok
                        { data = Array.append state.data [| newState.data |]
                          error = Array.append state.error newState.error
                          rest = newState.rest }
                | Error e -> state.MergeFatalError e
            | _ -> Ok state

        let res =
            parseOr
                { data = [| state.data |]
                  error = state.error
                  rest = state.rest }

        match res with
        | Error e -> state.MergeFatalError e
        | Ok s ->
            let pat = s.data

            let data =
                if pat.Length = 1 then
                    pat[0]
                else
                    OrPat
                        { pat = pat
                          span = Span.Make pat[0].span.first (Array.last pat).span.last }

            Ok
                { data = data

                  error = s.error
                  rest = s.rest }

    and parseRecursive input =
        match parseRangeRec input with
        | Error e -> Error e
        | Ok o ->
            match parseAs o with
            | Error e -> Error e
            | Ok o -> if ctx.inDecl then Ok o else parseOr o

    parseRecursive input

and internal parseParam (ctx: Context) input =
    match parsePat ctx.InDecl input with
    | Error e -> Error e
    | Ok p ->
        match peek p.rest with
        | Some({ data = Colon }, i) ->
            match peek p.rest[i..] with
            | None -> p.FatalError(IncompleteAtEnd("type annotation"))
            | _ ->
                match parseType ctx p.rest[i..] with
                | Error e -> p.MergeFatalError e
                | Ok ty ->
                    let param =
                        { pat = p.data
                          ty = Some ty.data
                          span = ty.data.span.WithFirst p.data.span.first }

                    Ok
                        { data = param
                          error = Array.append p.error ty.error
                          rest = ty.rest }
        | _ ->
            Ok
                { data =
                    { pat = p.data
                      ty = None
                      span = p.data.span }
                  error = p.error
                  rest = p.rest }

and internal parseTypeParam ctx input =
    match peek input with
    | Some({ data = Reserved CONST; span = span }, i) ->
        let input = input[i..]

        match parseId input "type parameter" with
        | Ok id ->
            match peek id.rest with
            | Some({ data = Colon }, i) ->
                match parseType { ctx with inTypeInst = false } id.rest[i..] with
                | Ok ty ->
                    let param =
                        { id = id.data
                          const_ = true
                          bound = Some ty.data
                          span = ty.data.span.WithFirst span.first }

                    Ok
                        { data = param
                          error = Array.append id.error ty.error
                          rest = ty.rest }
                | Error e -> Error e
            | _ ->
                Ok
                    { data =
                        { id = id.data
                          const_ = true
                          bound = None
                          span = id.data.span.WithFirst span.first }
                      error = id.error
                      rest = id.rest }
        | Error e -> Error [| e |]
    | Some({ data = Identifier sym; span = span }, i) ->
        let id = { sym = sym; span = span }

        match peek input[i..] with
        | Some({ data = Colon }, j) ->
            match parseType { ctx with inTypeInst = false } input[i + j ..] with
            | Ok ty ->
                let param =
                    { id = id
                      const_ = false
                      bound = Some ty.data
                      span = ty.data.span.WithFirst span.first }

                Ok
                    { data = param
                      error = ty.error
                      rest = ty.rest }
            | Error e -> Error e
        | _ ->
            Ok
                { data =
                    { id = id
                      const_ = false
                      bound = None
                      span = id.span }
                  error = [||]
                  rest = input[i..] }

    | Some(token, _) -> Error [| UnexpectedToken(token, "type parameter") |]
    | None -> Error [| IncompleteAtEnd "type parameter" |]

let internal isValidLValue expr =
    match expr with
    | Id _
    | Field _
    | Unary { op = Deref } -> true
    | _ -> false

let internal canStartExpr token =
    match token with
    | Lit _
    | Identifier _
    | Paren Open
    | Bracket Open
    | Curly Open
    | Operator(Arithmetic Sub | Arithmetic Mul | Arithmetic BitAnd | Arithmetic BitOr | Arithmetic LogicalOr | Gt)
    | Reserved(PACKAGE | SELF | IF | MATCH | FOR | WHILE | RETURN | BREAK | CONTINUE)
    | DotDot
    | DotDotCaret -> true
    | _ -> false

let internal canStartDecl token =
    match token with
    | Reserved(FUNCTION | LET | CONST | USE | IMPL | TRAIT | TYPE | ENUM | STRUCT) -> true
    | _ -> false

let internal parseManyItem (input: Token[]) parser delimiter =
    let skipLimiter (input: Token[]) =
        let rec skip i cnt =
            if i = input.Length then
                i, cnt
            else
                match input[i].data with
                | Comment _ -> skip (i + 1) cnt
                | Delimiter _ -> skip (i + 1) (cnt + 1)
                | t when delimiter t -> i, cnt + 1
                | _ -> i, cnt

        skip 0 0

    let rec skipUntil (input: Token[]) =
        match peekInline input with
        | Some({ data = Delimiter _ }, i) -> input[i..]
        | Some(_, i) -> skipUntil input[i..]
        | None -> [||]

    let i, _ = skipLimiter input

    let state =
        { data = [||]
          error = [||]
          rest = input[i..] }

    let rec parseMany state =
        match Array.tryHead state.rest with
        | None -> Ok(state, None)
        | Some token when delimiter token.data -> Ok({ state with rest = state.rest[1..] }, Some token)
        | Some _ ->
            match parser state.rest with
            | Error e ->
                let data = state.data
                let rest = skipUntil state.rest
                let error = Array.append state.error e

                parseMany
                    { data = data
                      error = error
                      rest = rest }
            | Ok(item: State<_>) ->
                let i, cnt = skipLimiter item.rest

                let error = Array.append state.error item.error

                let error =
                    if cnt = 0 then
                        Array.append error [| NeedDelimiter item.rest[i].span |]
                    else
                        error

                let newState =
                    { data = Array.append state.data [| item.data |]
                      error = error
                      rest = item.rest[i..] }

                parseMany newState

    parseMany state

let rec internal parseExpr (ctx: Context) input =
    let parseStructField input =
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

    let parseStruct (state: State<Path>) =
        let ret =
            { data = Path state.data
              error = state.error
              rest = state.rest }

        if ctx.inCond then
            Ok ret
        else
            match peekInline state.rest with
            | Some({ data = Curly Open }, i) ->
                let field =
                    parseCommaSeq state.rest[i..] parseStructField (Curly Close) "struct pattern field"

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
            | _ -> Ok ret

    let parsePath (state: State<Path>) =
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

            let res =
                parseStruct
                    { data = s.data
                      error = state.error
                      rest = s.rest }

            match res with
            | Ok { data = Path _ } -> Ok state
            | r -> r

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

    let rec rangeParser ctx input =
        match peek input with
        | None -> None
        | Some({ data = data }, _) when canStartExpr data -> Some(parseWithPrec ctx -1 input)
        | Some(_, _) -> None

    and parseClosure typeParam (input: Token[]) =
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

    and parseCond (ctx: Context) input =
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

    and parseMatchBranch state =
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
                                  result = res.data
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
                                    { newState with
                                        rest = newState.rest[i..] }
                            | _ ->
                                match peek res.rest with
                                | Some({ data = Curly Close }, _) -> parseMatchBranch newState
                                | Some({ data = Comma }, i) ->
                                    parseMatchBranch
                                        { newState with
                                            rest = newState.rest[i..] }

                                | Some(token, _) -> newState.FatalError(UnexpectedToken(token, "match branch"))
                                | None -> newState.FatalError(IncompleteAtEnd "match branch")

    and parsePrefix ctx input =
        match peek input with
        | Some({ data = Lit l; span = span }, i) ->
            Ok
                { data = LitExpr(l, span)
                  error = [||]
                  rest = input[i..] }
        | Some({ data = Reserved SELF; span = span }, i) ->
            let path =
                { prefix = Some Self
                  seg = [||]
                  span = span }

            let path =
                { data = path
                  error = [||]
                  rest = input[i..] }

            match parseStruct path with
            | Error e -> Error e
            | Ok({ data = Path _ } as o) ->
                Ok
                    { o with
                        error = Array.append o.error [| IncompletePath span |] }
            | Ok o -> Ok o
        | Some({ data = Reserved(PACKAGE | LOWSELF as kw)
                 span = span },
               i) ->
            let prefix, isSelf =
                match kw with
                | PACKAGE -> Package, false
                | LOWSELF -> Self, true
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
            | Some(_, i) -> parsePath { path with rest = path.rest[i..] }
            | None ->
                let error =
                    if isSelf then
                        if ctx.inMethod then [||] else [| OutofMethod span |]
                    else
                        [| IncompletePath span |]

                if isSelf then
                    Ok
                        { data = SelfExpr span
                          error = Array.append error [| IncompletePath span |]
                          rest = input[i..] }
                else
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

            parsePath newState

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
                let closure = parseClosure data param.rest

                match closure with
                | Ok c ->
                    Ok
                        { c with
                            error = Array.append param.error c.error }
                | Error e -> param.MergeFatalError e
            | Error e -> Error e

        | Some({ data = Operator(Arithmetic(BitOr | LogicalOr)) }, i) -> parseClosure [||] input[i - 1 ..]

        | Some({ data = Operator(Arithmetic Sub | Arithmetic Mul | Arithmetic BitAnd as op)
                 span = span },
               i) ->
            let op =
                match op with
                | Arithmetic Sub -> Neg
                | Arithmetic Mul -> Deref
                | Arithmetic BitAnd -> Ref
                | _ -> failwith "unreachable"

            match parseWithPrec ctx 1000 input[i..] with
            | Error e -> Error e
            | Ok(state: State<Expr>) ->
                let expr =
                    { op = op
                      expr = state.data
                      span = Span.Make span.first state.data.span.last }

                Ok { state with data = Unary expr }

        | Some({ data = Not; span = span }, i) ->
            match parseWithPrec ctx 1000 input[i..] with
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
            match parseWithPrec ctx 1000 input[i..] with
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
                                      value = body.data
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

                    match parseMatchBranch state with
                    | Error e -> value.MergeFatalError e
                    | Ok(branch, last) ->
                        let expr =
                            { value = value.data
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

    and parseFollow ctx prec (state: State<Expr>) =
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
                    if isValidLValue assignee then
                        state.error
                    else
                        Array.append state.error [| InvalidLValue assignee |]

                match parseWithPrec ctx -2 state.rest[i..] with
                | Error e -> Error e
                | Ok right ->
                    let expr =
                        { assignee = state.data
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
                match parseWithPrec ctx op.precedence state.rest[i..] with
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

    and parsePostfix ctx prec state =
        match peekInline state.rest with
        | Some({ data = Dot }, i) ->
            match peek state.rest[i..] with
            | None -> state.FatalError(Incomplete(state.data.span, "field access expression"))
            | Some({ data = Identifier id; span = span }, j) ->
                let expr =
                    { receiver = state.data
                      prop = id
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

    and parseRecursive ctx prec state =
        match parseFollow ctx prec state with
        | Error e -> Error e
        | Ok newState ->
            match peek newState.rest with
            | Some({ data = Operator op }, _) when prec < op.precedence -> parseRecursive ctx prec newState
            | Some({ data = DotDot | DotDotCaret }, _) when prec <= -1 -> parseRecursive ctx prec newState
            | Some({ data = AssignOp _ | Eq }, _) when prec <= -2 -> parseRecursive ctx prec newState
            | _ -> Ok newState

    and parseWithPrec ctx prec input =
        match parsePrefix ctx input with
        | Error e -> Error e
        | Ok state -> parseRecursive ctx prec state

    parseWithPrec ctx -100 input

and internal parseDecl (ctx: Context) input =
    match peek input with
    | Some({ data = Reserved FUNCTION
             span = span },
           i) ->
        match parseId input[i..] "function name" with
        | Error e -> Error [| e |]
        | Ok id ->
            let typeParam =
                match peek id.rest with
                | Some({ data = Operator(Lt | Arithmetic Shl) }, _) ->
                    parseLtGt id.rest (parseTypeParam ctx) "function type paramater"
                | _ ->
                    Ok
                        { data = [||], Span.dummy
                          error = [||]
                          rest = id.rest }

            match typeParam with
            | Error e -> Error e
            | Ok typeParam ->
                match consume typeParam.rest (Paren Open) "function parameter" with
                | Error e -> Error [| e |]
                | Ok(_, i) ->
                    match parseCommaSeq typeParam.rest[i..] (parseParam ctx) (Paren Close) "function parameter" with
                    | Error e -> id.MergeFatalError e
                    | Ok(param, _) ->
                        let error = Array.append typeParam.error param.error
                        let typeParam, _ = typeParam.data

                        let retTy =
                            match peekWith param.rest Arrow with
                            | Some(_, i) ->
                                match parseType ctx param.rest[i..] with
                                | Error e -> Error(Array.append error e)
                                | Ok s ->
                                    Ok
                                        { data = Some s.data
                                          error = Array.append error s.error
                                          rest = s.rest }
                            | _ ->
                                Ok
                                    { data = None
                                      error = error
                                      rest = param.rest }

                        match retTy with
                        | Error e -> Error e
                        | Ok retTy ->
                            match parseBlock Context.InFn retTy.rest with
                            | Error e -> Error(Array.append retTy.error e)
                            | Ok block ->
                                let fn =
                                    { name = id.data
                                      typeParam = typeParam
                                      retTy = retTy.data
                                      param = param.data
                                      body = block.data
                                      span = span }

                                Ok
                                    { data = FnDecl fn
                                      error = Array.append retTy.error block.error
                                      rest = block.rest }

    | Some({ data = Reserved LET; span = span }, i) ->
        let mut, i =
            match peek input[i..] with
            | Some({ data = Reserved MUTABLE }, j) -> true, i + j
            | _ -> false, i

        match parseParam ctx.InDecl input[i..] with
        | Error e -> Error e
        | Ok param ->
            match consume param.rest Eq "let declaration" with
            | Ok(_, i) ->
                match parseExpr ctx param.rest[i..] with
                | Error e -> Error e
                | Ok value ->
                    let decl =
                        { pat = param.data.pat
                          ty = param.data.ty
                          mut = mut
                          value = value.data
                          span = span.WithLast value.data.span.last }

                    Ok
                        { data = Let decl
                          error = Array.append param.error value.error
                          rest = value.rest }
            | Error e -> param.FatalError e

    | Some({ data = Reserved CONST; span = span }, i) ->
        match parseParam ctx.InDecl input[i..] with
        | Error e -> Error e
        | Ok param ->
            match consume param.rest Eq "const declaration" with
            | Ok(_, i) ->
                match parseExpr ctx param.rest[i..] with
                | Error e -> Error e
                | Ok value ->
                    let decl =
                        { pat = param.data.pat
                          ty = param.data.ty
                          value = value.data
                          span = span.WithLast value.data.span.last }

                    Ok
                        { data = Const decl
                          error = Array.append param.error value.error
                          rest = value.rest }

            | Error e -> param.FatalError e

    | Some({ data = Reserved USE }, i) ->
        match peek input[i..] with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | _ -> Error [| UnexpectedToken(input[i], "identifier") |]

    | Some({ data = Reserved TYPE; span = span }, i) ->
        match parseId input[i..] "type alias name" with
        | Error e -> Error [| e |]
        | Ok id ->
            match consume id.rest Eq "type alias" with
            | Ok(_, i) ->
                match parseType ctx id.rest[i..] with
                | Error e -> Error e
                | Ok ty ->
                    let decl =
                        { name = id.data
                          ty = ty.data
                          span = span.WithLast ty.data.span.last }

                    Ok
                        { data = TypeDecl decl
                          error = Array.append id.error ty.error
                          rest = ty.rest }

            | Error e -> id.FatalError e

    | Some({ data = Reserved STRUCT; span = span }, i) ->
        let parseStructField input =
            let vis, visSpan, i =
                match peek input with
                | Some({ data = Reserved PUBLIC } as token, i) -> Public, Some token, i
                | Some({ data = Reserved INTERNAL } as token, i) -> Internal, Some token, i
                | _ -> Private, None, 0

            match parseId input[i..] "struct field name" with
            | Error e -> Error [| e |]
            | Ok id ->
                match consume id.rest Colon "struct field delimiter" with
                | Error e -> id.FatalError e
                | Ok(_, i) ->
                    match parseType ctx id.rest[i..] with
                    | Error e -> id.MergeFatalError e
                    | Ok ty ->
                        let data =
                            { vis = vis
                              name = id.data
                              ty = ty.data
                              span = id.data.span }

                        let error = Array.append id.error ty.error

                        let error =
                            match visSpan with
                            | Some token when not ctx.mayHaveVis -> Array.append error [| VisibilityNotAllowed token |]
                            | _ -> error

                        Ok
                            { data = data
                              error = error
                              rest = ty.rest }

        match parseId input[i..] "struct name" with
        | Error e -> Error [| e |]
        | Ok id ->
            match peek id.rest with
            | None -> id.FatalError(IncompleteAtEnd "struct")
            | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
                let tyParam =
                    parseLtGt id.rest[i - 1 ..] (parseTypeParam ctx) "struct type parameter"

                match tyParam with
                | Error e -> Error e
                | Ok ty ->
                    match consume ty.rest (Curly Open) "struct fields" with
                    | Error e -> Error(Array.concat [ id.error; ty.error; [| e |] ])
                    | Ok(_, i) ->
                        match parseCommaSeq ty.rest[i..] parseStructField (Curly Close) "struct fields" with
                        | Error e -> ty.MergeFatalError e
                        | Ok(fields, curly) ->
                            let span = span.WithLast curly.span.last

                            let data =
                                { name = id.data
                                  tyParam = fst ty.data
                                  field = fields.data
                                  span = span }

                            let error = Array.concat [ id.error; ty.error; fields.error ]

                            Ok
                                { data = StructDecl data
                                  error = error
                                  rest = fields.rest }
            | Some({ data = Curly Open }, i) ->
                match parseCommaSeq id.rest[i..] parseStructField (Curly Close) "struct fields" with
                | Error e -> id.MergeFatalError e
                | Ok(fields, curly) ->
                    let span = span.WithLast curly.span.last

                    let data =
                        { name = id.data
                          tyParam = [||]
                          field = fields.data
                          span = span }

                    let error = Array.append id.error fields.error

                    Ok
                        { data = StructDecl data
                          error = error
                          rest = fields.rest }
            | Some(token, _) -> id.FatalError(UnexpectedToken(token, "struct definition"))

    | Some({ data = Reserved ENUM; span = span }, i) ->
        let parseEnumVariant input =
            match parseId input "enum variant name" with
            | Error e -> Error [| e |]
            | Ok id ->
                match peek id.rest with
                | Some({ data = Paren Open; span = parenSpan }, i) ->
                    match parseCommaSeq id.rest[i..] (parseType ctx) (Paren Close) "enum variant payload" with
                    | Error e -> id.MergeFatalError e
                    | Ok(ty, _) ->
                        let data =
                            { name = id.data
                              payload = ty.data
                              span = id.data.span }

                        let error = Array.append id.error ty.error

                        Ok
                            { data = data
                              error = error
                              rest = ty.rest }
                | _ ->
                    let data =
                        { name = id.data
                          payload = [||]
                          span = id.data.span }

                    Ok
                        { data = data
                          error = id.error
                          rest = id.rest }

        match parseId input[i..] "enum name" with
        | Error e -> Error [| e |]
        | Ok id ->
            match peek id.rest with
            | None -> id.FatalError(IncompleteAtEnd "enum")
            | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
                let tyParam = parseLtGt id.rest[i - 1 ..] (parseTypeParam ctx) "enum type parameter"

                match tyParam with
                | Error e -> Error e
                | Ok ty ->
                    match consume ty.rest (Curly Open) "enum variants" with
                    | Error e -> Error(Array.concat [ id.error; ty.error; [| e |] ])
                    | Ok(_, i) ->
                        match parseCommaSeq ty.rest[i..] parseEnumVariant (Curly Close) "enum variants" with
                        | Error e -> ty.MergeFatalError e
                        | Ok(variants, curly) ->
                            let span = span.WithLast curly.span.last

                            let data =
                                { name = id.data
                                  tyParam = fst ty.data
                                  variant = variants.data
                                  span = span }

                            let error = Array.concat [ id.error; ty.error; variants.error ]

                            let error =
                                if variants.data.Length = 0 then
                                    Array.append error [| EmptyEnum span |]
                                else
                                    error

                            Ok
                                { data = EnumDecl data
                                  error = error
                                  rest = variants.rest }
            | Some({ data = Curly Open }, i) ->
                match parseCommaSeq id.rest[i..] parseEnumVariant (Curly Close) "enum variants" with
                | Error e -> id.MergeFatalError e
                | Ok(variants, curly) ->
                    let span = span.WithLast curly.span.last

                    let data =
                        { name = id.data
                          tyParam = [||]
                          variant = variants.data
                          span = span }

                    let error = Array.append id.error variants.error

                    let error =
                        if variants.data.Length = 0 then
                            Array.append error [| EmptyEnum span |]
                        else
                            error

                    Ok
                        { data = EnumDecl data
                          error = error
                          rest = variants.rest }
            | Some(token, _) -> id.FatalError(UnexpectedToken(token, "struct definition"))

    | Some({ data = Reserved IMPL }, i) ->
        match parseId input[i..] "implementation name" with
        | Error e -> Error [| e |]
        | Ok id -> failwith "123"

    | Some({ data = Reserved TRAIT }, i) ->
        match parseId input[i..] "trait name" with
        | Error e -> Error [| e |]
        | Ok id -> failwith "123"

    | Some(token, _) -> Error [| UnexpectedToken(token, "declaration") |]
    | None -> Error [| IncompleteAtEnd("declaration") |]

and internal parseStmt ctx (input: Token[]) =
    if canStartExpr input[0].data then
        match parseExpr ctx input with
        | Error e -> Error e
        | Ok s ->
            Ok
                { data = ExprStmt s.data
                  error = s.error
                  rest = s.rest }
    else if canStartDecl input[0].data then
        match parseDecl ctx input with
        | Error e -> Error e
        | Ok s ->
            Ok
                { data = DeclStmt s.data
                  error = s.error
                  rest = s.rest }
    else
        Error [| UnexpectedToken(input[0], "statement") |]

and internal parseBlock ctx input =
    let ctx = ctx.NotInCond

    match consume input (Curly Open) "block expression" with
    | Ok(span, i) ->
        let item = parseManyItem input[i..] (parseStmt ctx) ((=) (Curly Close))

        match item with
        | Error e -> Error e
        | Ok(item, curly) ->
            match curly with
            | None -> Error [| IncompleteAtEnd "block expression" |]
            | Some token ->
                let span = span.WithLast token.span.last

                Ok
                    { data = { stmt = item.data; span = span }
                      error = item.error
                      rest = item.rest }

    | Error e -> Error [| e |]

let rec internal parseModuleItem (input: Lexer.Token[]) =
    let vis, visSpan, i =
        match peek input with
        | Some({ data = Reserved PUBLIC; span = span }, i) -> Public, Some span, i
        | Some({ data = Reserved INTERNAL
                 span = span },
               i) -> Internal, Some span, i
        | _ -> Private, None, 0

    let ctx =
        { Context.Normal with
            mayHaveVis = vis <> Private }

    let stmt = parseStmt ctx input[i..]

    match stmt with
    | Error e -> Error e
    | Ok s ->
        match s.data with
        | DeclStmt d ->
            let first =
                match visSpan with
                | Some s -> s.first
                | None -> d.span.first

            let item =
                { vis = vis
                  decl = d
                  span = d.span.WithFirst first }

            Ok
                { data = item
                  error = s.error
                  rest = s.rest }
        | ExprStmt e ->
            let error = Array.append s.error [| TopLevelExpr e.span |]

            match parseModuleItem s.rest with
            | Ok m ->
                Ok
                    { m with
                        error = Array.append error m.error }
            | Error e -> Error(Array.append error e)

/// A hand written recursive descent parser produces AST without paren
///
/// There should be a CST somewhere, but at the time it's omitted
let parse (input: Lexer.Token[]) =
    match parseManyItem input parseModuleItem (fun _ -> false) with
    | Ok(state, _) ->
        if state.error.Length = 0 then
            Ok state.data
        else
            Error(state.error, Some state.data)
    | Error e -> Error(e, None)
