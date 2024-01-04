module Parser.Common

open Common.Span
open AST.AST
open Lexer

type Error =
    | UnexpectedToken of Token * string
    | UnexpectedManyToken of Span * string
    | Incomplete of Span * string
    | IncompleteAtEnd of string
    | IncompletePair of Token
    | IncompletePath of Span
    | InvalidLValue of Expr
    | OutOfLoop of Token
    | OutOfFn of Span
    | OutofMethod of Span
    | ConstInType of Token
    | EmptyEnum of Span
    | EmptyTypeInst of Span
    | TooManyRestPat of Span
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
    | LexerError of Lexer.Error

type internal Context =
    { inLoop: bool
      inFn: bool
      inCond: bool
      mayHaveVis: bool
      inMethod: bool
      inTrait: bool
      inImpl: bool
      inDecl: bool
      inTypeInst: bool }

    static member Normal =
        { inLoop = false
          inFn = false
          inCond = false
          inTrait = false
          inImpl = false
          mayHaveVis = true
          inMethod = false
          inDecl = false
          inTypeInst = false }

    static member InFn =
        { inLoop = false
          inFn = true
          inCond = false
          mayHaveVis = false
          inTrait = false
          inImpl = false
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
        rest: Token[]
    }

    member this.FatalError e = Error(Array.append this.error [| e |])

    member this.MergeFatalError other = Error(Array.append this.error other)

let internal peek (input: Token[]) =
    let rec peek i =
        if i = input.Length then
            None
        else
            match input[i].Data with
            | Comment _
            | Delimiter CR
            | Delimiter LF -> peek (i + 1)
            | _ -> Some(input[i], i + 1)

    peek 0

let internal peekInline (input: Token[]) =
    let rec peek i =
        if i = input.Length then
            None
        else
            match input[i].Data with
            | Comment _ -> peek (i + 1)
            | _ -> Some(input[i], i + 1)

    peek 0

let internal peekWith input token =
    match peek input with
    | Some({ Data = data; Span = span }, i) when data = token -> Some(span, i)
    | _ -> None

let internal consume input token error =
    match peek input with
    | Some({ Data = data; Span = span }, i) when data = token -> Ok(span, i)
    | Some(token, _) -> Error(UnexpectedToken(token, error))
    | None -> Error(IncompleteAtEnd(error))

let internal tryRecover canStart parser msg (input: Token[]) =
    let rec tryRecover i unexpected =
        match peek input[i..] with
        | Some({ Data = Delimiter Semi }, i) -> Error(i - 1)
        | Some({ Data = data } as token, j) ->
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
                                Span.Make unexpected[0].Span.First (Array.last unexpected).Span.Last,
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

let internal parseCommaSeq (input: Token[]) parser limiter error =
    let limiter =
        if limiter = Operator(Cmp Gt) then
            fun t ->
                match t with
                | Operator(Cmp Gt)
                | Operator(Cmp GtEq)
                | Operator(Arith Shr)
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
        | Some(token, i) when limiter token.Data -> Ok({ state with rest = state.rest[i..] }, token)
        | _ ->
            match parser state.rest with
            | Error e -> state.MergeFatalError e
            | Ok(newState: State<_>) ->
                let newState =
                    { data = Array.append state.data [| newState.data |]
                      error = Array.append state.error newState.error
                      rest = newState.rest }

                match peek newState.rest with
                | Some({ Data = Comma }, i) ->
                    parseRecursive (
                        { newState with
                            rest = newState.rest[i..] }
                    )
                | Some(token, i) when limiter token.Data ->
                    Ok(
                        { newState with
                            rest = newState.rest[i..] },
                        token
                    )
                | Some(_, i) ->
                    parseRecursive
                        { newState with
                            error = Array.append newState.error [| NeedDelimiter newState.rest[i - 1].Span |] }
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
        match input[0].Data with
        | Operator(Cmp Lt) -> input[1..]
        | Operator(Arith Shl) ->
            Array.set
                input
                0
                { Data = Operator(Cmp Lt)
                  Span = input[0].Span.ShrinkFirst 1 }

            input
        | _ -> failwith "unreachable"

    let param = parseCommaSeq rest parser (Operator(Cmp Gt)) error

    let rec splitAndMerge op (span: Span) (input: Token[]) =
        let canMerge =
            match op with
            | Operator(Cmp Gt)
            | Eq -> true
            | Operator(Cmp GtEq) -> false
            | _ -> failwith "unreachable"

        let span = span.ShrinkFirst 1

        if canMerge then
            let first, rest =
                let follow =
                    match Array.tryHead input with
                    | Some token when token.Span.First - 1 = span.Last -> Some token
                    | Some _ -> None
                    | None -> None

                match op, follow with
                // >> >
                | Operator(Cmp Gt), (Some { Data = Operator(Cmp Gt); Span = span }) ->
                    { Data = Operator(Arith Shr)
                      Span = Span.Make (span.First - 1) (span.First) },
                    input[1..]
                // >> =
                | Operator(Cmp Gt), (Some { Data = Eq; Span = span }) ->

                    { Data = Operator(Cmp GtEq)
                      Span = Span.Make (span.First - 1) (span.First) },
                    input[1..]
                // >> >=
                | Operator(Cmp Gt),
                  (Some { Data = Operator(Cmp GtEq)
                          Span = span }) ->
                    { Data = AssignOp Shr
                      Span = Span.Make (span.First - 1) (span.First) },
                    input[1..]
                // >> >>
                | Operator(Cmp Gt),
                  (Some { Data = Operator(Arith Shr)
                          Span = span }) ->
                    let first =
                        { Data = Operator(Arith Shr)
                          Span = Span.Make (span.First - 1) (span.First) }

                    first, (splitAndMerge (Operator(Cmp Gt)) span input[1..])
                // >> >>=
                | Operator(Cmp Gt), (Some { Data = AssignOp Shr; Span = span }) ->
                    let first =
                        { Data = Operator(Arith Shr)
                          Span = Span.Make (span.First - 1) (span.First) }

                    first, (splitAndMerge (Operator(Cmp GtEq)) span input[1..])
                // >> =>
                | Operator(Cmp Gt), (Some { Data = FatArrow; Span = span }) ->
                    let first =
                        { Data = Operator(Cmp GtEq)
                          Span = Span.Make (span.First - 1) (span.First) }

                    first, (splitAndMerge (Operator(Cmp Gt)) span input[1..])

                // >= =
                | Eq, (Some { Data = Eq; Span = span }) ->
                    { Data = Operator(Cmp EqEq)
                      Span = Span.Make (span.First - 1) (span.First) },
                    input[1..]
                // >= >
                | Eq, (Some { Data = Operator(Cmp Gt); Span = span }) ->
                    { Data = FatArrow
                      Span = Span.Make (span.First - 1) (span.First) },
                    input[1..]
                // >= >=
                | Eq,
                  (Some { Data = Operator(Cmp GtEq)
                          Span = span }) ->
                    let first =
                        { Data = FatArrow
                          Span = Span.Make (span.First - 1) (span.First) }

                    first, (splitAndMerge Eq span input[1..])
                // >= >>
                | Eq,
                  (Some { Data = Operator(Arith Shr)
                          Span = span }) ->
                    let first =
                        { Data = FatArrow
                          Span = Span.Make (span.First - 1) (span.First) }

                    first, (splitAndMerge (Operator(Cmp Gt)) span input[1..])
                // >= >>=
                | Eq, (Some { Data = AssignOp Shr; Span = span }) ->
                    let first =
                        { Data = FatArrow
                          Span = Span.Make (span.First - 1) (span.First) }

                    first, (splitAndMerge (Operator(Cmp GtEq)) span input[1..])
                | _ -> { Data = op; Span = span }, input

            Array.insertAt 0 first rest
        else
            Array.insertAt 0 { Data = op; Span = span } input

    match param with
    | Ok(param, gt) ->
        let rest =
            match gt.Data with
            | Operator(Cmp Gt) -> param.rest
            | Operator(Arith Shr) -> splitAndMerge (Operator(Cmp Gt)) gt.Span param.rest
            | Operator(Cmp GtEq) -> splitAndMerge Eq gt.Span param.rest
            | AssignOp Shr -> splitAndMerge (Operator(Cmp GtEq)) gt.Span param.rest
            | _ -> failwith "unreachable"

        let span = Span.Make gt.Span.First (gt.Span.First + 1)

        Ok
            { data = param.data, span
              error = param.error
              rest = rest }
    | Error e -> Error e

let internal parseRangeTo state (op: Token) tryNext rangeCtor =
    let exclusive =
        match op.Data with
        | DotDot -> false
        | DotDotCaret -> true
        | _ -> failwith "unreachable"

    match tryNext state.rest with
    | None ->
        let error =
            if exclusive then
                Array.append state.error [| InclusiveNoEnd op.Span |]
            else
                state.error

        Ok
            { data = rangeCtor state.data None exclusive op.Span
              error = error
              rest = state.rest }

    | Some(Error e) -> Error e
    | Some(Ok(s: State<_>)) ->
        let error = Array.append state.error s.error

        Ok
            { s with
                data = rangeCtor state.data (Some s.data) exclusive op.Span
                error = error }

let internal parseId input msg =
    match peek input with
    | Some({ Data = Identifier sym; Span = span }, i) ->
        Ok
            { data = { Sym = sym; Span = span }
              error = [||]
              rest = input[i..] }
    | Some(token, _) -> Error(UnexpectedToken(token, msg))
    | None -> Error(IncompleteAtEnd msg)

let internal parseManyItem (input: Token[]) parser delimiter =
    let skipLimiter (input: Token[]) =
        let rec skip i cnt =
            if i = input.Length then
                i, cnt
            else
                match input[i].Data with
                | Comment _ -> skip (i + 1) cnt
                | Delimiter _ -> skip (i + 1) (cnt + 1)
                | t when delimiter t -> i, cnt + 1
                | _ -> i, cnt

        skip 0 0

    let rec skipUntil (input: Token[]) =
        match peekInline input with
        | Some({ Data = Delimiter _ }, i) -> input[i..]
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
        | Some token when delimiter token.Data -> Ok({ state with rest = state.rest[1..] }, Some token)
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
                    if cnt = 0 && i <> item.rest.Length then
                        Array.append error [| NeedDelimiter item.rest[i].Span |]
                    else
                        error

                let newState =
                    { data = Array.append state.data [| item.data |]
                      error = error
                      rest = item.rest[i..] }

                parseMany newState

    parseMany state
