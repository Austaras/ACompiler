module Parser.Pat

open AST.AST
open Lexer
open Parser.Common

let rec internal parsePatInner (ctx: Context) input =
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
            | Some pat -> pat.Span.First
            | None -> span.First

        match peek from.rest with
        | Some({ data = data }, _) when canStartPat data ->
            let to_ = parseRangeRec from.rest

            match to_ with
            | Error e -> from.MergeFatalError e
            | Ok(to_: State<Pat>) ->
                Ok
                    { data =
                        RangePat
                            { From = from.data
                              To = Some to_.data
                              Span = Span.Make first to_.data.Span.Last }
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
                            { From = from.data
                              To = None
                              Span = span.WithFirst first }
                      error = [||]
                      rest = from.rest }

    and parseStructField input =
        match peek input with
        | Some({ data = Identifier sym; span = span }, i) ->
            let id = { Sym = sym; Span = span }

            match peekWith input[i..] Colon with
            | Some(_, j) ->
                match parsePatInner childCtx input[i + j ..] with
                | Error e -> Error e
                | Ok(v: State<Pat>) ->
                    Ok
                        { data =
                            KeyValuePat
                                { Id = id
                                  Pat = v.data
                                  Span = v.data.Span.WithFirst span.First }
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
                { Id = state.data
                  Field = field.data
                  Span = state.data.Span.WithLast paren.span.Last }

            let isRest (idx, pat) =
                match pat with
                | RestFieldPat _ when idx <> (Array.length field.data) - 1 -> true
                | _ -> false

            let toError (_, pat: FieldPat) = RestAtStructEnd pat.Span

            let restError = Array.indexed field.data |> Array.filter isRest |> Array.map toError

            Ok
                { data = StructPat pat
                  error = Array.concat [ state.error; field.error; restError ]
                  rest = field.rest }
        | Error e -> Error e

    and parsePath (state: State<PathPat>) =
        let rec parsePath (state: State<PathPat>) =
            match parseId state.rest "path pattern" with
            | Ok id ->
                let newState: State<PathPat> =
                    { data =
                        { Prefix = state.data.Prefix
                          Seg = Array.append state.data.Seg [| id.data |]
                          Span = state.data.Span.WithLast id.data.Span.Last }
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
        | Ok state ->
            match peek state.rest with
            | Some({ data = Paren Open }, i) ->
                let content =
                    parseCommaSeq state.rest[i..] (parsePatInner childCtx) (Paren Close) "enum pattern content"

                match content with
                | Ok(content, paren) ->
                    let pat =
                        { Name = state.data
                          Payload = content.data
                          Span = state.data.Span.WithLast paren.span.Last }

                    Ok
                        { data = EnumPat pat
                          error = Array.append state.error content.error
                          rest = content.rest }
                | Error e -> Error e

            | Some({ data = Curly Open }, i) -> parseStruct { state with rest = state.rest[i..] }

            | _ ->
                let data = IdPat state.data.Seg[0]

                Ok
                    { data = data
                      error = state.error
                      rest = state.rest }

    and parsePrefix input =
        match peek input with
        | Some({ data = Underline; span = span }, i) ->
            Ok
                { data = CatchAllPat span
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

            let path: State<PathPat> =
                { data =
                    { Prefix = Some prefix
                      Seg = [||]
                      Span = span }
                  error = [||]
                  rest = input[i..] }

            match consume path.rest ColonColon "path pattern" with
            | Ok(_, i) -> parsePath { path with rest = path.rest[i..] }
            | Error _ ->
                let error =
                    match prefix with
                    | Package
                    | Self -> [| IncompletePath span |]
                    | LowSelf -> if ctx.inMethod then [||] else [| OutofMethod span |]

                match prefix with
                | Self ->
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
                | LowSelf ->
                    let data =
                        if path.data.Seg.Length = 1 then
                            SelfPat path.data.Span
                        else
                            PathPat path.data

                    Ok
                        { data = data
                          error = error
                          rest = path.rest }
                | Package ->
                    Ok
                        { data = PathPat path.data
                          error = error
                          rest = path.rest }

        | Some({ data = Identifier _; span = span }, _) ->
            parsePath
                { data =
                    { Prefix = None
                      Seg = [||]
                      Span = span }
                  error = [||]
                  rest = input }

        | Some({ data = Operator(Arithmetic Sub)
                 span = span },
               i) ->
            let first = span.First

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
            let ele =
                parseCommaSeq input[i..] (parsePatInner childCtx) (Paren Close) "tuple pattern"

            match ele with
            | Ok(ele, paren) ->
                let pat, error =
                    if ele.data.Length = 1 then
                        ele.data[0], ele.error
                    else
                        let span = paren.span.WithFirst span.First

                        let error =
                            if (Array.filter isRestPat ele.data).Length > 1 then
                                Array.append ele.error [| TooManyRestPat span |]
                            else
                                ele.error

                        TuplePat { Ele = ele.data; Span = span }, error

                Ok
                    { data = pat
                      error = error
                      rest = ele.rest }
            | Error e -> Error e

        | Some({ data = Bracket Open; span = span }, i) ->
            let ele =
                parseCommaSeq input[i..] (parsePatInner childCtx) (Bracket Close) "array pattern"

            match ele with
            | Ok(ele, bracket) ->
                let span = bracket.span.WithFirst span.First
                let pat = ArrayPat { Ele = ele.data; Span = span }

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

        | Some({ data = Operator(Arithmetic BitAnd)
                 span = span },
               i) ->
            match consume input[i..] (Reserved LOWSELF) "reference self" with
            | Error e -> Error [| e |]
            | Ok(s, j) ->
                Ok
                    { data = RefSelfPat(span.WithLast s.Last)
                      error = [||]
                      rest = input[i + j ..] }

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
                let id = { Sym = sym; Span = span }

                let newState =
                    { data =
                        AsPat
                            { Pat = state.data
                              Id = id
                              Span = span.WithFirst state.data.Span.First }
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
                        { Pat = pat
                          Span = Span.Make pat[0].Span.First (Array.last pat).Span.Last }

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

and internal parsePat ctx input =
    match parsePatInner ctx input with
    | Error e -> Error e
    | Ok p ->
        let error =
            match p.data with
            | RestPat span -> Array.append p.error [| InvalidRestPat span |]
            | _ -> p.error

        Ok { p with error = error }
