module Parser.Type

open AST.AST
open Lexer.Lexer

open Parser.Common
open Parser.Pat

let rec internal parsePathTypeInner (ctx: Context) (state: State<Path>) =
    let parseTypeParam (state: State<Path>) =
        let param = parseLtGt state.rest (parseType ctx.InTypeInst) "type instantiation"

        match param with
        | Ok(param) ->
            let data, span = param.data
            let error = Array.append state.error param.error

            let error =
                if data.Length = 0 then
                    Array.append error [| EmptyTypeInst span |]
                else
                    error

            let lastId, _ = Array.last state.data.seg

            Array.set state.data.seg (state.data.seg.Length - 1) (lastId, fst param.data)

            let data =
                { state.data with
                    span = state.data.span.WithLast span.last }

            let newState =
                { data = data
                  error = Array.append error param.error
                  rest = param.rest }

            match peek newState.rest with
            | Some({ data = ColonColon }, i) ->
                parsePathTypeInner
                    ctx
                    { newState with
                        rest = newState.rest[i..] }
            | _ -> Ok newState

        | Error e -> Error e

    match parseId state.rest "path type" with
    | Error e -> Error [| e |]
    | Ok id ->
        let error = Array.append state.error id.error

        let data =
            { state.data with
                seg = Array.append state.data.seg [| id.data, [||] |]
                span = state.data.span.WithLast id.data.span.last }

        let newState =
            { data = data
              error = error
              rest = id.rest }

        match peek newState.rest with
        | Some({ data = ColonColon }, i) ->
            let rest = newState.rest[i..]

            match peek rest with
            | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
                let newState = { newState with rest = rest[i - 1 ..] }

                parseTypeParam newState
            | _ -> parsePathTypeInner ctx { newState with rest = rest }
        | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
            let newState =
                { newState with
                    rest = newState.rest[i - 1 ..] }

            parseTypeParam newState

        | _ -> Ok newState

and internal parsePathType (ctx: Context) (s: State<Path>) =
    match parsePathTypeInner ctx s with
    | Error e -> Error e
    | Ok { data = path
           error = error
           rest = rest } ->

        if path.prefix = None && path.seg.Length = 1 && (snd path.seg[0]).Length = 0 then
            Ok
                { data = TypeId(fst path.seg[0])
                  error = error
                  rest = rest }
        else
            Ok
                { data = PathType path
                  error = error
                  rest = rest }

and internal parseType ctx input =
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

    match peek input with
    | Some({ data = Reserved(PACKAGE | SELF | LOWSELF as kw)
             span = span },
           i) ->
        let prefix, isSelf =
            match kw with
            | PACKAGE -> Package, false
            | SELF -> Self, true
            | LOWSELF -> LowSelf, true
            | _ -> failwith "unreachable"

        let path =
            { data =
                { prefix = Some prefix
                  seg = [||]
                  span = span }
              error = [||]
              rest = input[i..] }

        match consume path.rest ColonColon "path type" with
        | Error _ ->
            let error = if not isSelf then [| IncompletePath span |] else [||]

            Ok
                { data = PathType path.data
                  error = error
                  rest = path.rest }
        | Ok(_, i) -> parsePathType ctx { path with rest = path.rest[i..] }
    | Some({ data = Identifier _; span = span }, _) ->
        parsePathType
            ctx
            { data =
                { prefix = None
                  seg = [||]
                  span = span }
              error = [||]
              rest = input }
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

and internal parseTypeBound ctx input =
    let state =
        { data = [||]
          error = [||]
          rest = input }

    let parser input =
        match peek input with
        | Some({ data = Identifier _ }, _) ->
            let data =
                { prefix = None
                  seg = [||]
                  span = Span.dummy }

            let state =
                { data = data
                  error = [||]
                  rest = input }

            parsePathType ctx state
        | Some({ data = Reserved(PACKAGE | SELF | LOWSELF as kw)
                 span = span },
               i) ->
            let prefix, isSelf =
                match kw with
                | PACKAGE -> Package, false
                | LOWSELF -> LowSelf, false
                | SELF -> Self, true
                | _ -> failwith "unreachable"

            let path =
                { data =
                    { prefix = Some prefix
                      seg = [||]
                      span = span }
                  error = [||]
                  rest = input[i..] }

            match consume path.rest ColonColon "path type" with
            | Error _ ->
                let error = if not isSelf then [| IncompletePath span |] else [||]

                Ok
                    { data = PathType path.data
                      error = error
                      rest = path.rest }
            | Ok(_, i) -> parsePathType ctx { path with rest = path.rest[i..] }
        | Some(token, _) -> Error [| UnexpectedToken(token, "type bound") |]
        | None -> Error [| IncompleteAtEnd("type bound") |]

    let rec parseRecursive (state: State<_>) =
        match parser state.rest with
        | Error e -> state.MergeFatalError e
        | Ok(newState: State<_>) ->
            let data, extraError =
                match newState.data with
                | TypeId i ->
                    { prefix = None
                      seg = [| i, [||] |]
                      span = i.span },
                    [||]
                | PathType t -> t, [||]
                | InferedType s ->
                    { prefix = None
                      seg = [||]
                      span = Span.dummy },
                    [| UnexpectedToken({ data = Identifier "_"; span = s }, "type bound") |]
                | _ -> failwith "unreachable"

            let error = Array.append newState.error extraError

            let newState =
                { data = Array.append state.data [| data |]
                  error = Array.append state.error error
                  rest = newState.rest }

            match peek newState.rest with
            | Some({ data = Operator(Arithmetic Add) }, i) ->
                parseRecursive (
                    { newState with
                        rest = newState.rest[i..] }
                )
            | _ -> Ok newState

    match parseRecursive state with
    | Ok s -> Ok s
    | Error e ->
        let last = e.Length - 1

        match Array.last e with
        | IncompleteAtEnd _ -> Array.set e last (IncompleteAtEnd "type bound")
        | UnexpectedToken(t, _) -> Array.set e last (UnexpectedToken(t, "type bound"))
        | _ -> ()

        Error e

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
                match parseTypeBound { ctx with inTypeInst = false } id.rest[i..] with
                | Ok bound ->
                    let param =
                        { id = id.data
                          const_ = true
                          bound = bound.data
                          span = (Array.last bound.data).span.WithFirst span.first }

                    Ok
                        { data = param
                          error = Array.append id.error bound.error
                          rest = bound.rest }
                | Error e -> Error e
            | _ ->
                Ok
                    { data =
                        { id = id.data
                          const_ = true
                          bound = [||]
                          span = id.data.span.WithFirst span.first }
                      error = id.error
                      rest = id.rest }
        | Error e -> Error [| e |]
    | Some({ data = Identifier sym; span = span }, i) ->
        let id = { sym = sym; span = span }

        match peek input[i..] with
        | Some({ data = Colon }, j) ->
            match parseTypeBound { ctx with inTypeInst = false } input[i + j ..] with
            | Ok bound ->
                let param =
                    { id = id
                      const_ = false
                      bound = bound.data
                      span = (Array.last bound.data).span.WithFirst span.first }

                Ok
                    { data = param
                      error = bound.error
                      rest = bound.rest }
            | Error e -> Error e
        | _ ->
            Ok
                { data =
                    { id = id
                      const_ = false
                      bound = [||]
                      span = id.span }
                  error = [||]
                  rest = input[i..] }

    | Some(token, _) -> Error [| UnexpectedToken(token, "type parameter") |]
    | None -> Error [| IncompleteAtEnd "type parameter" |]
