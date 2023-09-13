module Parser.Stmt

open AST.AST
open Lexer

open Parser.Common
open Parser.Type
open Parser.Expr

let internal canStartDecl token =
    match token with
    | Reserved(FUNCTION | LET | CONST | USE | IMPL | TRAIT | TYPE | ENUM | STRUCT) -> true
    | _ -> false

let rec internal parseBlock (ctx: Context) input =
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

and internal parseExpr =
    Expr.parseBlock <- parseBlock
    Expr.parseExpr

and internal parseFn ctx input span =
    match parseId input "function name" with
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
                        match
                            parseBlock
                                { ctx with
                                    inFn = true
                                    inLoop = false
                                    inCond = false
                                    mayHaveVis = false }
                                retTy.rest
                        with
                        | Error e -> Error(Array.append retTy.error e)
                        | Ok block ->
                            let fn =
                                { name = id.data
                                  tyParam = typeParam
                                  retTy = retTy.data
                                  param = param.data
                                  body = block.data
                                  span = span }

                            Ok
                                { data = fn
                                  error = Array.append retTy.error block.error
                                  rest = block.rest }

and internal parseTypeAlias ctx input (span: Span) =
    match parseId input "type alias name" with
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
                    { data = decl
                      error = Array.append id.error ty.error
                      rest = ty.rest }

        | Error e -> id.FatalError e

and internal parseConst (ctx: Context) input (span: Span) =
    match parseParam ctx.InDecl input with
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
                    { data = decl
                      error = Array.append param.error value.error
                      rest = value.rest }

        | Error e -> param.FatalError e

and internal parseImplItem isForTrait input =
    let vis, visSpan, error, i =
        match peek input with
        | Some({ data = Reserved PUBLIC; span = span } as token, i) ->
            Public,
            Some span,
            (if isForTrait then
                 [| VisibilityNotAllowed token |]
             else
                 [||]),
            i
        | Some({ data = Reserved INTERNAL
                 span = span } as token,
               i) ->
            Internal,
            Some span,
            (if isForTrait then
                 [| VisibilityNotAllowed token |]
             else
                 [||]),
            i
        | _ -> Private, None, [||], 0

    let makeItem item =
        match visSpan with
        | Some span ->
            { vis = vis
              item = item
              span = item.span.WithFirst span.first }
        | None ->
            { vis = vis
              item = item
              span = item.span }

    let input = input[i..]
    let ctx = { Context.Normal with inImpl = true }

    match peek input with
    | Some({ data = Reserved FUNCTION
             span = span },
           i) ->
        let f = parseFn { ctx with inMethod = true } input[i..] span

        match f with
        | Error e -> Error e
        | Ok f ->
            Ok
                { data = makeItem (Method f.data)
                  error = Array.append error f.error
                  rest = f.rest }
    | Some({ data = Reserved TYPE; span = span }, i) ->
        match parseTypeAlias ctx input[i..] span with
        | Error e -> Error e
        | Ok f ->
            Ok
                { data = makeItem (AssocType f.data)
                  error = Array.append error f.error
                  rest = f.rest }
    | Some({ data = Reserved CONST; span = span }, i) ->
        match parseFn { ctx with inMethod = true } input[i..] span with
        | Error e -> Error e
        | Ok f ->
            Ok
                { data = makeItem (Method f.data)
                  error = Array.append error f.error
                  rest = f.rest }
    | Some(token, _) -> Error [| UnexpectedToken(token, "impl item") |]
    | None -> Error [| IncompleteAtEnd "impl item" |]

and internal parseDecl (ctx: Context) input =
    match peek input with
    | Some({ data = Reserved FUNCTION
             span = span },
           i) ->
        match parseFn ctx input[i..] span with
        | Error e -> Error e
        | Ok f ->
            Ok
                { data = FnDecl f.data
                  error = f.error
                  rest = f.rest }

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
        match parseConst ctx input[i..] span with
        | Error e -> Error e
        | Ok c ->
            Ok
                { data = Const c.data
                  error = c.error
                  rest = c.rest }

    | Some({ data = Reserved USE }, i) ->
        let path =
            match peek input[i..] with
            | Some({ data = Identifier id; span = span }, j) ->
                let id = { sym = id; span = span }

                let data =
                    { prefix = None
                      seg = [| id |]
                      item = [||]
                      span = span }

                Ok
                    { data = data
                      error = [||]
                      rest = input[i + j ..] }
            | Some({ data = Reserved(LOWSELF | PACKAGE as kw)
                     span = span },
                   j) ->
                let prefix =
                    match kw with
                    | LOWSELF -> LowSelf
                    | PACKAGE -> Package
                    | _ -> failwith "unreachable"

                let data =
                    { prefix = Some prefix
                      seg = [||]
                      item = [||]
                      span = span }

                Ok
                    { data = data
                      error = [||]
                      rest = input[i + j ..] }
            | Some(token, _) -> Error [| UnexpectedToken(token, "identifier") |]
            | None -> Error [| IncompleteAtEnd "use item" |]

        match path with
        | Error e -> Error e
        | Ok p ->
            let rec parseSeg (state: State<Use>) =
                match peek state.rest with
                | Some({ data = ColonColon }, i) ->
                    match peek state.rest[i..] with
                    | Some({ data = Identifier sym; span = span }, j) ->
                        let id = { sym = sym; span = span }

                        let data =
                            { state.data with
                                seg = Array.append state.data.seg [| id |]
                                span = state.data.span.WithLast span.last }

                        let newState =
                            { state with
                                data = data
                                rest = state.rest[i + j ..] }

                        parseSeg newState
                    | Some({ data = Operator(Arithmetic Mul)
                             span = span },
                           j) ->
                        let data =
                            { state.data with
                                item = [| UseAll span |]
                                span = state.data.span.WithLast span.last }

                        let newState =
                            { state with
                                data = data
                                rest = state.rest[i + j ..] }

                        Ok newState
                    | Some(token, _) -> Error [| UnexpectedToken(token, "identifier") |]
                    | None -> Error [| IncompleteAtEnd "use item" |]
                | _ -> Ok state

            let path = parseSeg p

            match path with
            | Error e -> Error e
            | Ok p ->
                let data = p.data

                let data =
                    if Array.isEmpty data.item && not (Array.isEmpty data.seg) then
                        let last = Array.length data.seg - 1

                        { data with
                            seg = data.seg[.. last - 1]
                            item = [| UseItem data.seg[last] |] }
                    else
                        data

                let error =
                    if data.prefix <> None && Array.isEmpty data.item then
                        Array.append p.error [| IncompletePath data.span |]
                    else
                        p.error

                Ok
                    { data = Use data
                      error = error
                      rest = p.rest }

    | Some({ data = Reserved TYPE; span = span }, i) ->
        match parseTypeAlias ctx input[i..] span with
        | Error e -> Error e
        | Ok ty ->
            Ok
                { data = TypeDecl ty.data
                  error = ty.error
                  rest = ty.rest }

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

    | Some({ data = Reserved IMPL; span = span }, i) ->
        let first = span.first

        let typeParam =
            let rest = input[i..]

            match peek rest with
            | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
                parseLtGt rest[i - 1 ..] (parseTypeParam ctx) "impl type paramater"
            | _ ->
                Ok
                    { data = [||], Span.dummy
                      error = [||]
                      rest = rest }

        match typeParam with
        | Error e -> Error e
        | Ok param ->
            match parseType ctx param.rest with
            | Error e -> param.MergeFatalError e
            | Ok ty1 ->
                let ty2, isForTrait =
                    match peek ty1.rest with
                    | Some({ data = Reserved FOR }, i) ->
                        match parseType ctx ty1.rest[i..] with
                        | Error e -> ty1.MergeFatalError e, false
                        | Ok t -> Ok(Some t), true
                    | _ -> Ok None, false

                let impl =
                    match ty2 with
                    | Ok None ->
                        let data =
                            { trait_ = None
                              typeParam = fst param.data
                              type_ = ty1.data
                              item = [||]
                              span = Span.dummy }

                        Ok
                            { data = data
                              error = ty1.error
                              rest = ty1.rest }
                    | Ok(Some ty2) ->
                        let error = Array.append ty1.error ty2.error

                        let trait_, error =
                            match ty1.data with
                            | TypeId id ->
                                Some
                                    { prefix = None
                                      seg = [| id, [||] |]
                                      span = id.span },
                                error
                            | PathType p ->
                                Some
                                    { prefix = p.prefix
                                      seg = p.seg
                                      span = p.span },
                                error
                            | _ -> None, Array.append error [| InvalidTrait ty1.data.span |]

                        let data =
                            { trait_ = trait_
                              typeParam = fst param.data
                              type_ = ty2.data
                              item = [||]
                              span = Span.dummy }

                        Ok
                            { data = data
                              error = error
                              rest = ty2.rest }
                    | Error e -> Error e

                match impl with
                | Error e -> Error e
                | Ok impl ->
                    match consume impl.rest (Curly Open) "impl block" with
                    | Error e -> impl.FatalError e
                    | Ok(_, i) ->
                        let item =
                            parseManyItem impl.rest[i..] (parseImplItem isForTrait) ((=) (Curly Close))

                        match item with
                        | Error e -> impl.MergeFatalError e
                        | Ok(item, curly) ->
                            match curly with
                            | None ->
                                Error(Array.concat [ impl.error; item.error; [| IncompleteAtEnd "implmentation" |] ])
                            | Some { span = span } ->
                                Ok
                                    { data =
                                        Impl
                                            { impl.data with
                                                item = item.data
                                                span = span.WithFirst first }
                                      error = Array.append impl.error item.error
                                      rest = item.rest }

    | Some({ data = Reserved TRAIT }, i) ->
        match parseId input[i..] "trait name" with
        | Error e -> Error [| e |]
        | Ok id ->
            let typeParam =
                let rest = input[i..]

                match peek rest with
                | Some({ data = Operator(Lt | Arithmetic Shl) }, i) ->
                    parseLtGt rest[i - 1 ..] (parseTypeParam ctx) "trait type paramater"
                | _ ->
                    Ok
                        { data = [||], Span.dummy
                          error = [||]
                          rest = rest }

            match typeParam with
            | Error e -> Error e
            | Ok param -> failwith "123"

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

let rec internal parseModuleItem (input: Token[]) =
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

            let error =
                match d with
                | FnDecl f when vis = Public ->
                    let needTy = Array.filter (fun (p: Param) -> p.ty = None) f.param
                    let needTy = Array.map (fun (p: Param) -> PubTypeAnnotation p.span) needTy

                    Array.append s.error needTy
                | _ -> s.error

            Ok
                { data = item
                  error = error
                  rest = s.rest }
        | ExprStmt e ->
            let error = Array.append s.error [| TopLevelExpr e.span |]

            match parseModuleItem s.rest with
            | Ok m ->
                Ok
                    { m with
                        error = Array.append error m.error }
            | Error e -> Error(Array.append error e)
