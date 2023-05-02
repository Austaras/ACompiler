module Parser.Parser

open AST
open Lexer

type Error =
    | LexError of Lexer.Error
    | UnexpectedToken of Lexer.Token * string
    | Incomplete of AST.Span * string
    | IncompletePair of Lexer.Token
    | InvalidLValue of AST.Expr
    | BreakContinueOutsideOfLoop of AST.Span
    | ReturnOutsideOfFunction of AST.Span

type internal Context =
    { in_loop: bool
      in_fn: bool }

    static member Normal = { in_loop = false; in_fn = false }

type internal State<'T> =
    {
        data: 'T
        /// recoverable error
        error: Error[]
        rest: Lexer.Token[]
    }

    member this.FatalError e = Error(Array.append this.error [| e |])

let internal parse_until input parser limiter =
    let rec parse_until state =
        if state.rest.Length = 0 || limiter state.rest[0].data then
            Ok state
        else
            match parser state.rest with
            | Ok new_state ->
                let new_state =
                    { data = Array.append state.data [| new_state.data |]
                      error = Array.append state.error new_state.error
                      rest = new_state.rest }

                parse_until new_state
            | Error e -> Error e

    parse_until
        { data = [||]
          error = [||]
          rest = input }

open AST
open Lexer

let internal peek input =
    let rec peek (input: Token[]) i =
        if input.Length = 0 then
            None
        else
            match input[0].data with
            | Comment _ -> peek input[1..] (i + 1)
            | _ -> Some(input[0], i + 1)

    peek input 0

let internal peek_cross input =
    let rec peek_cross (input: Token[]) i =
        if input.Length = 0 then
            None
        else
            match input[0].data with
            | Comment _
            | Delimiter CR
            | Delimiter LF -> peek_cross input[1..] (i + 1)
            | _ -> Some(input[0], i + 1)

    peek_cross input 0

let is_valid_lvalue expr =
    match expr with
    | Id _
    | Field _
    | Unary { op = Deref } -> true
    | _ -> false

let rec internal parse_expr_prefix ctx (input: Lexer.Token[]) =
    match peek_cross input with
    | Some({ data = Lit l; span = span }, i) ->
        Ok
            { data = AST.Lit(l, span)
              error = [||]
              rest = input[i..] }
    | Some({ data = Identifier id; span = span }, i) ->
        Ok
            { data = Id { sym = id; span = span }
              error = [||]
              rest = input[i..] }

    | Some({ data = Paren Open; span = span }, i) ->
        let input = input[i..]

        if input.Length = 0 then
            Error([| IncompletePair(Token.Make (Paren Close) span) |])
        else
            match parse_expr ctx input with
            | Error e -> Error e
            | Ok state ->
                if state.rest.Length = 0 then
                    state.FatalError(IncompletePair(Token.Make (Paren Close) span))
                else
                    Ok { state with rest = state.rest[1..] }

    | Some({ data = Reserved IF }, i) ->
        let cond = parse_expr ctx input[i..]

        cond

    | Some({ data = Reserved BREAK; span = span }, i) ->
        let error =
            if ctx.in_loop then
                [| BreakContinueOutsideOfLoop span |]
            else
                [||]

        Ok
            { data = Break span
              error = error
              rest = input[i..] }

    | Some({ data = Reserved CONTINUE
             span = span },
           i) ->
        let error =
            if ctx.in_loop then
                [| BreakContinueOutsideOfLoop span |]
            else
                [||]

        Ok
            { data = Continue span
              error = error
              rest = input[i..] }

    | Some({ data = Reserved RETURN; span = span }, i) ->
        let error =
            if ctx.in_fn then
                [| ReturnOutsideOfFunction span |]
            else
                [||]

        Ok
            { data = Continue span
              error = error
              rest = input[i..] }

    | _ -> Error([| UnexpectedToken(input[0], "expression") |])

and internal parse_expr ctx (input: Lexer.Token[]) =
    let rec parse_expr_prec prec (input: Lexer.Token[]) : Result<State<Expr>, _> =
        let expr = parse_expr_prefix ctx input

        match expr with
        | Error e -> Error e
        | Ok state ->
            match peek_cross state.rest with
            | Some({ data = Operator _; span = span }, _) when state.rest.Length < 2 ->
                state.FatalError(Incomplete(span, "binary expression"))
            | Some({ data = Operator op }, i) when op.precedence > prec ->
                match parse_expr_prec op.precedence state.rest[i..] with
                | Error e -> Error e
                | Ok right ->
                    let span = Span.Make input[0].span.first right.data.span.last

                    let expr =
                        { left = state.data
                          op = op
                          right = right.data
                          span = span }

                    Ok(
                        { data = Binary expr
                          error = Array.append state.error right.error
                          rest = right.rest }
                    )
            | _ -> Ok state

    let rec parse_until (state: Result<State<Expr>, _>) =
        match state with
        | Error e -> Error e
        | Ok state ->
            match peek_cross state.rest with
            | Some({ data = Delimiter Semi }, _) -> Ok state
            | Some({ data = AssignOp _ | Eq; span = span }, _) when state.rest.Length < 2 ->
                state.FatalError(Incomplete(span, "binary expression"))
            | Some({ data = Eq }, i) ->
                let assignee = state.data

                let error =
                    if is_valid_lvalue assignee then
                        state.error
                    else
                        Array.append state.error [| InvalidLValue assignee |]

                match parse_expr_prefix ctx state.rest[i..] |> parse_until with
                | Error e -> Error e
                | Ok right ->
                    let expr =
                        { assignee = state.data
                          op = None
                          value = right.data
                          span = Span.Make state.data.span.first right.data.span.last }

                    Ok
                        { data = Assign expr
                          error = error
                          rest = right.rest }
            | Some({ data = AssignOp op }, i) ->
                let assignee = state.data

                let error =
                    if is_valid_lvalue assignee then
                        state.error
                    else
                        Array.append state.error [| InvalidLValue assignee |]

                match parse_until (Ok { state with rest = state.rest[i..] }) with
                | Error e -> Error e
                | Ok right ->
                    let expr =
                        { assignee = state.data
                          op = Some op
                          value = right.data
                          span = Span.Make state.data.span.first right.data.span.last }

                    Ok
                        { data = Assign expr
                          error = error
                          rest = right.rest }
            | Some({ data = Operator _; span = span }, _) when state.rest.Length < 2 ->
                state.FatalError(Incomplete(span, "binary expression"))
            | Some({ data = Operator op }, i) ->
                match parse_expr_prec op.precedence state.rest[i..] with
                | Error e -> Error e
                | Ok right ->
                    let span = Span.Make state.data.span.first right.data.span.last

                    let expr =
                        { left = state.data
                          op = op
                          right = right.data
                          span = span }

                    parse_until (
                        Ok
                            { data = Binary expr
                              error = Array.append state.error right.error
                              rest = right.rest }
                    )
            | _ -> Ok state

    parse_until (parse_expr_prec -1 input)

and internal parse_block ctx (input: Lexer.Token[]) =
    if input[0].data = Curly Open then
        let stmts = parse_until input[1..] (parse_stmt ctx) ((=) (Curly Close))
        Error(UnexpectedToken(input[0], "curly bracket"))
    else
        Error(UnexpectedToken(input[0], "curly bracket"))

and internal parse_decl (input: Lexer.Token[]) =
    match input[0].data with
    | Reserved FUNCTION ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "function declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | Reserved LET ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "function declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | Reserved USE ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "function declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | Reserved TYPE ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "type declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | Reserved STRUCT ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "struct declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | Reserved ENUM ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "enum declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | Reserved IMPL ->
        match peek input with
        | Some({ data = Identifier id; span = span }, i) ->
            let id = { sym = id; span = span }
            failwith "123"
        | None -> Error(Incomplete(input[0].span, "impl declaration"))
        | _ -> Error(UnexpectedToken(input[0], "identifier"))

    | _ -> Error(UnexpectedToken(input[0], "declaration"))

and internal parse_stmt ctx input =
    let first = input[0].span

    let res =
        match input[0].data with
        | Delimiter _ -> parse_stmt ctx input[1..]

        | _ -> Error(UnexpectedToken(input[0], "statement"))

    res

let internal parse_module_item (input: Lexer.Token[]) =
    let vis, i =
        match input[0].data with
        | Reserved PUBLIC -> Public, 1
        | Reserved INTERNAL -> Internal, 1
        | _ -> Private, 0

    failwith "123"

/// A hand written recursive descent parser produces AST without paren
///
/// There should be a CST somewhere, but at the time it's omitted
let parse (input: Lexer.Token[]) =
    match parse_until input parse_module_item (fun _ -> true) with
    | Ok state ->
        if state.error.Length = 0 then
            Ok state.data
        else
            Error state.error
    | Error e -> Error [| e |]
