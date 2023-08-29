module Parser.Parser

open AST
open AST
open Lexer.Lexer

open Parser.Common
open Parser.Stmt

/// A hand written recursive descent parser produces AST without paren
///
/// There should be a CST somewhere, but at the time it's omitted
let parse (input: Token[]) =
    let span =
        if input.Length > 0 then
            let first = input[0].span.first
            let last = (Array.last input).span.last

            Span.Make first last
        else
            Span.dummy

    match parseManyItem input parseModuleItem (fun _ -> false) with
    | Ok(state, _) ->
        let data = { item = state.data; span = span }

        if state.error.Length = 0 then
            Ok data
        else
            Error(state.error, Some data)
    | Error e -> Error(e, None)
