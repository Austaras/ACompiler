module Parser.Tests.Util

open Parser
open Parser.Common

exception CustomError of Error[]

let internal makeTest parse dump input =
    match Lexer.lex input with
    | Ok token ->
        match parse Context.Normal token with
        | Ok ast -> fun sw -> dump sw 0 ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexerError e))
