module Parser.Tests.Util

open Parser
open Parser.Common

open FSharp.Json

exception CustomError of Error[]

let internal makeTest t =
    let test input =
        match Lexer.lex input with
        | Ok token ->
            match t Context.Normal token with
            | Ok ast -> Json.serialize ast.data
            | Error e -> raise (CustomError e)
        | Error e -> raise (CustomError(Array.map LexerError e))

    test
