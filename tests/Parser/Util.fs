module Parser.Tests.Util

open Lexer
open Parser.Parser
open Parser.Common

open FSharp.Json

type ErrorData =
    | ParseError of Error
    | LexError of Lexer.Error

exception CustomError of ErrorData[]

let internal makeTest t =
    let test input =
        match Lexer.lex 0 input with
        | Ok token ->
            match t Context.Normal token with
            | Ok ast -> Json.serialize ast.data
            | Error e -> raise (CustomError(Array.map ParseError e))
        | Error e -> raise (CustomError(Array.map LexError e))

    test
