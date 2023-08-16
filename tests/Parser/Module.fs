module Parser.Tests.Module

open Lexer
open Parser.Parser

open System.IO
open Xunit

let parseModuleOk path =
    let content = File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../examples/" + path)

    match Lexer.lex 0 content with
    | Error error -> Array.map Util.LexError error
    | Ok token ->
        match parse token with
        | Error(error, _) -> Array.map Util.ParseError error
        | Ok _ -> [||]


[<Fact>]
let Example () =
    Assert.Empty(parseModuleOk "example.adf")
