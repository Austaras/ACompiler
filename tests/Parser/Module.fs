module Parser.Tests.Module

open Parser.Lexer
open Parser.Parser

open System.IO
open Xunit

let parseModuleOk prefix path =
    let content = File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../" + prefix + path)

    match lex 0 content with
    | Error error -> Array.map Util.LexError error
    | Ok token ->
        match parse token with
        | Error(error, _) -> Array.map Util.ParseError error
        | Ok _ -> [||]

[<Fact>]
let Example () =
    let parse = parseModuleOk "examples/"
    Assert.Empty(parse "example.adf")

    Assert.Empty(parse "type/tree.adf")

[<Fact>]
let Std () =
    let parse = parseModuleOk "runtime/"
    Assert.Empty(parse "core/util.adf")
