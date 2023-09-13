module Parser.Tests.Module

open Parser.Lexer
open Parser.Parser
open Parser.Common

open System.IO
open Xunit

let parseModuleOk path =
    let path = __SOURCE_DIRECTORY__ + "/../../" + path

    let files = Directory.EnumerateFiles(path, "*.adf", SearchOption.AllDirectories)

    for path in files do
        let path = Path.GetFullPath path

        let error =
            match lex 0 (File.ReadAllText path) with
            | Error error -> Array.map LexerError error
            | Ok token ->
                match parse token with
                | Error(error, _) -> error
                | Ok _ -> [||]

        Assert.Empty error

[<Fact>]
let Example () =
    parseModuleOk "examples"

    parseModuleOk "runtime/std"
