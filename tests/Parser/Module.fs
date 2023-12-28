module Parser.Tests.Module

open System.IO

open Xunit

open Parser.Lexer
open Parser.Parser
open Parser.Common

let getAllFile path =
    let path = __SOURCE_DIRECTORY__ + "/../../" + path

    Directory.EnumerateFiles(path, "*.adf", SearchOption.AllDirectories)
    |> Seq.map (Path.GetFullPath >> (Array.create 1))

let parseModuleOk path =
    let error =
        match lex (File.ReadAllText path) with
        | Error error -> Array.map LexerError error
        | Ok token ->
            match parse token with
            | Error(error, _) -> error
            | Ok _ -> [||]

    Assert.Empty error

let example = getAllFile "examples"

[<Theory>]
[<MemberData(nameof (example))>]
let Example path = parseModuleOk path

let std = getAllFile "runtime/std"

[<Theory>]
[<MemberData(nameof (std))>]
let Std path = parseModuleOk path
