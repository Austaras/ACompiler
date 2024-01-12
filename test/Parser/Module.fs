module Parser.Tests.Module

open System.IO

open Xunit

open Parser.Parser

let getAllFile path =
    let path = __SOURCE_DIRECTORY__ + "/../../" + path

    Directory.EnumerateFiles(path, "*.adf", SearchOption.AllDirectories)
    |> Seq.map (Path.GetFullPath >> (Array.create 1))

let parseModuleOk path =
    let error =
        match parse (File.ReadAllText path) with
        | Error(error, _) -> error
        | Ok _ -> [||]

    Assert.Empty error

let example = getAllFile "example"

[<Theory>]
[<MemberData(nameof (example))>]
let Example path = parseModuleOk path

let std = getAllFile "runtime"

[<Theory>]
[<MemberData(nameof (std))>]
let Std path = parseModuleOk path
