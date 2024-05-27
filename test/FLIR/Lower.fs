module FLIR.Tests.Lower

open System.IO
open System.Collections.Generic

open Xunit

open Snapshot
open Parser.Parser
open Semantic.Check
open FLIR.Lower

let snap = Snapshot("flir")

let getAllFile path =
    let path = __SOURCE_DIRECTORY__ + path

    let dict = Dictionary()

    for path in Directory.EnumerateFiles(path, "*.adf", SearchOption.AllDirectories) do
        let path = Path.GetFullPath path
        let name = (Directory.GetParent path).Name

        if not (name.StartsWith "_") then
            dict.Add(name, path)

    dict

let arch = Common.Target.X86_64

let runTansform input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    match check (Dictionary()) m with
    | Ok sema -> (lower arch m sema).Print
    | Error e -> failwithf "type error %A" e

let specFile = getAllFile "/Spec"
let spec = specFile.Keys |> Seq.map (Array.create 1)

[<Theory>]
[<MemberData(nameof (spec))>]
let Spec name =
    snap.ShouldMatch runTansform specFile[name]
