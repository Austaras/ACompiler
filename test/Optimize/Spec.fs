module FLIR.Tests.Lower

open System.IO
open System.Collections.Generic

open Xunit

open Snapshot
open Syntax.Parser
open Semantic.Analysis
open Optimize.Lower.Lower
open Optimize.SSA

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

let specFile = getAllFile "/Spec"
let spec = specFile.Keys |> Seq.map (Array.create 1)

let lowerSnap = Snapshot("raw.flir")
let ssaSnap = Snapshot("ssa.flir")

[<Theory>]
[<MemberData(nameof (spec))>]
let Spec name =
    let content = File.ReadAllText(specFile[name])

    let m =
        match parse content with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema = Semantic.Semantic.SemanticInfo.Create()

    match analysis sema m with
    | Ok sema ->
        let m = lower arch m sema
        lowerSnap.ShouldMatch m.Print specFile[name]

        let m = ssa m
        ssaSnap.ShouldMatch m.Print specFile[name]
    | Error e -> failwithf "type error %A" e
