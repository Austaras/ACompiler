module FLIR.Tests.Transform

open System.IO
open System.Collections.Generic

open Xunit

open Snapshot
open Parser.Parser
open Semantic.Check
open FLIR.Transform

let snap = Snapshot("flir")

let getAllFile path =
    let path = __SOURCE_DIRECTORY__ + path

    Directory.EnumerateFiles(path, "*.adf", SearchOption.AllDirectories)
    |> Seq.map (Path.GetFullPath >> (Array.create 1))

let arch = Common.Target.X86_64

let runTansform input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema, error = check (Dictionary()) m

    Assert.Empty error

    (transform arch m sema).Print

let spec = getAllFile "/Spec"

[<Theory>]
[<MemberData(nameof (spec))>]
let Spec path = snap.ShouldMatch runTansform path
