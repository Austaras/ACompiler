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

    Directory.EnumerateFiles(path, "*.adf", SearchOption.AllDirectories)
    |> Seq.map (Path.GetFullPath >> (Array.create 1))

let arch = Common.Target.X86_64

let runTansform input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    match check (Dictionary()) m with
    | Ok sema -> (lower arch m sema).Print
    | Error e -> failwithf "type error %A" e

let spec = getAllFile "/Spec"

[<Theory>]
[<MemberData(nameof (spec))>]
let Spec path = snap.ShouldMatch runTansform path
