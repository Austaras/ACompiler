module FLIR.Tests.Lower

open System.IO
open System.Collections.Generic

open Xunit

open Common.Config
open Snapshot
open Syntax.Parser
open Semantic.Analysis
open Optimize.FLIR
open Optimize.Lower.Lower
open Optimize.SSA
open Optimize.Optimize

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
let optSnap = Snapshot("opt.flir")
let aggrSnap = Snapshot("aggr.flir")

let cfgShouldMatch (f: Func) =
    for idx in 0 .. f.Block.Length - 1 do
        let block = f.Block[idx]
        let node = f.CFG[idx]

        match block.Trans with
        | Jump j ->
            Assert.Equal(1, node.Succ.Length)
            Assert.Contains(j.Target, node.Succ)
            Assert.Contains(idx, f.CFG[j.Target].Pred)
        | Branch b ->
            Assert.Equal(2, node.Succ.Length)
            Assert.Contains(b.Zero, node.Succ)
            Assert.Contains(b.One, node.Succ)
            Assert.Contains(idx, f.CFG[b.Zero].Pred)
            Assert.Contains(idx, f.CFG[b.One].Pred)
        | Switch s ->
            Assert.Equal(s.Dest.Length, node.Succ.Length)

            for dest, _ in s.Dest do
                Assert.Contains(dest, node.Succ)
                Assert.Contains(idx, f.CFG[dest].Pred)
        | Return _
        | Unreachable _ -> Assert.Equal(0, node.Succ.Length)

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

        for f in m.Func do
            cfgShouldMatch f

        let ssaModule = ssa m
        ssaSnap.ShouldMatch ssaModule.Print specFile[name]

        for f in ssaModule.Func do
            cfgShouldMatch f

        let m = optimize Optimization.Release ssaModule
        optSnap.ShouldMatch m.Print specFile[name]

        for f in m.Func do
            cfgShouldMatch f

        let m = optimize Optimization.Aggressive ssaModule
        aggrSnap.ShouldMatch m.Print specFile[name]

        for f in m.Func do
            cfgShouldMatch f

    | Error e -> failwithf "type error %A" e
