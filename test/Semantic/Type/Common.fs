module Semantic.Tests.Type.Common

open System.Collections.Generic

open Xunit

open Syntax
open Syntax.Parser
open Semantic.Semantic
open Semantic.Analysis

let runAnalysis input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema = SemanticInfo.Create()

    match analysis sema m with
    | Ok sema ->
        let map (id: AST.Id, t: Scheme) = (id.Sym, t.Print())
        sema.DeclTy |> Seq.map (|KeyValue|) |> Seq.map map |> Map.ofSeq
    | Error e -> failwithf "type error %A" e

let toBe (expect: Map<string, string>) (ty: Map<string, string>) =
    Assert.Multiple(fun () ->
        for KeyValue(name, expect) in expect do
            Assert.Equal(expect, ty[name]))
