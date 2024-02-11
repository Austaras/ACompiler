module Semantic.Tests.Type.Common

open System.Collections.Generic

open Xunit

open AST
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let runInfer input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    match check (Dictionary()) m with
    | Ok sema ->
        let map (id: AST.Id, t: Scheme) = (id.Sym, t.Print())
        sema.Binding |> Seq.map (|KeyValue|) |> Seq.map map |> Map.ofSeq
    | Error e -> failwithf "type error %A" e

let toBe (expect: Map<string, string>) (ty: Map<string, string>) =
    Assert.Multiple(fun () ->
        for KeyValue(name, expect) in expect do
            Assert.Equal(expect, ty[name]))
