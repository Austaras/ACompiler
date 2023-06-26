module AST.Tests

open FSharp.Json
open Snapper
open System
open Xunit

open Lexer
open Parser
open AST.TypeInfer

let settings = SnapshotSettings.New().SnapshotFileName("Infer")

let runInfer input name =
    let token =
        match Lexer.lex 0 input with
        | Ok tok -> tok
        | Error e -> failwithf "lex error %A" e

    let m =
        match Parser.parse token with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let ctx = Context()

    ctx.Infer m

    Assert.Empty ctx.GetError

    let stripSpan (key: AST.Id, value: Type.Type) = key.sym, value.ToString

    (ctx.GetTypes
     |> Seq.map (|KeyValue|)
     |> Seq.map stripSpan
     |> Map.ofSeq
     |> Json.serialize)
        .ShouldMatchChildSnapshot(name, settings)

let runInferFromExample path =
    let input = IO.File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../examples/" + path)

    runInfer input

[<Fact>]
let MutualRec () =
    runInferFromExample "function/mutual_rec.adf" "MutualRec"

[<Fact>]
let Closure () =
    runInfer "fn call(c) { c(0) + 1 }" "Closure"

[<Fact>]
let Reference () =
    runInfer "fn deref(a) { *a + 1 }" "Reference"
