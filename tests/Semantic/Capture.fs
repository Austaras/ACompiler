module Semantic.Tests.Capture

open FSharp.Json
open Snapper
open Xunit

open AST
open Util.Util
open Parser.Lexer
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let settings = SnapshotSettings.New().SnapshotFileName("Capture")

let runCheck input name =
    let token =
        match lex 0 input with
        | Ok tok -> tok
        | Error e -> failwithf "lex error %A" e

    let m =
        match parse token with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let checker = TypeCheck(Map.empty)

    checker.Check m

    Assert.Empty checker.GetError

    let mutable cid = 0

    let reform (key: Either<AST.Fn, AST.Closure>, value: ResizeArray<AST.Id>) =
        let key =
            match key with
            | Left f -> f.Name.Sym
            | Right _ ->
                let key = $"Closure{cid}"
                cid <- cid + 1
                key

        key, Array.ofSeq value

    (checker.GetInfo.Capture
     |> Seq.map (|KeyValue|)
     |> Seq.map reform
     |> Map.ofSeq
     |> Json.serialize)
        .ShouldMatchChildSnapshot(name, settings)

[<Fact>]
let Add () =
    runCheck
        "
    fn add(x) {
        fn add1(y) {
            fn add2(z) {
                return x + y + z
            }

            return add2
        }
        return add1
    }
    "
        "Add"
