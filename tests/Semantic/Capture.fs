module Semantic.Tests.Capture

open System.Collections.Generic

open Xunit

open AST
open Util.Util
open Parser.Lexer
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let runCheck input =
    let token =
        match lex input with
        | Ok tok -> tok
        | Error e -> failwithf "lex error %A" e

    let m =
        match parse token with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema, error = typeCheck (Dictionary()) m

    Assert.Empty error

    let mutable cid = 0

    let reform (key: Either<AST.Fn, AST.Closure>, value: ResizeArray<AST.Id>) =
        let key =
            match key with
            | Left f -> f.Name.Sym
            | Right _ ->
                let key = $"Closure{cid}"
                cid <- cid + 1
                key

        key, value |> Array.ofSeq |> Array.map _.Sym

    sema.Capture |> Seq.map (|KeyValue|) |> Seq.map reform |> Map.ofSeq

[<Fact>]
let Add () =
    let capture =
        runCheck
            "
fn add(x) {
    |y| |z| x + y + z
}
"

    Assert.Equivalent(capture, Map [ "Closure0", [| "x"; "y" |]; "Closure1", [| "x" |] ])
