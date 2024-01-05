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

    let reform (value: ResizeArray<AST.Id>) = value |> Seq.map _.Sym |> Array.ofSeq

    sema.Capture.Values |> Seq.map reform |> Array.ofSeq

[<Fact>]
let Add () =
    let capture =
        runCheck
            "
fn add(x) {
    |y| |z| x + y + z
}
"

    Assert.Equivalent([| [| "x"; "y" |]; [| "x" |] |], capture)

[<Fact>]
let Shadow () =
    let shadow =
        runCheck
            "
fn foo() {
    fn bar() {}
    let a = || bar

    let bar = 1

    return || bar
}
"

    Assert.Equivalent([| [| "bar" |] |], shadow)
