module Semantic.Tests.Capture

open System.Collections.Generic

open Xunit

open AST
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let runCheck input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema, error = check (Dictionary()) m

    Assert.Empty error

    Map.values sema.Capture |> Seq.map (Array.map _.Sym) |> Array.ofSeq

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

    || bar
}
"

    Assert.Equivalent([| [| "bar" |] |], shadow)
