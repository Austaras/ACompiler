module Semantic.Tests.Capture

open System.Collections.Generic

open Xunit

open Syntax.Parser
open Semantic.Semantic
open Semantic.Check

let runCheck input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema = SemanticInfo.Create()

    match check sema m with
    | Ok sema -> Map.values sema.Capture.ToMap |> Seq.map (Array.map _.Sym) |> Array.ofSeq
    | Error e -> failwithf "type error %A" e

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
