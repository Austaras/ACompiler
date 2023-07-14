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

    let reform (key: AST.Id, value: Type.Type) = key.sym, value.ToString

    (ctx.GetTypes
     |> Seq.map (|KeyValue|)
     |> Seq.map reform
     |> Map.ofSeq
     |> Json.serialize)
        .ShouldMatchChildSnapshot(name, settings)

let runInferFromExample path =
    IO.File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../examples/" + path)
    |> runInfer

[<Fact>]
let MutualRec () =
    runInferFromExample "function/mutual_rec.adf" "MutualRec"

[<Fact>]
let Closure () =
    runInfer "fn call(c) { c(0) + 1 }" "Closure"

[<Fact>]
let Reference () =
    runInfer "fn deref(a) { *a + 1 }" "Reference"

[<Fact>]
let Struct () =
    runInferFromExample "function/struct.adf" "Struct"

// [<Fact>]
// let Poly () =
//     runInfer
//         "
//     fn id(x) { x }

//     fn main() {
//         id(id)(id(0))
//     }
//     "
//         "Poly1"

//     runInfer
//         "
//     fn one(x) { 1 }

//     fn main() {
//         one(one(one))
//     }
//     "
//         "Poly2"

// [<Fact>]
// let WeirdRec =
//     runInfer
//         "
//     fn weird_rec(x) { weird_rec(1) }
//     "
//         "WeirdRec"
