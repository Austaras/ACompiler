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

    (ctx.GetTypes.var
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

// runInfer
//     "
//     struct Foo {
//         b: &Bar
//     }

//     struct Bar {
//         f: &Foo
//     }

//     fn foo(f) {
//         f.b.f
//     }
// "
//     "AutoDeref"

[<Fact>]
let Return () =
    runInfer
        "
        fn foo(i) { 
            if i == 0 {
                return 0
            }

            i + 1
        }"
        "Return"

[<Fact>]
let Poly () =
    runInfer
        "
    fn id(x) { x }

    fn main() {
        id(id)(id(0))
    }
    "
        "Poly"

    runInfer
        "
    fn one(x) { 1 }

    fn main() {
        one(one(one))
    }
    "
        "PolyOne"

    runInfer "fn double(f, x) { f(f(x)) }" "PolyDouble"

[<Fact>]
let WeirdRec () =
    runInfer "fn weird_rec(x) { weird_rec(1) }" "WeirdRec"

[<Fact>]
let Tuple () =
    runInfer
        "
        fn foo((a, b, c)) {
            a == 1 && b == 2 && c == 3
        }
    "
        "Tuple"

[<Fact>]
let Match () =
    runInferFromExample "function/fib.adf" "Fib"

    runInfer
        "
        enum Either {
            L(i32),
            R(f64)
        }

        fn is_zero(e: E) {
            match e {
                Either::L(i) => i == 0,
                Either::R(f) => f == 0.0
            }
        }
    "
        "Enum"
