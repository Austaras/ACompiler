module AST.Tests

open System
open Xunit

open Lexer
open Parser
open AST.TypeInfer

let runInfer input =
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

    ctx

[<Fact>]
let MyTest () =
    let input =
        IO.File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../examples/function/mutual_rec.adf")

    let ctx = runInfer input

    Assert.Empty(ctx.GetError)
