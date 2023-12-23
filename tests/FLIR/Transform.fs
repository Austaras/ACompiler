module FLIR.Tests.Transform

open System.Collections.Generic

open Xunit

open Parser.Lexer
open Parser.Parser
open Semantic.Check
open FLIR.Transform

let arch = Common.Target.X86_64

let runInfer input name =
    let token =
        match lex 0 input with
        | Ok tok -> tok
        | Error e -> failwithf "lex error %A" e

    let m =
        match parse token with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema, error = typeCheck (Dictionary()) m

    Assert.Empty error

    transform arch m sema

[<Fact>]
let Simple () = Assert.True(true)
