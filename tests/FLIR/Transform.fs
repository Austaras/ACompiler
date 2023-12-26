module FLIR.Tests.Transform

open System.Collections.Generic

open Xunit
open Snapper

open Parser.Lexer
open Parser.Parser
open Semantic.Check
open FLIR.Transform

let arch = Common.Target.X86_64

let runTansform input =
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
let Simple () =
    let ir =
        runTansform
            "
fn arith(x, y) {
    let z = 2 * x
    (y + 3 + z) * z
}
"

    let ir = ir.ToString

    Assert.Equal(
        "fn (x: i64, y: i64) -> i64 {
    '0: {
        z = 2 * x
        _4 = y + 3
        _5 = _4 + z
        _0 = _5 * z
        ret _0
    }
}",
        ir
    )

[<Fact>]
let Condition () =
    let ir =
        runTansform
            "
fn limit(n) {
    if n > 10 {
        n - 10
    } else {
        n
    }
}
"

    let ir = ir.ToString

    Assert.Equal(
        "fn (n: i64) -> i64 {
    '0: {
        _2 = n > 10
        br _2 ? '2 : '1
    }
    '1: {
        _0 = n
        jmp '3
    }
    '2: {
        _0 = n - 10
        jmp '3
    }
    '3: {
        ret _0
    }
}",
        ir
    )

[<Fact>]
let Loop () =
    let ir =
        runTansform
            "
fn sum(n) {
    let mut i = 0
    let mut sum = 0

    while i < n {
        sum += i
        i += 1
    }

    sum
}
"

    let ir = ir.ToString

    Assert.Equal(
        "fn (n: i64) -> i64 {
    '0: {
        i = 0
        sum = 0
        jmp '1
    }
    '1: {
        _4 = i < n
        br _4 ? '2 : '3
    }
    '2: {
        sum = sum + i
        i = i + 1
        jmp '1
    }
    '3: {
        _0 = sum
        ret _0
    }
}",
        ir
    )
