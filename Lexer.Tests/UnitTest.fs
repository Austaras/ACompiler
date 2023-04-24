module Lexer.Tests

open NUnit.Framework
open AST.AST
open Lexer

let lex_strip_span =
    lex
    >> (fun r ->
        match r with
        | Ok d -> d
        | Error e -> failwith (snd e[0]))
    >> Array.map (fun t -> t.data)

[<Test>]
let Pair () =
    Assert.AreEqual(lex_strip_span "()", [| Paren Open; Paren Close |])
    Assert.AreEqual(lex_strip_span "{}", [| Curly Open; Curly Close |])

[<Test>]
let Literal () =
    Assert.AreEqual(lex_strip_span "\"abcdefg\"", [| Lit(String "abcdefg") |])
    Assert.AreEqual(lex_strip_span "\"\\n\\r\\t\"", [| Lit(String "\n\r\t") |])
    Assert.AreEqual(lex_strip_span "\'a\'", [| Lit(Char 'a') |])
    Assert.AreEqual(lex_strip_span "true", [| Lit(Bool true) |])
    Assert.AreEqual(lex_strip_span "123", [| Lit(Int 123u) |])
    Assert.AreEqual(lex_strip_span "0000", [| Lit(Int 0u) |])
    Assert.AreEqual(lex_strip_span "0_0_0", [| Lit(Int 0u) |])
    Assert.AreEqual(lex_strip_span "0x100", [| Lit(Int 256u) |])
    Assert.AreEqual(lex_strip_span "123.", [| Lit(Float 123) |])
    Assert.AreEqual(lex_strip_span ".123", [| Lit(Float 0.123) |])
    Assert.AreEqual(lex_strip_span ".123e10", [| Lit(Float 1.23e9) |])
    Assert.AreEqual(lex_strip_span "1E-16", [| Lit(Float 1e-16) |])
    Assert.AreEqual(lex_strip_span "005047e+6", [| Lit(Float 5.047e9) |])

[<Test>]
let If () =
    Assert.AreEqual(
        lex_strip_span "if true { 1 } else { 2 }",
        [| Reserved IF
           Lit(Bool true)
           Curly Open
           Lit(Int 1u)
           Curly Close
           Reserved ELSE
           Curly Open
           Lit(Int 2u)
           Curly Close |]
    )

[<Test>]
let NumDot () =
    Assert.AreEqual(
        lex_strip_span "0.max(1)",
        [| Lit(Int 0u); Dot; Identifier "max"; Paren Open; Lit(Int 1u); Paren Close |]
    )

    Assert.AreEqual(lex_strip_span "0..1", [| Lit(Int 0u); DotDot; Lit(Int 1u) |])

[<Test>]
let Op () =
    Assert.AreEqual(lex_strip_span ">>>", [| Operator ">>>" |])
    Assert.AreEqual(lex_strip_span "1 + 1", [| Lit(Int 1u); Operator "+"; Lit(Int 1u) |])
