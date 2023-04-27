module Lexer.Tests

open NUnit.Framework
open AST.AST
open Lexer

exception CustomError of (Span * string)[]

let lex_strip_span =
    lex
    >> (fun r ->
        match r with
        | Ok d -> d
        | Error e -> raise (CustomError e))
    >> Array.map (fun t -> t.data)

[<Test>]
let Pair () =
    Assert.AreEqual(lex_strip_span "()", [| Paren Open; Paren Close |])
    Assert.AreEqual(lex_strip_span "[]", [| Bracket Open; Bracket Close |])
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
    Assert.AreEqual(lex_strip_span "01E+1_6", [| Lit(Float 1e16) |])
    Assert.AreEqual(lex_strip_span "0e999", [| Lit(Float 0) |])
    Assert.AreEqual(lex_strip_span "005047e+6", [| Lit(Float 5.047e9) |])
    Assert.AreEqual(lex_strip_span "_123", [| Identifier "_123" |])
    Assert.AreEqual(lex_strip_span "123_", [| Lit(Int 123u) |])

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
    Assert.AreEqual(lex_strip_span ">>", [| Binary(Arithmetic Shr) |])
    Assert.AreEqual(lex_strip_span "-> =>", [| Arrow; FatArrow |])

    Assert.AreEqual(
        lex_strip_span "1 +- 1",
        [| Lit(Int 1u); Binary(Arithmetic Add); Binary(Arithmetic Sub); Lit(Int 1u) |]
    )

    Assert.AreEqual(lex_strip_span "a ||= true", [| Identifier "a"; Assign(LogicalOr); Lit(Bool true) |])

[<Test>]
let Composite () =
    Assert.AreEqual(lex_strip_span "(a, b)", [| Paren Open; Identifier "a"; Comma; Identifier "b"; Paren Close |])

    Assert.AreEqual(
        lex_strip_span "Op::Add(1)",
        [| Identifier "Op"
           ColonColon
           Identifier "Add"
           Paren Open
           Lit(Int 1u)
           Paren Close |]
    )

[<Test>]
let Comment =
    Assert.AreEqual(
        lex_strip_span "aaa // single comment a + b",
        [| Identifier "aaa"; Comment(SingleLine, " single comment a + b") |]
    )

    Assert.AreEqual(
        lex_strip_span
            "/*
          a multiline comment
        */",
        [| Comment(
               MultiLine,
               "
          a multiline comment
        "
           ) |]
    )


[<Test>]
let Error () =
    let test input =
        fun () -> (lex_strip_span input |> ignore)

    let e = Assert.Throws<CustomError>(test "\"")
    Assert.AreEqual(snd e.Data0[0], "unmatched double quote")

    let e = Assert.Throws<CustomError>(test "\'123\'")
    Assert.AreEqual(snd e.Data0[0], "char can only contain one character")

    let e = Assert.Throws<CustomError>(test "1e")
    Assert.AreEqual(snd e.Data0[0], "missing exponent")

    let e = Assert.Throws<CustomError>(test "0.e+")
    Assert.AreEqual(snd e.Data0[0], "missing exponent")

    let e = Assert.Throws<CustomError>(test "0d")
    Assert.AreEqual(snd e.Data0[0], "unknown number literal prefix d")

    let e = Assert.Throws<CustomError>(test "0x")
    Assert.AreEqual(snd e.Data0[0], "missing number content")
