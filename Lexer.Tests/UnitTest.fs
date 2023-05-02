module Lexer.Tests

open NUnit.Framework
open AST.AST
open Lexer

exception CustomError of Error[]

let lex_strip_span =
    lex
    >> (fun r ->
        match r with
        | Ok d -> d
        | Error e -> raise (CustomError e))
    >> Array.map (fun t -> t.data)

[<Test>]
let Pair () =
    Assert.AreEqual([| Paren Open; Paren Close |], lex_strip_span "()")
    Assert.AreEqual([| Bracket Open; Bracket Close |], lex_strip_span "[]")
    Assert.AreEqual([| Curly Open; Curly Close |], lex_strip_span "{}")

[<Test>]
let Literal () =
    Assert.AreEqual([| Lit(String "abcdefg") |], lex_strip_span "\"abcdefg\"")
    Assert.AreEqual([| Lit(String "\n\r\t") |], lex_strip_span "\"\\n\\r\\t\"")

    Assert.AreEqual([| Lit(Char 'a') |], lex_strip_span "\'a\'")

    Assert.AreEqual([| Lit(Bool true) |], lex_strip_span "true")

    Assert.AreEqual([| Lit(Int 123u) |], lex_strip_span "123")
    Assert.AreEqual([| Lit(Int 0u) |], lex_strip_span "0000")
    Assert.AreEqual([| Lit(Int 0u) |], lex_strip_span "0_0_0")
    Assert.AreEqual([| Lit(Int 256u) |], lex_strip_span "0x100")
    Assert.AreEqual([| Lit(Float 123) |], lex_strip_span "123.")
    Assert.AreEqual([| Lit(Float 0.123) |], lex_strip_span ".123")
    Assert.AreEqual([| Lit(Float 1.23e9) |], lex_strip_span ".123e10")
    Assert.AreEqual([| Lit(Float 1e-16) |], lex_strip_span "1E-16")
    Assert.AreEqual([| Lit(Float 1e16) |], lex_strip_span "01E+1_6")
    Assert.AreEqual([| Lit(Float 0) |], lex_strip_span "0e999")
    Assert.AreEqual([| Lit(Float 5.047e9) |], lex_strip_span "005047e+6")
    Assert.AreEqual([| Identifier "_123" |], lex_strip_span "_123")
    Assert.AreEqual([| Lit(Int 123u) |], lex_strip_span "123_")

[<Test>]
let If () =
    Assert.AreEqual(
        [| Reserved IF
           Lit(Bool true)
           Curly Open
           Lit(Int 1u)
           Curly Close
           Reserved ELSE
           Curly Open
           Lit(Int 2u)
           Curly Close |],
        lex_strip_span "if true { 1 } else { 2 }"
    )

[<Test>]
let NumDot () =
    Assert.AreEqual(
        [| Lit(Int 0u); Dot; Identifier "max"; Paren Open; Lit(Int 1u); Paren Close |],
        lex_strip_span "0.max(1)"
    )

    Assert.AreEqual([| Lit(Int 0u); DotDot; Lit(Int 1u) |], lex_strip_span "0..1")

[<Test>]
let Op () =
    Assert.AreEqual([| Operator(Arithmetic Shr) |], lex_strip_span ">>")
    Assert.AreEqual([| Arrow; FatArrow |], lex_strip_span "-> =>")

    Assert.AreEqual(
        [| Lit(Int 1u)
           Operator(Arithmetic Add)
           Operator(Arithmetic Sub)
           Lit(Int 1u) |],
        lex_strip_span "1 +- 1"
    )

    Assert.AreEqual([| Identifier "a"; AssignOp(LogicalOr); Lit(Bool true) |], lex_strip_span "a ||= true")

[<Test>]
let Composite () =
    Assert.AreEqual([| Paren Open; Identifier "a"; Comma; Identifier "b"; Paren Close |], lex_strip_span "(a, b)")

    Assert.AreEqual(
        [| Identifier "Op"
           ColonColon
           Identifier "Add"
           Paren Open
           Lit(Int 1u)
           Paren Close |],
        lex_strip_span "Op::Add(1)"
    )

[<Test>]
let Comment =
    Assert.AreEqual(
        [| Identifier "aaa"; Comment(SingleLine, " single comment a + b") |],
        lex_strip_span "aaa // single comment a + b"
    )

    Assert.AreEqual(
        [| Comment(
               MultiLine,
               "
          a multiline comment
        "
           ) |],
        lex_strip_span
            "/*
          a multiline comment
        */"
    )

[<Test>]
let Error () =
    let test input =
        fun () -> (lex_strip_span input |> ignore)

    let e = Assert.Throws<CustomError>(test "\"")
    Assert.AreEqual(Unmatched(Span.Make 0 0, '"'), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "\'123\'")
    Assert.AreEqual(CharTooMany(Span.Make 0 4), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "1e")
    Assert.AreEqual(MissingExpContent(Span.Make 0 1), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "0.e+")
    Assert.AreEqual(MissingExpContent(Span.Make 0 3), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "0d")
    Assert.AreEqual(UnknownNumberPrefix(Span.Make 0 1, 'd'), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "0x")
    Assert.AreEqual(MissingIntContent(Span.Make 0 1), e.Data0[0])
