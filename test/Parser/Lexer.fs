module Parser.Tests.Lexer

open Xunit
open Common.Span
open AST.AST
open Parser.Lexer

exception CustomError of Error[]

let lex_strip_span =
    lex
    >> (fun r ->
        match r with
        | Ok d -> d
        | Error e -> raise (CustomError e))
    >> Array.map _.Data

[<Fact>]
let Pair () =
    Assert.Equivalent([| Paren Open; Paren Close |], lex_strip_span "()")
    Assert.Equivalent([| Bracket Open; Bracket Close |], lex_strip_span "[]")
    Assert.Equivalent([| Curly Open; Curly Close |], lex_strip_span "{}")

[<Fact>]
let Literal () =
    Assert.Equivalent([| Lit(String "abcdefg") |], lex_strip_span "\"abcdefg\"")
    Assert.Equivalent([| Lit(String "\n\r\t") |], lex_strip_span "\"\\n\\r\\t\"")

    Assert.Equivalent([| Lit(Char 'a') |], lex_strip_span "\'a\'")

    Assert.Equivalent([| Lit(Bool true) |], lex_strip_span "true")

    Assert.Equivalent([| Lit(Int 123UL) |], lex_strip_span "123")
    Assert.Equivalent([| Lit(Int 0UL) |], lex_strip_span "0000")
    Assert.Equivalent([| Lit(Int 0UL) |], lex_strip_span "0_0_0")
    Assert.Equivalent([| Lit(Int 0UL) |], lex_strip_span "0 ")
    Assert.Equivalent([| Lit(Int 256UL) |], lex_strip_span "0x100")
    Assert.Equivalent([| Lit(Float 123) |], lex_strip_span "123.")
    Assert.Equivalent([| Lit(Float 1.23e9) |], lex_strip_span ".123e1_0")
    Assert.Equivalent([| Lit(Float 1e-16) |], lex_strip_span "1E-16")
    Assert.Equivalent([| Lit(Float 1e16) |], lex_strip_span "01E+1_6")
    Assert.Equivalent([| Lit(Float 0) |], lex_strip_span "0e999")
    Assert.Equivalent([| Lit(Float 5.047e9) |], lex_strip_span "005047e+6")
    Assert.Equivalent([| Identifier "_123" |], lex_strip_span "_123")
    Assert.Equivalent([| Lit(Int 123UL) |], lex_strip_span "123_")

[<Fact>]
let If () =
    Assert.Equivalent(
        [| Reserved IF
           Lit(Bool true)
           Curly Open
           Lit(Int 1UL)
           Curly Close
           Reserved ELSE
           Curly Open
           Lit(Int 2UL)
           Curly Close |],
        lex_strip_span "if true { 1 } else { 2 }"
    )

[<Fact>]
let NumDot () =
    Assert.Equivalent(
        [| Lit(Int 0UL); Dot; Identifier "max"; Paren Open; Lit(Int 1UL); Paren Close |],
        lex_strip_span "0.max(1)"
    )

    Assert.Equivalent([| Lit(Int 0UL); DotDot; Lit(Int 1UL) |], lex_strip_span "0..1")

[<Fact>]
let Op () =
    Assert.Equivalent([| Operator(Arith Shl) |], lex_strip_span "<<")
    Assert.Equivalent([| Arrow; FatArrow |], lex_strip_span "-> =>")

    Assert.Equivalent(
        [| Lit(Int 1UL); Operator(Arith Add); Operator(Arith Sub); Lit(Int 1UL) |],
        lex_strip_span "1 +- 1"
    )

    Assert.Equivalent([| Identifier "a"; AssignOp(BitOr); Lit(Bool true) |], lex_strip_span "a |= true")

[<Fact>]
let Composite () =
    Assert.Equivalent([| Paren Open; Identifier "a"; Comma; Identifier "b"; Paren Close |], lex_strip_span "(a, b)")

    Assert.Equivalent(
        [| Identifier "Op"
           ColonColon
           Identifier "Add"
           Paren Open
           Lit(Int 1UL)
           Paren Close |],
        lex_strip_span "Op::Add(1)"
    )

[<Fact>]
let Comment =
    Assert.Equivalent(
        [| Identifier "aaa"; Comment(SingleLine, " single comment a + b") |],
        lex_strip_span "aaa // single comment a + b"
    )

    Assert.Equivalent(
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

[<Fact>]
let Error () =
    let test input =
        fun () -> (lex_strip_span input |> ignore)

    let e = Assert.Throws<CustomError>(test "\"")
    Assert.Equal(Unmatched(Span.Make 0 0, '"'), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "\'123\'")
    Assert.Equal(CharTooMany(Span.Make 0 4), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "1e")
    Assert.Equal(MissingExpContent(Span.Make 0 1), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "0.e+")
    Assert.Equal(MissingExpContent(Span.Make 0 3), e.Data0[0])

    let e = Assert.Throws<CustomError>(test "0x")
    Assert.Equal(MissingIntContent(Span.Make 0 1), e.Data0[0])
