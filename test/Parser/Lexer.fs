module Parser.Tests.Lexer

open Xunit
open Common.Span
open AST.AST
open Parser.Common
open Parser.Lexer

let lexStripSpan input =
    let error = ResizeArray()
    let lexer = Lexer(input, error)

    lexer.AllToken() |> fst |> Array.map _.Data

[<Fact>]
let Pair () =
    Assert.Equivalent([| Open Paren; Close Paren |], lexStripSpan "()")
    Assert.Equivalent([| Open Bracket; Close Bracket |], lexStripSpan "[]")
    Assert.Equivalent([| Open Curly; Close Curly |], lexStripSpan "{}")

[<Fact>]
let Literal () =
    Assert.Equivalent([| Lit(String "abcdefg") |], lexStripSpan "\"abcdefg\"")
    Assert.Equivalent([| Lit(String "\n\r\t") |], lexStripSpan "\"\\n\\r\\t\"")

    Assert.Equivalent([| Lit(Char 'a') |], lexStripSpan "\'a\'")

    Assert.Equivalent([| Lit(Bool true) |], lexStripSpan "true")

    Assert.Equivalent([| Lit(Int 123UL) |], lexStripSpan "123")
    Assert.Equivalent([| Lit(Int 0UL) |], lexStripSpan "0000")
    Assert.Equivalent([| Lit(Int 0UL) |], lexStripSpan "0_0_0")
    Assert.Equivalent([| Lit(Int 0UL) |], lexStripSpan "0 ")
    Assert.Equivalent([| Lit(Int 256UL) |], lexStripSpan "0x100")
    Assert.Equivalent([| Lit(Float 123) |], lexStripSpan "123.")
    Assert.Equivalent([| Lit(Float 1.23e9) |], lexStripSpan ".123e1_0")
    Assert.Equivalent([| Lit(Float 1e-16) |], lexStripSpan "1E-16")
    Assert.Equivalent([| Lit(Float 1e16) |], lexStripSpan "01E+1_6")
    Assert.Equivalent([| Lit(Float 0) |], lexStripSpan "0e999")
    Assert.Equivalent([| Lit(Float 5.047e9) |], lexStripSpan "005047e+6")
    Assert.Equivalent([| Identifier "_123" |], lexStripSpan "_123")
    Assert.Equivalent([| Lit(Int 123UL) |], lexStripSpan "123_")

[<Fact>]
let If () =
    Assert.Equivalent(
        [| Reserved IF
           Lit(Bool true)
           Open Curly
           Lit(Int 1UL)
           Close Curly
           Reserved ELSE
           Open Curly
           Lit(Int 2UL)
           Close Curly |],
        lexStripSpan "if true { 1 } else { 2 }"
    )

[<Fact>]
let NumDot () =
    Assert.Equivalent(
        [| Lit(Int 0UL); Dot; Identifier "max"; Open Paren; Lit(Int 1UL); Close Paren |],
        lexStripSpan "0.max(1)"
    )

    Assert.Equivalent([| Lit(Int 0UL); DotDot; Lit(Int 1UL) |], lexStripSpan "0..1")

[<Fact>]
let Op () =
    Assert.Equivalent([| Operator(Arith Shl) |], lexStripSpan "<<")
    Assert.Equivalent([| Arrow; FatArrow |], lexStripSpan "-> =>")

    Assert.Equivalent([| Lit(Int 1UL); Operator(Arith Add); Operator(Arith Sub); Lit(Int 1UL) |], lexStripSpan "1 +- 1")

    Assert.Equivalent([| Identifier "a"; AssignOp(BitOr); Lit(Bool true) |], lexStripSpan "a |= true")

[<Fact>]
let Composite () =
    Assert.Equivalent([| Open Paren; Identifier "a"; Comma; Identifier "b"; Close Paren |], lexStripSpan "(a, b)")

    Assert.Equivalent(
        [| Identifier "Op"
           ColonColon
           Identifier "Add"
           Open Paren
           Lit(Int 1UL)
           Close Paren |],
        lexStripSpan "Op::Add(1)"
    )

[<Fact>]
let Comment =
    Assert.Equivalent(
        [| Identifier "aaa"; Comment(SingleLine, " single comment a + b") |],
        lexStripSpan "aaa // single comment a + b"
    )

    Assert.Equivalent(
        [| Comment(
               MultiLine,
               "
          a multiline comment
        "
           ) |],
        lexStripSpan
            "/*
          a multiline comment
        */"
    )

let lexError input =
    let error = ResizeArray()
    let lexer = Lexer(input, error)

    try
        lexer.AllToken() |> snd
    with ParserExp e ->
        [| e |]

[<Fact>]
let Error () =
    let e = lexError "\""
    Assert.Equal(Unmatched(Span.Make 0 0, '"'), e[0])

    let e = lexError "\'123\'"
    Assert.Equal(CharTooMany(Span.Make 0 4), e[0])

    let e = lexError "1e"
    Assert.Equal(MissingExpContent(Span.Make 0 1), e[0])

    let e = lexError "0.e+"
    Assert.Equal(MissingExpContent(Span.Make 0 3), e[0])

    let e = lexError "0x"
    Assert.Equal(MissingIntContent(Span.Make 0 1), e[0])
