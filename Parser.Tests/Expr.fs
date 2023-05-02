module Parser.Tests

open Lexer
open Parser

open NUnit.Framework
open Snapper.Nunit

exception CustomError of (Parser.Error)[]

let parse_test input =
    match Lexer.lex input with
    | Ok token ->
        match parse_expr Context.Normal token with
        | Ok ast -> ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

// [<Test>]
// let If () =
//     Assert.That(parse_test "if true { 1 } else { 2 }", Matches.Snapshot())

[<Test>]
let Bin () =
    Assert.That(parse_test "1 + 2 * 3", Matches.ChildSnapshot("Binary"))
    Assert.That(parse_test "3 - 2 - 1", Matches.ChildSnapshot("Assoc"))
    Assert.That(parse_test "a + b == c + d", Matches.ChildSnapshot("Compare"))

    Assert.That(parse_test "a = b = c", Matches.ChildSnapshot("RightAssoc"))

    Assert.That(parse_test "(1 + 2) * 3", Matches.ChildSnapshot("Paren"))
    Assert.That(parse_test "((((1 + 2))) * (3))", Matches.ChildSnapshot("ManyParen"))

    Assert.That(
        parse_test
            "1 + // comment
    2",
        Matches.ChildSnapshot("Comment")
    )
