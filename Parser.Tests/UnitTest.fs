module Parser.Tests

open AST.AST
open Lexer
open Parser

open NUnit.Framework
open Snapper.Nunit

exception CustomError of (Span * string)[]

let parse_test input =
    match Lexer.lex input with
    | Ok token ->
        match parse token with
        | Ok ast -> ast
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError e)

[<Test>]
let If () =
    Assert.That(parse_test "if true { 1 } else { 2 }", Matches.Snapshot())
