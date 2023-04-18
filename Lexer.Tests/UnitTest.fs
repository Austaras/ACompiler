module Lexer.Tests

open NUnit.Framework
open Lexer.Lexer

[<Test>]
let PairOfParen () =
    Assert.AreEqual(lex "()", [| Paren Open; Paren Close |])

