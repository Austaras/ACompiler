module Parser.Tests.Type

open Lexer
open Parser.Parser

open NUnit.Framework
open Snapper.Nunit

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parseType Context.Normal token with
        | Ok ast -> ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Test>]
let Fn () =
    Assert.That(parseTest "|i32| -> |i32| -> i32", Matches.ChildSnapshot("Assoc"))
    Assert.That(parseTest "|| -> !", Matches.ChildSnapshot("Empty"))

[<Test>]
let Inst () =
    Assert.That(parseTest "std::collections::HashMap<i32, Vec<i32>>", Matches.ChildSnapshot("Shr"))
    Assert.That(parseTest "pak::vec::Vec<<T>|T|->i32>", Matches.ChildSnapshot("Shl"))

[<Test>]
let Arr () =
    Assert.That(parseTest "&[&[i32];4]", Matches.ChildSnapshot("Slice"))
    Assert.That(parseTest "&&[usize]", Matches.ChildSnapshot("Ref"))

[<Test>]
let Const () =
    Assert.That(parseTest "Container<-1>", Matches.ChildSnapshot("Neg"))
