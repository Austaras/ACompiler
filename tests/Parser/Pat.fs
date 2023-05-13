module Parser.Tests.Pat

open Lexer
open Parser.Parser

open NUnit.Framework
open Snapper.Nunit

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parsePat Context.Normal token with
        | Ok ast -> ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Test>]
let StructEnum () =
    Assert.That(parseTest "core::Option::Some(1)", Matches.ChildSnapshot("Enum"))
    Assert.That(parseTest "pak::Foo { v, x: 10, ..}", Matches.ChildSnapshot("Struct"))

    Assert.That(
        parseTest
            "Person {
        car: Some(_),
        age: 13..19 as person,
        name: person_name,
        ..
    }",
        Matches.ChildSnapshot("Compound")
    )

[<Test>]
let Range () =
    Assert.That(parseTest "..", Matches.ChildSnapshot("CatchAll"))
    Assert.That(parseTest "A..", Matches.ChildSnapshot("Left"))
    Assert.That(parseTest "..10", Matches.ChildSnapshot("Right"))

[<Test>]
let Assoc () =
    Assert.That(parseTest "1 as a as b | d", Matches.ChildSnapshot("AsOr"))
