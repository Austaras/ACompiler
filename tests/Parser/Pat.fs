module Parser.Tests.Pat

open Lexer
open Parser.Parser

open FSharp.Json
open Snapper
open Xunit

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parsePat Context.Normal token with
        | Ok ast -> Json.serialize ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Fact>]
let StructEnum () =
    (parseTest "core::Option::Some(1)").ShouldMatchChildSnapshot("Enum")
    (parseTest "pak::Foo { v, x: 10, ..}").ShouldMatchChildSnapshot("Struct")

    (parseTest
        "Person {
        car: Some(_),
        age: 13..19 as person,
        name: person_name,
        ..
    }")
        .ShouldMatchChildSnapshot("Compound")


[<Fact>]
let Range () =
    (parseTest "..").ShouldMatchChildSnapshot("CatchAll")
    (parseTest "A..").ShouldMatchChildSnapshot("Left")
    (parseTest "..10").ShouldMatchChildSnapshot("Right")

[<Fact>]
let Assoc () =
    (parseTest "1 as a as b | d").ShouldMatchChildSnapshot("AsOr")
