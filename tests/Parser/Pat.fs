module Parser.Tests.Pat

open Parser.Parser

open Snapper
open Xunit

let parseTest = Util.makeTest parsePat

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
