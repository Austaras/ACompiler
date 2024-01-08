module Parser.Tests.Pat

open Xunit

open Snapshot
open AST.Dump
open Parser.Pat

let parseTest = Util.makeTest parsePatInner pat

let snap = Snapshot("snap")

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Pat"

[<Theory>]
[<InlineData("Enum", "core::Option::Some(1)")>]
[<InlineData("Struct", "pak::Foo { v, x: 10, .. }")>]

[<InlineData("Compound",
             "Person {
    car: Some(_),
    age: 13..19 as person,
    name: person_name,
    ..
}")>]
let Binary (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/ADT/{name}"

[<Theory>]
[<InlineData("CatchAll", "..")>]
[<InlineData("Left", "A..")>]
[<InlineData("Right", "..10")>]
let Range (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Range/{name}"

[<Fact>]
let Assoc () =
    let res = parseTest "1 as a as b | d"
    snap.ShouldMatchText res $"{basePath}/AsOr"
