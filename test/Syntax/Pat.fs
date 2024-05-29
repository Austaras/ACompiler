module Parser.Tests.Pat

open System.IO

open Xunit

open Snapshot
open Syntax.Dump
open Syntax.Util
open Syntax.Lexer
open Syntax.Parser

let internal parseTest input (tw: TextWriter) =
    let error = ResizeArray()
    let lexer = Lexer(input, error)
    let parser = Parser(lexer, error, Context.Normal)
    let dump = Dump(tw)

    let p = parser.Pat()

    dump.Pat p

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Pat/"
let snap = TextSnapshot("snap", basePath)

[<Theory>]
[<InlineData("Enum", "core::Option::Some(1)")>]
[<InlineData("Struct", "pak::Foo { v, x: 10, }")>]

[<InlineData("Compound",
             "Person {
    car: Some(_),
    age: 13..19 as person,
    name: person_name,
}")>]
let ADT (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatch res $"ADT/{name}"

[<Theory>]
[<InlineData("CatchAll", "..")>]
[<InlineData("Left", "A..")>]
[<InlineData("Right", "..10")>]
let Range (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatch res $"Range/{name}"

[<Fact>]
let AsOr () =
    let res = parseTest "1 as a as b | d"
    snap.ShouldMatch res $"AsOr"

[<Fact>]
let OrAs () =
    let res = parseTest "a | b as c"
    snap.ShouldMatch res $"OrAs"
