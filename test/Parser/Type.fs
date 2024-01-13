module Parser.Tests.Type

open System.IO

open Xunit

open Snapshot
open AST.Dump
open Parser.Lexer
open Parser.Parser

let internal parseTest input (tw: TextWriter) =
    let error = ResizeArray()
    let lexer = Lexer(input, error)
    let parser = Parser(lexer, error)
    let dump = Dump(tw)

    let e = parser.Type()

    dump.Type e

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Type/"
let snap = TextSnapshot("snap", basePath)

[<Theory>]
[<InlineData("Assoc", "|i32| -> |i32| -> i32")>]
[<InlineData("Empty", "|| -> !")>]
let Fn (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatch res $"Fn/{name}"

[<Theory>]
[<InlineData("Const", "Container<-1>")>]
[<InlineData("Self", "Self::Output")>]
let Path (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatch res $"Path/{name}"

[<Theory>]
[<InlineData("Slice", "&[&[i32];4]")>]
[<InlineData("Ref", "&&[uint]")>]
let Arr (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatch res $"Arr/{name}"
