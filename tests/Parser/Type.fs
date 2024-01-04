module Parser.Tests.Type

open Xunit

open Snapshot
open AST.Dump
open Parser.Type

let dump ast =
    use sw = new System.IO.StringWriter()
    ty sw 0 ast
    sw.ToString()

let parseTest = Util.makeTest parseType dump

let snap = Snapshot("snap")

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Type"

[<Theory>]
[<InlineData("Assoc", "|i32| -> |i32| -> i32")>]
[<InlineData("Empty", "|| -> !")>]

[<InlineData("MultiBound", "<T : Add + Sub>| T, T | -> T")>]
let Fn (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Fn/{name}"

[<Theory>]
[<InlineData("Shl", "pak::vec::Vec<<T>|T|->i32>")>]
[<InlineData("Const", "Container<-1>")>]
[<InlineData("Self", "Self::Output")>]
let Path (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Path/{name}"

[<Theory>]
[<InlineData("Slice", "&[&[i32];4]")>]
[<InlineData("Ref", "&&[uint]")>]
let Arr (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Arr/{name}"
