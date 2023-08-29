module Parser.Tests.Type

open Parser.Type
open Parser.Stmt

open Snapper
open Xunit

let parseTest = Util.makeTest parseType

[<Fact>]
let Fn () =
    (parseTest "|i32| -> |i32| -> i32").ShouldMatchChildSnapshot("Assoc")
    (parseTest "|| -> !").ShouldMatchChildSnapshot("Empty")

    (parseTest "<T : Add + Sub>| T, T | -> T")
        .ShouldMatchChildSnapshot("MultiBound")

[<Fact>]
let Path () =
    (parseTest "std::collections::HashMap<i32, Vec<i32>>")
        .ShouldMatchChildSnapshot("Shr")

    (parseTest "pak::vec::Vec<<T>|T|->i32>").ShouldMatchChildSnapshot("Shl")

    (parseTest "Container<-1>").ShouldMatchChildSnapshot("Const")

    (parseTest "Self::Output").ShouldMatchChildSnapshot("Self")

[<Fact>]
let Arr () =
    (parseTest "&[&[i32];4]").ShouldMatchChildSnapshot("Slice")
    (parseTest "&&[usize]").ShouldMatchChildSnapshot("Ref")
