module Parser.Tests.Type

open Lexer
open Parser.Parser

open Xunit
open Snapper

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parseType Context.Normal token with
        | Ok ast -> ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Fact>]
let Fn () =
    (parseTest "|i32| -> |i32| -> i32").ShouldMatchChildSnapshot("Assoc")
    (parseTest "|| -> !").ShouldMatchChildSnapshot("Empty")

[<Fact>]
let Inst () =
    (parseTest "std::collections::HashMap<i32, Vec<i32>>")
        .ShouldMatchChildSnapshot("Shr")

    (parseTest "pak::vec::Vec<<T>|T|->i32>").ShouldMatchChildSnapshot("Shl")

[<Fact>]
let Arr () =
    (parseTest "&[&[i32];4]").ShouldMatchChildSnapshot("Slice")
    (parseTest "&&[usize]").ShouldMatchChildSnapshot("Ref")

[<Fact>]
let Const () =
    (parseTest "Container<-1>").ShouldMatchChildSnapshot("Neg")
