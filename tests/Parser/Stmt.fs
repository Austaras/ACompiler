module Parser.Tests.Stmt

open Lexer
open Parser.Parser

open FSharp.Json
open Snapper
open Xunit

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parseDecl Context.Normal token with
        | Ok ast -> Json.serialize ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Fact>]
let Decl () =
    (parseTest
        "
        fn add<T: Add>(x: T, y: T) -> T {
            x + y
        }
    ")
        .ShouldMatchChildSnapshot("function")

    (parseTest
        "
        let _ = {
            let mut a = 10;
            print(a);
            a
        }
    ")
        .ShouldMatchChildSnapshot("Let")

    (parseTest
        "
        enum Option<T> {
            Some(T),
            None
        }
    ")
        .ShouldMatchChildSnapshot("Enum")
