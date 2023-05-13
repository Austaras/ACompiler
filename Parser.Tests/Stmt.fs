module Parser.Tests.Stmt

open Lexer
open Parser.Parser

open NUnit.Framework
open Snapper.Nunit

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parseDecl Context.Normal token with
        | Ok ast -> ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Test>]
let Decl () =
    Assert.That(
        parseTest
            "
        fn add<T: Add>(x: T, y: T) -> T {
            x + y
        }
    ",
        Matches.ChildSnapshot("function")
    )

    Assert.That(
        parseTest
            "
        let _ = {
            let a = 10;
            print(a);
            a
        }
    ",
        Matches.ChildSnapshot("Let")
    )
