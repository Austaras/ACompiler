module Parser.Tests.Stmt

open Parser.Parser

open Snapper
open Xunit

exception CustomError of Error[]

let parseTest = Util.makeTest parseDecl

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
