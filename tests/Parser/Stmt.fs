module Parser.Tests.Stmt

open Parser.Stmt

open Snapper
open Xunit

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

    (parseTest
        "
        impl<T> Vec<T> {
            pub fn push(&self, element: T) {}
        }
    ")
        .ShouldMatchChildSnapshot("Impl")

    (parseTest
        "
        trait Summary {
            fn summarize(&self) -> String;
        }
        ")
        .ShouldMatchChildSnapshot("Trait")
