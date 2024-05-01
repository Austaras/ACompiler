module Semantic.Tests.Type.Trait

open Xunit

open Common

[<Fact>]
let Basic () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

impl Foo for int {
    fn foo(self) {}
}

fn test(n: int) {
    n.foo()
}"
    |> toBe (Map [| "test", "|int| -> ()" |])
