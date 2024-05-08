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

fn test(n) {
    n.foo()
    n == 1
}"
    |> toBe (Map [| "test", "|int| -> bool" |])

[<Fact>]
let Poly () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

fn test(n) {
    n.foo()
}"
    |> toBe (Map [| "test", "<T0>|T0| -> ()" |])
