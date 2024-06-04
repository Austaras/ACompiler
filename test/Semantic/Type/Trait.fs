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
    |> toBe (Map [| "test", "<T0>|T0| -> () where T0: Foo" |])

[<Fact>]
let Super () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

trait Bar : Foo {
    fn bar(self)
}

impl Foo for int {
    fn foo(self) {}
}

impl Bar for int {
    fn bar(self) {}
}

fn test(a: int) {
    a.bar()
}"
    |> toBe (Map [| "test", "|int| -> ()" |])

[<Fact>]
let SuperGeneric () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

trait Bar : Foo {
    fn bar(self)
}

fn test<T: Bar>(a: T) {
    a.foo()
}"
    |> toBe (Map [| "test", "<T>|T| -> () where T: Bar" |])

[<Fact>]
let Bound () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

impl Foo for int {
    fn foo(self) {}
}

impl <T: Foo, U: Foo> Foo for (T, U) {
    fn foo(self) {}
}

fn test() {
    (1, (1, 2)).foo()
}"
    |> toBe (Map [| "test", "|| -> ()" |])

[<Fact>]
let TuplePred () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

impl <T> Foo for (T, T) {
    fn foo(self) {}
}

fn test(a, b) {
    (a, b).foo()
}

fn main() {
    test(1, 1)
}
"
    |> toBe (Map [| "test", "<T0, T1>|T0, T1| -> () where (T0, T1): Foo" |])

[<Fact>]
let SimplifyByInst () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

impl <T: Foo> Foo for (T, T) {
    fn foo(self) {}
}

fn test(a) {
    (a, a).foo()
}"
    |> toBe (Map [| "test", "<T0>|T0| -> () where T0: Foo" |])

[<Fact>]
let SimplifyBySuper () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

trait Bar: Foo {
    fn bar(self)
}

fn test(a) {
    a.foo()
    a.bar()
}"
    |> toBe (Map [| "test", "<T0>|T0| -> () where T0: Bar" |])

[<Fact>]
let Self () =
    runInfer
        "
trait Id {
    fn id(self) -> Self
}

impl Id for int {
    fn id(self) -> Self {
        self
    }
}

fn test(i: int) {
    i.id()
}"
    |> toBe (Map [| "test", "|int| -> int" |])
