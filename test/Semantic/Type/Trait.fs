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
    |> toBe (Map [| "test", "<T>|T| -> ()" |])

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
    (1, 2).foo()
}"
    |> toBe (Map [| "test", "|| -> ()" |])

[<Fact>]
let Enum () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

impl Foo for int {
    fn foo(self) {}
}

enum Bar<T: Foo> { A(T), B }

fn test(a: int) {
    A(a)
}"
    |> toBe (Map [| "test", "|int| -> Bar<int>" |])

[<Fact>]
let Subst () =
    runInfer
        "
trait Foo {
    fn foo(self)
}

impl Foo for int {
    fn foo(self) {}
}

impl <T: Foo> Foo for (int, T) {
    fn foo(self) {}
}

fn test(a) {
    (a, a).foo()
}"
    |> toBe (Map [| "test", "<T1>|T1| -> ()" |])
