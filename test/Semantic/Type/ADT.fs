module Semantic.Tests.Type.ADT

open Xunit

open Common

[<Fact>]
let Stru () =
    runInfer
        "
struct Point {
    x: int,
    y: int
}

struct Point3D {
    x: int,
    y: int,
    z: int
}

fn add(p) {
    p.x + p.y + p.z
}"
    |> toBe (Map [| "add", "|Point3D| -> int" |])

[<Fact>]
let AutoDeref () =
    runInfer
        "
struct Foo {
    b: &Bar
}

struct Bar {
    f: &Foo
}

fn foo(f) {
    f.b.f
}"
    |> toBe (Map [| "foo", "|Foo| -> &Foo" |])

[<Fact>]
let DerefParam () =
    runInfer
        "
struct Foo {
    b: uint
}

fn foo(f: &Foo) {
    f.b
}"
    |> toBe (Map [| "foo", "|&Foo| -> uint" |])

[<Fact>]
let Tuple () =
    runInfer
        "
fn foo((a, b, c)) {
    a == 1 && b == 2 && c == 3
}"
    |> toBe (Map [| "foo", "|(int, int, int)| -> bool" |])


[<Fact>]
let Infer () =
    runInfer
        "
struct Foo<T> {
    f: T
}

fn foo(f: Foo<_>) -> uint {
    f.f
}"
    |> toBe (Map [| "foo", "|Foo<uint>| -> uint" |])

[<Fact>]
let Reference () =
    runInfer "fn deref(a) { *a + 1 }" |> toBe (Map [| "deref", "|&int| -> int" |])

[<Fact>]
let RefField () =
    runInfer
        "
struct Foo {
    f: uint
}

fn get_f(f) { &f.f }"
    |> toBe (Map [| "get_f", "|Foo| -> &uint" |])

[<Fact>]
let GenericStruct () =
    runInfer
        "
struct Foo<T> {
    f: T
}

fn new_foo() { Foo { f: 1 } }"
    |> toBe (Map [| "new_foo", "|| -> Foo<int>" |])

[<Fact>]
let Slice () =
    runInfer
        "
fn head(a) { a[0] }"
    |> toBe (Map [| "head", "<T0>|[T0]| -> T0" |])
