module Semantic.Tests.Type.Trait

open Xunit

open Common

[<Fact>]
let Basic () =
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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
    runAnalysis
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

[<Fact>]
let BadCollect () =
    runAnalysis
        "
trait Collect<C> {
    fn insert(self, value: C)
}

fn twice(c, a, b) {
    c.insert(a)
    c.insert(b)
}"
    |> toBe (Map [| "twice", "<T0, T1, T2>|T0, T1, T2| -> () where T0: Collect<T1> + Collect<T2>" |])

[<Fact>]
let GoodCollect () =
    runAnalysis
        "
trait Collect {
    type C
    fn insert(self, value: C)
}

fn twice(c, a, b) {
    c.insert(a)
    c.insert(b)
}"
    |> toBe (Map [| "twice", "<T0, T1>|T0, T1, T1| -> () where T0: Collect<C = T1>" |])

[<Fact>]
let PolyAdd () =
    runAnalysis
        "
trait Add<Rhs> {
    fn add(self, rhs: Rhs) -> Self
}

impl Add<int> for int {
    fn add(self, rhs: int) -> i64 {
        self
    }
}

fn add(a: int) {
    a.add(a)
}

fn add_poly(a: int, b) {
    a.add(b)
}

fn main() {
    add_poly(1, 2)
}"
    |> toBe (
        Map
            [| "add", "|int| -> int"
               "add_poly", "<T0>|int, T0| -> int where int: Add<T0>" |]
    )

[<Fact>]
let AddDep () =
    runAnalysis
        "
trait Add {
    type Res
    fn add(self, rhs: Self) -> Res
}

impl Add for int {
    type Res = int

    fn add(self, rhs: Self) -> Res {
        self
    }
}

fn add(a: int, b) {
    a.add(b)
}

fn add_infer(a) {
    a.add(1)
}"
    |> toBe (Map [| "add", "|int, int| -> int" |])
