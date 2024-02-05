module Semantic.Tests.Type

open System.Collections.Generic

open System.IO
open Xunit

open AST
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let runInfer input =
    let m =
        match parse input with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    match check (Dictionary()) m with
    | Ok sema ->
        let map (id: AST.Id, t: Scheme) = (id.Sym, t.Print())
        sema.Binding |> Seq.map (|KeyValue|) |> Seq.map map |> Map.ofSeq
    | Error e -> failwithf "type error %A" e

let runInferFromExample path =
    File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../example/" + path) |> runInfer

[<Fact>]
let Closure () =
    let mutualRec = runInferFromExample "function/mutual_rec.adf"
    Assert.Equal("|int| -> bool", mutualRec["is_even"])
    Assert.Equal("|int| -> bool", mutualRec["is_odd"])

    let closure = runInfer "fn call(c) { c(0) + 1 }"
    Assert.Equal("||int| -> int| -> int", closure["call"])

    let curry =
        runInfer
            "
fn equal(x) {
    |y| x == y
}"

    Assert.Equal("<Tx>|Tx| -> |Tx| -> bool", curry["equal"])

    let monoClosure =
        runInfer
            "
fn main() {
    let id = |x| x

    id(1)
}"

    Assert.Equal("|int| -> int", monoClosure["id"])

    let topLevel =
        runInfer
            "
fn foo() {
    f
}

let f = 1"

    Assert.Equal("|| -> int", topLevel["foo"])

    let ret =
        runInfer
            "
fn foo(i) {
    if i == 0 {
        return 0
    }

    i + 1
}"

    Assert.Equal("|int| -> int", ret["foo"])

    let never =
        runInfer
            "
fn foo(i) {
    let mut i = i

    while i > 0 {
        if i % 2 == 0 {
            return i / 2
        }

        i -= 1
    }
}"

    Assert.Equal("|int| -> int", never["foo"])

[<Fact>]
let Reference () =
    let reference = runInfer "fn deref(a) { *a + 1 }"
    Assert.Equal("|&int| -> int", reference["deref"])

    let refField =
        runInfer
            "
struct Foo {
    f: uint
}

fn get_f(f) { &f.f }"

    Assert.Equal("|Foo| -> &uint", refField["get_f"])

[<Fact>]
let ADT () =
    let stru = runInferFromExample "function/struct.adf"
    Assert.Equal("|Point3D| -> int", stru["add"])

    let autoDeref =
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

    Assert.Equal("|Foo| -> &Foo", autoDeref["foo"])

    let derefParam =
        runInfer
            "
    struct Foo {
        b: uint
    }

    fn foo(f: &Foo) {
        f.b
    }"

    Assert.Equal(derefParam["foo"], "|&Foo| -> uint")

    let tuple =
        runInfer
            "
fn foo((a, b, c)) {
    a == 1 && b == 2 && c == 3
}"

    Assert.Equal("|(int, int, int)| -> bool", tuple["foo"])

    let inferred =
        runInfer
            "
struct Foo<T> {
    f: T
}

fn foo(f: Foo<_>) -> uint {
    f.f
}"

    Assert.Equal("|Foo<uint>| -> uint", inferred["foo"])

[<Fact>]
let Poly () =
    let poly =
        runInfer
            "
fn id(x) { 
    x
}

fn main() {
    id(id)(id(0))
}"

    Assert.Equal("<Tx>|Tx| -> Tx", poly["id"])

    let hoistedMono =
        runInfer
            "
fn main() {
    one(1)
}

fn one(x) { 1 }"

    Assert.Equal("|int| -> int", hoistedMono["one"])

    let hoistedTyped =
        runInfer
            "
fn main() {
    id(1)
    let _ = id(true)
}

fn id<T>(x: T) -> T {
    x
}"

    Assert.Equal("<T>|T| -> T", hoistedTyped["id"])

    let recTyped =
        runInfer
            "
fn id<T>(x: T) -> T {
    let _ = id(1)
    let _ = id(true)
    x
}"

    Assert.Equal("<T>|T| -> T", recTyped["id"])

    let polyDouble = runInfer "fn double(f, x) { f(f(x)) }"
    Assert.Equal("<Tx>||Tx| -> Tx, Tx| -> Tx", polyDouble["double"])

    let polyDoubleCurly = runInfer "fn double(f) { |x| f(f(x)) }"
    Assert.Equal("<Tx>||Tx| -> Tx| -> |Tx| -> Tx", polyDoubleCurly["double"])

    let polyRec =
        runInfer
            "
fn foo(x) {
    bar(1)
    x
}

fn bar(x) {
    foo(1)
}"

    Assert.Equal("<Tx>|Tx| -> Tx", polyRec["foo"])
    Assert.Equal("|int| -> int", polyRec["bar"])

    let weirdRec = runInfer "fn weird_rec(x) { weird_rec(1) }"
    Assert.Equal("|int| -> !", weirdRec["weird_rec"])

    let explicit =
        runInfer
            "
pub fn swap<T1, T2>((fst, snd): (T1, T2)) -> (T2, T1) {
    (snd, fst)
}"

    Assert.Equal("<T1, T2>|(T1, T2)| -> (T2, T1)", explicit["swap"])

    let otherScope =
        runInfer
            "
fn former(x) {
    later(x)
}

fn later(x) {
    x
}"

    Assert.Equal("<Tx>|Tx| -> Tx", otherScope["former"])
    Assert.Equal("|Tx| -> Tx", otherScope["later"])

    let nested =
        runInfer
            "
fn outer(x) {
    fn inner(y) {
        outer(y) == y
    }

    x
}"

    Assert.Equal("<Tx>|Tx| -> Tx", nested["outer"])
    Assert.Equal("|Tx| -> bool", nested["inner"])

[<Fact>]
let Match () =
    // let fib = runInferFromExample "function/fib.adf"
    // Assert.Equal("|int| -> int", fib["fib"])

    let enum =
        runInfer
            "
enum Either<L, R> {
    L(L),
    R(R)
}

fn is_zero(e) {
    match e {
        L(i) => i == 0,
        R(f) => f == 0.0
    }
}"

    Assert.Equal("|Either<int, f64>| -> bool", enum["is_zero"])

    let valueRestriction =
        runInfer
            "
enum Option<V> {
    Some(V),
    None
}

fn main() {
    let mut o = None

    o = Some(1)
}"

    Assert.Equal("Option<int>", valueRestriction["o"])

    let closure =
        runInfer
            "
fn church(f) {
    match f {
        true => |t, f| t,
        false => |t, f| f
    }
}"

    Assert.Equal("<Tt>|bool| -> |Tt, Tt| -> Tt", closure["church"])
