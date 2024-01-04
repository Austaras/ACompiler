module Semantic.Tests.Type

open System.Collections.Generic

open System.IO
open Xunit

open AST
open Parser.Lexer
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let runInfer input =
    let token =
        match lex input with
        | Ok tok -> tok
        | Error e -> failwithf "lex error %A" e

    let m =
        match parse token with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let sema, error = typeCheck (Dictionary()) m

    Assert.Empty error

    let map (id: AST.Id, t: Type) = (id.Sym, t.ToString)

    sema.Var |> Map.toSeq |> Seq.map map |> Map.ofSeq

let runInferFromExample path =
    File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../examples/" + path) |> runInfer

[<Fact>]
let Closure () =
    let mutualRec = runInferFromExample "function/mutual_rec.adf"
    Assert.Equal(mutualRec["is_even"], "|int| -> bool")
    Assert.Equal(mutualRec["is_odd"], "|int| -> bool")

    let closure = runInfer "fn call(c) { c(0) + 1 }"
    Assert.Equal(closure["call"], "||int| -> int| -> int")

    let curry =
        runInfer
            "
fn equal(x) {
    |y| x == y
}"

    Assert.Equal(curry["equal"], "<Tx>|Tx| -> |Tx| -> bool")

    let monoClosure =
        runInfer
            "
fn main() {
    let id = |x| x

    id(1)
}"

    Assert.Equal(monoClosure["id"], "|int| -> int")

    let topLevel =
        runInfer
            "
fn foo() {
    f
}

let f = 1"

    Assert.Equal(topLevel["foo"], "|| -> int")

    let ret =
        runInfer
            "
fn foo(i) {
    if i == 0 {
        return 0
    }

    i + 1
}"

    Assert.Equal(ret["foo"], "|int| -> int")

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

    Assert.Equal(never["foo"], "|int| -> int")

[<Fact>]
let Reference () =
    let reference = runInfer "fn deref(a) { *a + 1 }"
    Assert.Equal(reference["deref"], "|&int| -> int")

    let refField =
        runInfer
            "
struct Foo {
    f: uint
}

fn get_f(f) { &f.f }"

    Assert.Equal(refField["get_f"], "|Foo| -> &uint")

[<Fact>]
let ADT () =
    let stru = runInferFromExample "function/struct.adf"
    Assert.Equal(stru["add"], "|Point3D| -> int")

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

    Assert.Equal(autoDeref["foo"], "|Foo| -> &Foo")

    //     let derefParam =
    //         runInfer
    //             "
    // struct Foo {
    //     b: uint
    // }

    // fn foo(f: &Foo) {
    //     f.b
    // }"

    //     Assert.Equal(derefParam["foo"], "|&Foo| -> &uint")

    let tuple =
        runInfer
            "
fn foo((a, b, c)) {
    a == 1 && b == 2 && c == 3
}"

    Assert.Equal(tuple["foo"], "|(int, int, int)| -> bool")

    let inferred =
        runInfer
            "
struct Foo<T> {
    f: T
}

fn foo(f: Foo<_>) -> uint {
    f.f
}"

    Assert.Equal(inferred["foo"], "|Foo<uint>| -> uint")

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

    Assert.Equal(poly["id"], "<Tx>|Tx| -> Tx")

    let hoistedMono =
        runInfer
            "
fn main() {
    one(1)
}

fn one(x) { 1 }"

    Assert.Equal(hoistedMono["one"], "|int| -> int")

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

    Assert.Equal(hoistedTyped["id"], "<T>|T| -> T")

    let polyDouble = runInfer "fn double(f, x) { f(f(x)) }"
    Assert.Equal(polyDouble["double"], "<Tx>||Tx| -> Tx, Tx| -> Tx")

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

    Assert.Equal(polyRec["foo"], "<Tx>|Tx| -> Tx")
    Assert.Equal(polyRec["bar"], "|int| -> int")

    let weirdRec = runInfer "fn weird_rec(x) { weird_rec(1) }"
    Assert.Equal(weirdRec["weird_rec"], "<T21>|int| -> T21")

    let explicit =
        runInfer
            "
pub fn swap<T1, T2>(t: (T1, T2)) -> (T2, T1) {
    let (fst, snd) = t

    (snd, fst)
}"

    Assert.Equal(explicit["swap"], "<T1, T2>|(T1, T2)| -> (T2, T1)")

[<Fact>]
let Match () =
    let fib = runInferFromExample "function/fib.adf"
    Assert.Equal(fib["fib"], "|int| -> int")

    let enum =
        runInfer
            "
enum Either<L, R> {
    L(L),
    R(R)
}

fn is_zero(e) {
    match e {
        Either::L(i) => i == 0,
        Either::R(f) => f == 0.0
    }
}"

    Assert.Equal(enum["is_zero"], "|Either<int, f64>| -> bool")

    let valueRestriction =
        runInfer
            "
enum Option<V> {
    Some(V),
    None
}

fn main() {
    let mut o = Option::None

    o = Option::Some(1)
}"

    Assert.Equal(valueRestriction["o"], "Option<int>")

    let closure =
        runInfer
            "
fn foo(f) {
    match f {
        true => |t, f| -> uint t,
        false => |t, f| f
    }
}"

    Assert.Equal(closure["foo"], "|bool| -> |uint, uint| -> uint")
