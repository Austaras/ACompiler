module Semantic.Tests.Type.Poly

open Xunit

open Common

[<Fact>]
let Poly () =
    runAnalysis
        "
fn id(x) { 
    x
}

fn main() {
    id(id)(id(0))
}"
    |> toBe (Map [| "id", "<T0>|T0| -> T0" |])

[<Fact>]
let HoistedMono () =
    runAnalysis
        "
fn main() {
    one(1)
}

fn one(x) { 1 }"
    |> toBe (Map [| "one", "|int| -> int" |])

[<Fact>]
let HoistedTyped () =
    runAnalysis
        "
fn main() {
    id(1)
    let _ = id(true)
}

fn id<T>(x: T) -> T {
    x
}"
    |> toBe (Map [| "id", "<T>|T| -> T" |])

[<Fact>]
let RecTyped () =
    runAnalysis
        "
fn id<T>(x: T) -> T {
    let _ = id(1)
    let _ = id(true)
    x
}"
    |> toBe (Map [| "id", "<T>|T| -> T" |])

[<Fact>]
let PolyDouble () =
    runAnalysis "fn double(f, x) { f(f(x)) }"
    |> toBe (Map [| "double", "<T0>||T0| -> T0, T0| -> T0" |])

    runAnalysis "fn double(f) { |x| f(f(x)) }"
    |> toBe (Map [| "double", "<T0>||T0| -> T0| -> |T0| -> T0" |])

[<Fact>]
let PolyRec () =
    runAnalysis
        "
fn foo(x) {
    bar(1)
    x
}

fn bar(x) {
    foo(1)
}"
    |> toBe (Map [| "foo", "<T0>|T0| -> T0"; "bar", "|int| -> int" |])

[<Fact>]
let WeirdRec () =
    runAnalysis "fn weird_rec(x) { weird_rec(1) }"
    |> toBe (Map [| "weird_rec", "|int| -> !" |])

[<Fact>]
let ExplicitTuple () =
    runAnalysis
        "
pub fn swap<T1, T2>((fst, snd): (T1, T2)) -> (T2, T1) {
    (snd, fst)
}"
    |> toBe (Map [| "swap", "<T1, T2>|(T1, T2)| -> (T2, T1)" |])

[<Fact>]
let OtherScope () =
    runAnalysis
        "
fn former(x) {
    later(x)
}

fn later(x) {
    x
}"
    |> toBe (Map [| "former", "<T0>|T0| -> T0" |]) //; "later", "<T0>|T0| -> T0" |])

[<Fact>]
let Nested () =
    runAnalysis
        "
fn outer(x) {
    fn inner(y) {
        outer(y) == y
    }

    x
}"
    |> toBe (Map [| "outer", "<T0>|T0| -> T0"; "inner", "|T0| -> bool" |])
