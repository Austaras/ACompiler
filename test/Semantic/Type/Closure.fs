module Semantic.Tests.Type.Closure

open Xunit

open Common

[<Fact>]
let MutualRec () =
    runInfer
        "
fn is_even(n) {
    if n == 0 {
        true
    } else {
        !is_odd(n - 1)
    }
}

fn is_odd(n) {
    if n == 0 {
        false
    } else {
        !is_even(n - 1)
    }
}"
    |> toBe (Map [| "is_even", "|int| -> bool"; "is_odd", "|int| -> bool" |])

[<Fact>]
let Closure () =
    runInfer "fn call(c) { c(0) + 1 }"
    |> toBe (Map [| "call", "||int| -> int| -> int" |])

[<Fact>]
let Curry () =
    runInfer
        "
fn equal(x) {
    |y| x == y
}"
    |> toBe (Map [| "equal", "<T0>|T0| -> |T0| -> bool" |])

[<Fact>]
let MonoClosure () =
    runInfer
        "
fn main() {
    let id = |x| x

    id(1)
}"
    |> toBe (Map [| "id", "|int| -> int" |])

[<Fact>]
let TopLevel () =
    runInfer
        "
fn foo() {
    f
}

let f = 1"
    |> toBe (Map [| "foo", "|| -> int" |])

[<Fact>]
let Ret () =
    runInfer
        "
fn foo(i) {
    if i == 0 {
        return 0
    }

    i + 1
}"
    |> toBe (Map [| "foo", "|int| -> int" |])

[<Fact>]
let Never () =
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
    |> toBe (Map [| "foo", "|int| -> int" |])
