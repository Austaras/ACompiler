module Semantic.Tests.Type.Match

open Xunit

open Common

[<Fact>]
let Fib () =
    runInfer
        "
fn fib(n) {
    match n {
        0 => 1,
        1 => 1,
        n => fib(n - 1) + fib(n - 2)
    }
}"
    |> toBe (Map [| "fib", "|int| -> int" |])

[<Fact>]
let Enum () =
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
    |> toBe (Map [| "is_zero", "|Either<int, f64>| -> bool" |])

[<Fact>]
let ValueRestriction () =
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
    |> toBe (Map [| "o", "Option<int>" |])

[<Fact>]
let Closure () =
    runInfer
        "
fn church(f) {
    match f {
        true => |t, f| t,
        false => |t, f| f
    }
}"
    |> toBe (Map [| "church", "<T0>|bool| -> |T0, T0| -> T0" |])
