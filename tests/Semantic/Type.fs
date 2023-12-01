module Semantic.Tests.Type

open FSharp.Json
open Snapper
open System.IO
open Xunit

open AST
open Parser.Lexer
open Parser.Parser
open Semantic.Semantic
open Semantic.Check

let runInfer input name =
    let token =
        match lex 0 input with
        | Ok tok -> tok
        | Error e -> failwithf "lex error %A" e

    let m =
        match parse token with
        | Ok m -> m
        | Error(e, _) -> failwithf "parse error %A" e

    let checker = TypeCheck(Map.empty)

    checker.Check m

    Assert.Empty checker.GetError

    let reform (key: AST.Id, value: Type) = key.Sym, value.ToString

    (checker.GetInfo.Var
     |> Seq.map (|KeyValue|)
     |> Seq.map reform
     |> Map.ofSeq
     |> Json.serialize)
        .ShouldMatchChildSnapshot(name)

let runInferFromExample path =
    File.ReadAllText(__SOURCE_DIRECTORY__ + "/../../examples/" + path) |> runInfer

[<Fact>]
let Closure () =
    runInferFromExample "function/mutual_rec.adf" "MutualRec"

    runInfer "fn call(c) { c(0) + 1 }" "Closure"

    runInfer
        "
    fn equal(x) {
        fn equal1(y) {
            x == y
        }

        equal1
    }
    "
        "Curry"

    runInfer
        "
    fn main() {
        let id = |x| x

        let _ = id(1)
    }
    "
        "MonoClosure"

    runInfer
        "
    fn foo() {
        f
    }

    let f = 1
    "
        "TopLevel"


    runInfer
        "
        fn foo(i) { 
            if i == 0 {
                return 0
            }

            i + 1
        }"
        "Return"

[<Fact>]
let Reference () =
    runInfer "fn deref(a) { *a + 1 }" "Reference"

    runInfer
        "
    struct Foo {
        f: usize
    }

    fn get_f(f) { &f.f }
    "
        "RefField"

[<Fact>]
let ADT () =
    runInferFromExample "function/struct.adf" "Struct"

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
        }
        "
        "AutoDeref"

    runInfer
        "
        struct Foo {
            b: usize
        }

        fn foo(f: &Foo) {
            f.b
        }
        "
        "DerefParam"

    runInfer
        "
        fn foo((a, b, c)) {
            a == 1 && b == 2 && c == 3
        }
    "
        "Tuple"

    runInfer
        "
    struct Foo<T> {
        f: T
    }
    
    fn foo(f: Foo<_>) -> usize {
        f.f
    }
    "
        "InferedType"

[<Fact>]
let Poly () =
    runInfer
        "
    fn id(x) { x }

    fn main() {
        id(id)(id(0))
        ()
    }
    "
        "Poly"

    runInfer
        "
    fn main() {
        one(1)
        ()
    }

    fn one(x) { 1 }
    "
        "HoistedMono"

    runInfer
        "
    fn main() {
        id(1)
        let _ = id(true)
    }

    fn id<T>(x: T) -> T { 
        x 
    }
    "
        "HoistedTyped"

    runInfer "fn double(f, x) { f(f(x)) }" "PolyDouble"

    runInfer
        "
    fn foo(x) {
        bar(1)
        x
    }
    fn bar(x) {
        foo(1)
    }
    "
        "PolyRec"

    runInfer "fn weird_rec(x) { weird_rec(1) }" "WeirdRec"

    runInfer
        "
    pub fn swap<T1, T2>(t: (T1, T2)) -> (T2, T1) {
        let (fst, snd) = t

        (snd, fst)
    }"
        "Explicit"

[<Fact>]
let Match () =
    runInferFromExample "function/fib.adf" "Fib"

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
        }
    "
        "Enum"

    runInfer
        "
        enum Option<V> {
            Some(V),
            None
        }

        fn main() {
            let mut o = Option::None

            o = Option::Some(1)
        }
    "
        "ValueRestriction"

    runInfer
        "
        fn foo(f) {
            match f {
                true => |t, f| t,
                false => |t, f| f
            }
        }
    "
        "Closure"
