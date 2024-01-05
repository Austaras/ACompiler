module Parser.Tests.Expr

open Xunit

open Snapshot
open AST.Dump
open Parser.Expr

let parseTest = Util.makeTest parseExpr expr

let snap = Snapshot("snap")

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Expr"

[<Theory>]
[<InlineData("Normal", "1 + 2 * 3")>]
[<InlineData("Assoc", "3 - 2 - 1")>]
[<InlineData("Compare", "a == c + d * 3")>]

[<InlineData("Assign", "a = b + c")>]
[<InlineData("AssignOp", "a *= b + c")>]
[<InlineData("RightAssoc", "a = b = c")>]

[<InlineData("Paren", "(1 + 2) * 3")>]
[<InlineData("ManyParen", "((((1 + 2))) * (3))")>]

[<InlineData("Comment",
             "1 + // comment
2")>]

[<InlineData("Malformed", "1 + 2 * let 3")>]
let Binary (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Binary/{name}"

[<Theory>]
[<InlineData("Zero", "()")>]
[<InlineData("One", "(1 + 2) * (4 - 5)")>]
[<InlineData("Many", "(2, (1, 2), a = b)")>]
let Tuple (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Tuple/{name}"

[<Theory>]
[<InlineData("Normal", "[1, 2 + 3, 4,]")>]
[<InlineData("Repeat", "[a; 10]")>]
[<InlineData("Binary", "[1 + 2] + [3 * 4]")>]
let Array (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Array/{name}"

[<Theory>]
[<InlineData("Assoc", "a.b.c")>]
// [<InlineData("(0, 1)._0 + 1", "Tuple")>]
[<InlineData("Array", "[1,2,3][2]")>]
[<InlineData("Multi", "a[1][c + d]")>]
[<InlineData("Mix", "a[1].x")>]
[<InlineData("Mix2", "a.x[1]")>]
[<InlineData("Assign", "a.b = c.d")>]
[<InlineData("Binary", "a.b + c[0] * d.e")>]
let Field (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Field/{name}"

[<Theory>]
[<InlineData("Binary", "-1+-2")>]

[<InlineData("Delimiter",
             "[] -
    1")>]

[<InlineData("LogicalAnd", "&&a")>]
let Unary (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Unary/{name}"

[<Theory>]
[<InlineData("Full", "a.b = 1+1 .. 2*3")>]
[<InlineData("Unary", "-5..-3")>]
[<InlineData("Half", "..1 + 1..")>]
let Range (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/Range/{name}"

[<Theory>]
[<InlineData("Many", "a()()")>]
[<InlineData("Unary", "-a.b()")>]
[<InlineData("Binary", "a() + c(d)")>]

[<InlineData("Block",
             "{
    a()
    ()
}")>]
let Call (name: string) (input: string) =
    let res = parseTest input

    snap.ShouldMatchText res $"{basePath}/Call/{name}"

[<Theory>]
[<InlineData("GenericShr", "Vec::<i32>>>1")>]
[<InlineData("DoubleGeneric", "Vec::<Vec<i32>>>1")>]

[<InlineData("Struct", "Foo::Bar::<Vec<i32>> { a, b: 10, ..d }")>]
let Path (name: string) (input: string) =
    let res = parseTest input

    snap.ShouldMatchText res $"{basePath}/Path/{name}"

[<Theory>]
[<InlineData("Compose", "(|x| x * 2) >> |x| Some(x)")>]
[<InlineData("Curry", "|x| |y| x + y")>]
[<InlineData("NotClosure", "true ||x| x")>]
let Closure (name: string) (input: string) =
    let res = parseTest input

    snap.ShouldMatchText res $"{basePath}/Closure/{name}"

[<Theory>]
[<InlineData("If", "if let L(_) | R(_) = a { 1 } else if a <= 3 { 2 } else { 3 }")>]
[<InlineData("For", "for i in 0..9 { print(i) }")>]
[<InlineData("Match", "match a { Some(a) => a, None => 1, _ if true => 3 }")>]
let Control (name: string) (input: string) =
    let res = parseTest input

    snap.ShouldMatchText res $"{basePath}/Control/{name}"
