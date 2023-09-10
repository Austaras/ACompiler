module Parser.Tests.Expr

open Parser.Expr

open Snapper
open Xunit

let parseTest = Util.makeTest parseExpr

[<Fact>]
let Bin () =
    (parseTest "1 + 2 * 3").ShouldMatchChildSnapshot("Binary")
    (parseTest "3 - 2 - 1").ShouldMatchChildSnapshot("Assoc")
    (parseTest "a == c + d * 3").ShouldMatchChildSnapshot("Compare")

    (parseTest "a = b + c").ShouldMatchChildSnapshot("Assign")
    (parseTest "a = b = c").ShouldMatchChildSnapshot("RightAssoc")
    (parseTest "a *= b + c").ShouldMatchChildSnapshot("AssignOp")

    (parseTest "(1 + 2) * 3").ShouldMatchChildSnapshot("Paren")
    (parseTest "((((1 + 2))) * (3))").ShouldMatchChildSnapshot("ManyParen")

    (parseTest
        "1 + // comment
    2")
        .ShouldMatchChildSnapshot("Comment")

    (parseTest "1 + 2 * let 3").ShouldMatchChildSnapshot("Malformed")

[<Fact>]
let Tuple () =
    (parseTest "()").ShouldMatchChildSnapshot("Zero")
    (parseTest "(1 + 2) * (4 - 5)").ShouldMatchChildSnapshot("One")
    (parseTest "(2, (1, 2), a = b)").ShouldMatchChildSnapshot("Many")

[<Fact>]
let Array () =
    (parseTest "[1, 2 + 3, 4,]").ShouldMatchChildSnapshot("Normal")
    (parseTest "[a; 10]").ShouldMatchChildSnapshot("Repeat")
    (parseTest "[1 + 2] + [3 * 4]").ShouldMatchChildSnapshot("Binary")

[<Fact>]
let Field () =
    (parseTest "a.b.c").ShouldMatchChildSnapshot("Assoc")
    (parseTest "(0, 1)._0 + 1").ShouldMatchChildSnapshot("Tuple")
    (parseTest "[1,2,3][2]").ShouldMatchChildSnapshot("Array")
    (parseTest "a[1][c + d]").ShouldMatchChildSnapshot("Multi")
    (parseTest "a[1].x").ShouldMatchChildSnapshot("Mix")
    (parseTest "a.x[1]").ShouldMatchChildSnapshot("Mix2")
    (parseTest "a.b = c.d").ShouldMatchChildSnapshot("Assign")
    (parseTest "a.b + c.0 * d.e").ShouldMatchChildSnapshot("Bin")

[<Fact>]
let Unary () =
    (parseTest "-1+-2").ShouldMatchChildSnapshot("Binary")

    (parseTest
        "[] -
        1")
        .ShouldMatchChildSnapshot("Delimiter")

    (parseTest "&&a").ShouldMatchChildSnapshot("LogicalAnd")

[<Fact>]
let Range () =
    (parseTest "a.b = 1+1 .. 2*3").ShouldMatchChildSnapshot("Full")
    (parseTest "-5..-3").ShouldMatchChildSnapshot("Unary")
    (parseTest "..1 + 1..").ShouldMatchChildSnapshot("Half")

[<Fact>]
let Call () =
    (parseTest "a()()").ShouldMatchChildSnapshot("Many")
    (parseTest "-a.b()").ShouldMatchChildSnapshot("Unary")
    (parseTest "a() + c(d)").ShouldMatchChildSnapshot("Bin")

[<Fact>]
let Path () =
    (parseTest "Vec::<i32>>>1").ShouldMatchChildSnapshot("GenericShr")
    (parseTest "Vec::<Vec<i32>>>1").ShouldMatchChildSnapshot("DoubleGeneric")

    (parseTest "Foo::Bar::<Vec<i32>> { a, b: 10, ..d }")
        .ShouldMatchChildSnapshot("Struct")

[<Fact>]
let Closure () =
    (parseTest "(|x| x * 2) >> |x| Some(x)").ShouldMatchChildSnapshot("Compose")

    (parseTest "|x| |y| x + y").ShouldMatchChildSnapshot("Curry")

    (parseTest "true ||x| x").ShouldMatchChildSnapshot("NotClosure")

[<Fact>]
let Control () =
    (parseTest "if let L(_) | R(_) = a { 1 } else if a <= 3 { 2 } else { 3 }")
        .ShouldMatchChildSnapshot("If")

    (parseTest "for i in 0..9 { print(i) }").ShouldMatchChildSnapshot("For")

    (parseTest "match a { Some(a) => a, None => 1, _ if true => 3 }")
        .ShouldMatchChildSnapshot("Match")
