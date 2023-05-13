module Parser.Tests.Expr

open Lexer
open Parser.Parser

open NUnit.Framework
open Snapper.Nunit

exception CustomError of Error[]

let parseTest input =
    match Lexer.lex input with
    | Ok token ->
        match parseExpr Context.Normal token with
        | Ok ast -> ast.data
        | Error e -> raise (CustomError e)
    | Error e -> raise (CustomError(Array.map LexError e))

[<Test>]
let Bin () =
    Assert.That(parseTest "1 + 2 * 3", Matches.ChildSnapshot("Binary"))
    Assert.That(parseTest "3 - 2 - 1", Matches.ChildSnapshot("Assoc"))
    Assert.That(parseTest "a == c + d * 3", Matches.ChildSnapshot("Compare"))

    Assert.That(parseTest "a = b + c", Matches.ChildSnapshot("Assign"))
    Assert.That(parseTest "a = b = c", Matches.ChildSnapshot("RightAssoc"))
    Assert.That(parseTest "a *= b + c", Matches.ChildSnapshot("AssignOp"))

    Assert.That(parseTest "(1 + 2) * 3", Matches.ChildSnapshot("Paren"))
    Assert.That(parseTest "((((1 + 2))) * (3))", Matches.ChildSnapshot("ManyParen"))

    Assert.That(
        parseTest
            "1 + // comment
    2",
        Matches.ChildSnapshot("Comment")
    )

    Assert.That(parseTest "1 + 2 * let 3", Matches.ChildSnapshot("Malformed"))

[<Test>]
let Tuple () =
    Assert.That(parseTest "()", Matches.ChildSnapshot("Zero"))
    Assert.That(parseTest "(1 + 2) * (4 - 5)", Matches.ChildSnapshot("One"))
    Assert.That(parseTest "(2, (1, 2), a = b)", Matches.ChildSnapshot("Many"))

[<Test>]
let Array () =
    Assert.That(parseTest "[1, 2 + 3, 4,]", Matches.ChildSnapshot("Nomral"))
    Assert.That(parseTest "[a; 10]", Matches.ChildSnapshot("Repeat"))
    Assert.That(parseTest "[1 + 2] + [3 * 4]", Matches.ChildSnapshot("Binary"))

[<Test>]
let Field () =
    Assert.That(parseTest "a.b.c", Matches.ChildSnapshot("Assoc"))
    Assert.That(parseTest "(0, 1)._0 + 1", Matches.ChildSnapshot("Tuple"))
    Assert.That(parseTest "[1,2,3][2]", Matches.ChildSnapshot("Array"))
    Assert.That(parseTest "a[1][c + d]", Matches.ChildSnapshot("Multi"))
    Assert.That(parseTest "a[1].x", Matches.ChildSnapshot("Mix"))
    Assert.That(parseTest "a.x[1]", Matches.ChildSnapshot("Mix2"))
    Assert.That(parseTest "a.b = c.d", Matches.ChildSnapshot("Assign"))
    Assert.That(parseTest "a.b + c.0 * d.e", Matches.ChildSnapshot("Bin"))

[<Test>]
let Unary () =
    Assert.That(parseTest "-1+-2", Matches.ChildSnapshot("Binary"))

    Assert.That(
        parseTest
            "[] -
        1",
        Matches.ChildSnapshot("Delimiter")
    )

[<Test>]
let Range () =
    Assert.That(parseTest "a.b = 1+1 .. 2*3", Matches.ChildSnapshot("Full"))
    Assert.That(parseTest "-5..-3", Matches.ChildSnapshot("Unary"))
    Assert.That(parseTest "..1 + 1..", Matches.ChildSnapshot("Half"))

[<Test>]
let Call () =
    Assert.That(parseTest "a()()", Matches.ChildSnapshot("Many"))
    Assert.That(parseTest "-a.b()", Matches.ChildSnapshot("Unary"))
    Assert.That(parseTest "a() + c(d)", Matches.ChildSnapshot("Bin"))

[<Test>]
let Path () =
    Assert.That(parseTest "Vec::<i32>>>1", Matches.ChildSnapshot("GenericShr"))
    Assert.That(parseTest "Vec::<Vec<i32>>>1", Matches.ChildSnapshot("DoubleGeneric"))
    Assert.That(parseTest "Foo::Bar::<Vec<i32>> { a, b: 10, ..d }", Matches.ChildSnapshot("Struct"))

[<Test>]
let Closure () =
    Assert.That(parseTest "(|x| x * 2) >> <T>|x: T| -> Option<T> Some(x)", Matches.ChildSnapshot("Compose"))
    Assert.That(parseTest "|x| |y| x + y", Matches.ChildSnapshot("Curry"))

[<Test>]
let Control () =
    Assert.That(parseTest "if let L(_) | R(_) = a { 1 } else if a <= 3 { 2 } else { 3 }", Matches.ChildSnapshot("If"))

    Assert.That(parseTest "for i in 0..9 { print(i) }", Matches.ChildSnapshot("For"))

    Assert.That(parseTest "match a { Some(a) => a, None => 1, _ if true => 3 }", Matches.ChildSnapshot("Match"))
