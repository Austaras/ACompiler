module Parser.Tests.Stmt

open Xunit

open Snapshot
open AST.Dump
open Parser.Stmt

let dump ast =
    use sw = new System.IO.StringWriter()
    stmt sw 0 ast
    sw.ToString()

let parseTest = Util.makeTest parseStmt dump

let snap = Snapshot("snap")

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Stmt"

[<Theory>]
[<InlineData("Function",
             "fn add<T: Add>(x: T, y: T) -> T {
    x + y
}
    a
}")>]

[<InlineData("Let",
             "let _ = {
    let mut a = 10;
    print(a);
    a
}")>]

[<InlineData("Enum",
             "enum Option<T> {
    Some(T),
    None
}")>]

[<InlineData("Impl",
             "impl<T> Vec<T> {
    pub fn push(&self, element: T) {}
}")>]

[<InlineData("Trait",
             "trait Summary {
    fn summarize(&self) -> String
}")>]
let Decl (name: string) (input: string) =
    let res = parseTest input
    snap.ShouldMatchText res $"{basePath}/{name}"
