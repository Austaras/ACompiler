module Parser.Tests.Stmt

open System.IO

open Xunit

open Snapshot
open AST.Dump
open Parser.Lexer
open Parser.Parser

let internal parseTest input (tw: TextWriter) =
    let error = ResizeArray()
    let lexer = Lexer(input, error)
    let parser = Parser(lexer, error)
    let dump = Dump(tw)

    let s = parser.Stmt()

    dump.Stmt s

let basePath = __SOURCE_DIRECTORY__ + "/Spec/Stmt/"
let snap = TextSnapshot("snap", basePath)

[<Theory>]
[<InlineData("Function",
             "fn add<T: Add>(x: T, y: T) -> T {
    x + y
}")>]

[<InlineData("Let",
             "let _ = {
    let mut a = 10
    print(a)
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
    snap.ShouldMatch res name
