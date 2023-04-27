module Parser.Parser

open AST
open Lexer

let parse (input: Lexer.Token[]) : Result<AST.Stmt[], (AST.Span * string)[]> = Ok [||]
