module Semantic.Escape

open AST.AST

type Location =
    | Register
    | Stack
    | Heap

type Closure with

    member this.Escape = 1

type Fn with

    member this.Escape = 1
