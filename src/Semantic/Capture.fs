module Semantic.Capture

open AST.AST

type Closure with

    member this.Capture = 1

type Fn with

    member this.Capture = 1
