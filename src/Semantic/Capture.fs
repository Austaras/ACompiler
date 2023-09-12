module Semantic.Capture

open System.Collections.Generic

open AST.AST

let internal processParam (param: Param[]) =
    let newEnv = HashSet()

    for p in param do
        for id in p.pat.ExtractId do
            newEnv.Add id.sym |> ignore

    newEnv

type Closure with

    member this.Capture(env: HashSet<string>[]) = 1

type Fn with

    member this.Capture(env: HashSet<string>[]) = 1
