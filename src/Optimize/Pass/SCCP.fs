// Sparse Condition COnstant Propagation
module Optimize.Pass.SCCP

open Optimize.FLIR
open Optimize.WorkList

type Value =
    | Top
    | Bottom
    | Known of uint64

type VarValue(count: int) =
    let value = Array.create count Bottom

    member _.ValueOf v =
        match v with

        | Const i -> Known i
        | Binding v -> value[v]

    member this.Eval instr =
        match instr with
        | Call _
        | Load
        | Alloc -> Top
        | Assign v -> this.ValueOf v.Value
        | Binary b ->
            let left = this.ValueOf b.Left
            let right = this.ValueOf b.Right

            match left, right with
            | Top, _
            | _, Top -> Top
            | Bottom, _
            | _, Bottom -> failwith "Unreachable"
            | Known l, Known r ->
                match b.Op with
                | Add -> Known(l + r)
                | Sub -> Known(l - r)
                | Mul -> Known(l * r)
                | Div -> Known(l / r)
                | Rem -> failwith "Not Implemented"
                | Xor -> failwith "Not Implemented"
                | And -> failwith "Not Implemented"
                | Or -> failwith "Not Implemented"
                | Shl -> failwith "Not Implemented"
                | Shr(_) -> failwith "Not Implemented"
                | Eq -> failwith "Not Implemented"
                | NotEq -> failwith "Not Implemented"
                | Lt(_) -> failwith "Not Implemented"
                | LtEq(_) -> failwith "Not Implemented"
                | GtEq(_) -> failwith "Not Implemented"
                | Gt(_) -> failwith "Not Implemented"
        | Unary(_) -> failwith "Not Implemented"
        | Store -> failwith "Not Implemented"

let sccpImpl (f: Func) =
    let varValue = Array.create f.Var.Length Bottom

    let varList = WorkList(seq { 0 .. f.Var.Length - 1 })
    let blockList = WorkList(seq { 0 .. f.Block.Length - 1 })

    for var in varList do
        ()

    for block in blockList do
        ()

    f

let sccp = transRegional sccpImpl
