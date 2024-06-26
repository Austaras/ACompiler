/// Local Value Numbering
module Optimize.Pass.LVN

open System.Collections.Generic

open Optimize.FLIR

let lvnImpl (b: Block) =
    let mutable num = 0
    let binaryTable = Dictionary()
    let unaryTable = Dictionary()

    let rewrite instr =
        match instr with
        | Binary b ->
            let ident = b.Left, b.Op, b.Right

            if binaryTable.ContainsKey ident then
                let var = binaryTable[ident]

                Assign
                    { Target = b.Target
                      Value = Binding var
                      Span = b.Span }
            else
                binaryTable.Add(ident, b.Target)
                Binary b
        | Unary u ->
            let ident = u.Value, u.Op

            if unaryTable.ContainsKey ident then
                let var = unaryTable[ident]

                Assign
                    { Target = u.Target
                      Value = Binding var
                      Span = u.Span }
            else
                unaryTable.Add(ident, u.Target)
                Unary u
        | _ -> instr

    { b with
        Instr = Array.map rewrite b.Instr }

let lvn = transLocal lvnImpl
