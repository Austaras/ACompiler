/// Local Value Numbering
module Optimize.Pass.LVN

open System.Collections.Generic

open Optimize.FLIR

let lvnImpl (f: Func) (blockId: int, b: Block) =
    let binaryTable = Dictionary()
    let unaryTable = Dictionary()

    let rewrite instr =
        match instr with
        | Binary b ->
            let ident = b.Left, b.Op, b.Right

            if binaryTable.ContainsKey ident then
                let var = binaryTable[ident]

                let varData =
                    { BlockId = blockId
                      Data = ForTarget b.Target }

                f.Var[var] <- f.Var[var].WithUse varData

                match b.Left with
                | Const _ -> ()
                | Binding l -> f.Var[l] <- f.Var[l].WithoutUse varData

                match b.Right with
                | Const _ -> ()
                | Binding r -> f.Var[r] <- f.Var[r].WithoutUse varData

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

                let varData =
                    { BlockId = blockId
                      Data = ForTarget u.Target }

                f.Var[var] <- f.Var[var].WithUse varData

                match u.Value with
                | Const _ -> ()
                | Binding l -> f.Var[l] <- f.Var[l].WithoutUse varData

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
