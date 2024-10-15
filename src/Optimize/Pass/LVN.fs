/// Local Value Numbering
module Optimize.Pass.LVN

open System.Collections.Generic

open Optimize.FLIR

let rewriteBlock (newVar: Var[]) (blockId: int) (block: Block) =
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

                newVar[var] <- newVar[var].WithUse varData

                match b.Left with
                | Const _ -> ()
                | Binding l -> newVar[l] <- newVar[l].WithoutUse varData

                match b.Right with
                | Const _ -> ()
                | Binding r -> newVar[r] <- newVar[r].WithoutUse varData

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

                newVar[var] <- newVar[var].WithUse varData

                match u.Value with
                | Const _ -> ()
                | Binding u -> newVar[u] <- newVar[u].WithoutUse varData

                Assign
                    { Target = u.Target
                      Value = Binding var
                      Span = u.Span }
            else
                unaryTable.Add(ident, u.Target)
                Unary u
        | _ -> instr

    { block with
        Instr = Array.map rewrite block.Instr }

let lvnImpl (f: Func) =
    let var = Array.copy f.Var

    let block =
        f.Block |> Array.indexed |> Array.map (fun (idx, b) -> rewriteBlock var idx b)

    { f with Block = block; Var = var }

let lvn = transRegional lvnImpl
