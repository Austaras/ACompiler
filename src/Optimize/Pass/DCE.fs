/// Dead Code Elimination
module Optimize.DCE

open Optimize.FLIR
open Optimize.WorkList

let dceImpl (f: Func) =
    let var = f.Var
    let block = f.Block
    let worklist = WorkList([||])
    let removed = ResizeArray()

    let findInstr id (i: Instr) = i.Target = id

    let canRemove id =
        let block = block[var[id].Def]

        if block.Phi.ContainsKey id then
            true
        else
            let instr = Array.find (findInstr id) block.Instr

            match instr with
            | Assign _
            | Unary _
            | Binary _ -> true
            | Call _
            | Load
            | Store
            | Alloc -> false

    for id in 0 .. f.Var.Length - 1 do
        if var[id].Use.Length = 0 && canRemove id then
            removed.Add id |> ignore
            worklist.Add id |> ignore

    for id in worklist do
        let blockId = var[id].Def
        let currBlock = block[blockId]

        if currBlock.Phi.ContainsKey id then
            for phi in currBlock.Phi[id] do
                let useData = { BlockId = blockId; Data = InPhi id }

                var[phi] <- var[phi].WithoutUse useData

                if var[phi].Use.Length = 0 && canRemove phi then
                    removed.Add phi
                    worklist.Add phi |> ignore

            let newPhi = currBlock.Phi.Remove id
            block[blockId] <- { currBlock with Phi = newPhi }
        else
            let instr = Array.find (findInstr id) currBlock.Instr

            for value in instr.Value do
                match value with
                | Const _ -> ()
                | Binding valueId ->
                    let useData =
                        { BlockId = blockId
                          Data = ForTarget id }

                    var[valueId] <- var[valueId].WithoutUse useData

                    if var[valueId].Use.Length = 0 && canRemove valueId then
                        removed.Add valueId
                        worklist.Add valueId |> ignore

            let instr = Array.filter ((findInstr id) >> not) currBlock.Instr

            block[blockId] <- { currBlock with Instr = instr }

    let varMapping = Array.create var.Length -1
    let mutable currIdx = 0

    for id = 0 to var.Length - 1 do
        if not (removed.Contains id) then
            varMapping[id] <- currIdx
            currIdx <- currIdx + 1

    let chooseVar id =
        if varMapping[id] = -1 then None else Some varMapping[id]

    let minimize (block: Block) =
        let rewritePhi (key, value) =
            if removed.Contains key then
                None
            else
                Some(varMapping[key], Array.choose chooseVar value)

        let phi = block.Phi |> Seq.map (|KeyValue|) |> Seq.choose rewritePhi |> Map.ofSeq
        let def id = varMapping[id]

        let use_ value =
            match value with
            | Const c -> Const c
            | Binding i -> Binding varMapping[i]

        { block.Rewrite def use_ with
            Phi = phi }

    let block = block |> Array.map minimize

    let filterVar idx =
        if not (removed.Contains idx) then Some var[idx] else None

    let var = seq { 0 .. var.Length - 1 } |> Seq.choose filterVar |> Array.ofSeq

    { f with Var = var; Block = block }

let dce = transRegional dceImpl
