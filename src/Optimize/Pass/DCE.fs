/// Dead Code Elimination
module Optimize.DCE

open System.Collections.Generic

open Optimize.FLIR
open Optimize.Util

let dceImpl (phiOnly: bool) (f: Func) =
    let var = Array.copy f.Var
    let block = Array.copy f.Block
    let worklist = WorkList([||])
    let removed = HashSet()

    let findInstr id (i: Instr) = i.Target = id

    let allRemoved (useList: Use[]) =
        let removed use_ =
            match use_.Data with
            | InTx -> false
            | InPhi phiVar -> removed.Contains phiVar
            | ForTarget target -> removed.Contains target

        useList.Length = 0 || Array.forall removed useList

    let canRemove id =
        let block = block[var[id].Def]

        if block.Phi.ContainsKey id then
            true
        else if not phiOnly then
            let instr = Array.find (findInstr id) block.Instr

            match instr with
            | Assign _
            | Unary _
            | Binary _ -> true
            | Call _
            | Load _
            | Store
            | Alloc -> false
        else
            false

    for id in 0 .. f.Var.Length - 1 do
        if var[id].Use.Length = 0 && canRemove id then
            removed.Add id |> ignore
            worklist.Add id |> ignore

    for id in worklist do
        let blockId = var[id].Def
        let currBlock = block[blockId]

        if currBlock.Phi.ContainsKey id then
            for phi in currBlock.Phi[id] do
                match phi with
                | Const _ -> ()
                | Binding i ->
                    if allRemoved var[i].Use && canRemove i then
                        removed.Add i |> ignore
                        worklist.Add i |> ignore

            let newPhi = currBlock.Phi.Remove id
            block[blockId] <- { currBlock with Phi = newPhi }
        else
            let instr = Array.find (findInstr id) currBlock.Instr

            for value in instr.Value do
                match value with
                | Const _ -> ()
                | Binding valueId ->
                    if allRemoved var[valueId].Use && canRemove valueId then
                        removed.Add valueId |> ignore
                        worklist.Add valueId |> ignore

            let instr = Array.filter ((findInstr id) >> not) currBlock.Instr

            block[blockId] <- { currBlock with Instr = instr }

    let varMapping =
        seq { 0 .. var.Length - 1 }
        |> Seq.map (fun idx -> if removed.Contains idx then None else Some(Binding idx))
        |> Array.ofSeq

    let blockMapping = seq { 0 .. block.Length - 1 } |> Array.ofSeq

    mapVarAndBlock f varMapping blockMapping

let dce phiOnly = transRegional (dceImpl phiOnly)
