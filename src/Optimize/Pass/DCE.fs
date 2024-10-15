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
            | Load
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

    let varMapping = Array.create var.Length -1
    let mutable currIdx = 0

    for id = 0 to var.Length - 1 do
        if not (removed.Contains id) then
            varMapping[id] <- currIdx
            currIdx <- currIdx + 1

    let chooseVar value =
        match value with
        | Const c -> Some value
        | Binding id ->
            if varMapping[id] = -1 then
                None
            else
                Some(Binding varMapping[id])

    let rewriteBlock (block: Block) =
        let rewritePhi (key, value) =
            if removed.Contains key then
                None
            else
                Some(varMapping[key], Array.choose chooseVar value)

        let phi = block.Phi |> Seq.map (|KeyValue|) |> Seq.choose rewritePhi |> Map.ofSeq
        let rewriteDef id = varMapping[id]

        let rewriteUse value =
            match value with
            | Const c -> Const c
            | Binding i -> Binding varMapping[i]

        { block.Rewrite rewriteDef rewriteUse with
            Phi = phi }

    let block = block |> Array.map rewriteBlock

    let filterUse use_ =
        match use_.Data with
        | InTx -> Some use_
        | InPhi phi ->
            if removed.Contains phi then
                None
            else
                Some
                    { BlockId = use_.BlockId
                      Data = InPhi varMapping[phi] }
        | ForTarget target ->
            if removed.Contains target then
                None
            else
                Some
                    { BlockId = use_.BlockId
                      Data = ForTarget varMapping[target] }

    let filterVar idx =
        if not (removed.Contains idx) then
            Some
                { var[idx] with
                    Use = Array.choose filterUse var[idx].Use }
        else
            None

    let var = seq { 0 .. var.Length - 1 } |> Seq.choose filterVar |> Array.ofSeq

    { f with Var = var; Block = block }

let dce phiOnly = transRegional (dceImpl phiOnly)
