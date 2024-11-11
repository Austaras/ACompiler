/// Aggressive Dead Code Elimination
module Optimize.Pass.ADCE

open System.Collections.Generic

open Optimize.FLIR
open Optimize.Util

let adceImpl (f: Func) =
    let cdg = cdg f

    let varLive = Array.create f.Var.Length false
    let blockLive = Array.create f.Block.Length false

    for p in f.Param do
        varLive[p] <- true

    let varList = WorkList([])

    let markValue value =
        match value with
        | Const _ -> ()
        | Binding id ->
            let prev = varLive[id]
            varLive[id] <- true

            if not prev then
                varList.Add id |> ignore

    let rec markBlock id =
        let prev = blockLive[id]
        blockLive[id] <- true

        if not prev then
            match f.Block[id].Trans with
            | Branch { Value = value }
            | Indirect { Value = value } -> markValue value
            | _ -> ()

            let control = cdg[id].Pred

            for control in control do
                match f.Block[control].Trans with
                | Branch b ->
                    markBlock control
                    markValue b.Value
                | _ -> ()

            match f.Block[id].Trans with
            | Jump j -> markBlock j.Target
            | Branch b ->
                markBlock b.Zero
                markBlock b.One
            | _ -> ()

    for (blockIdx, block) in Array.indexed f.Block do
        match block.Trans with
        | Return r ->
            markBlock blockIdx

            match r.Value with
            | None -> ()
            | Some v -> markValue v
        | _ -> ()

        for instr in block.Instr do
            match instr with
            | Call _
            | Load _
            | Store
            | Alloc ->
                markBlock blockIdx

                for value in instr.Value do
                    markValue value
            | _ -> ()

    for id in varList do
        let blockId = f.Var[id].Def
        markBlock blockId
        let block = f.Block[blockId]
        let findInstr id (i: Instr) = i.Target = id

        if block.Phi.ContainsKey id then
            for value in block.Phi[id] do
                markValue value
        else
            let instr = Array.find (findInstr id) block.Instr

            for value in instr.Value do
                markValue value

    let mapVarValue (idx, live) =
        if live then Some(Binding idx) else None

    let varValue = varLive |> Array.indexed |> Array.map mapVarValue

    removeVarAndBlock f varValue (removeOnlyMapping blockLive)

let adce = transRegional adceImpl
