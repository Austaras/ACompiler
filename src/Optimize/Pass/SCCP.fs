// Sparse Condition COnstant Propagation
module Optimize.Pass.SCCP

open Optimize.FLIR
open Optimize.Util

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

    member _.GetValue id = value[id]
    member _.SetValue id v = value[id] <- v

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
            | _, Bottom -> Bottom
            | Known l, Known r ->
                let value =
                    match b.Op with
                    | Add -> l + r
                    | Sub -> l - r
                    | Mul -> l * r
                    | Div -> l / r
                    | Rem -> failwith "Not Implemented"
                    | Xor -> failwith "Not Implemented"
                    | And -> failwith "Not Implemented"
                    | Or -> failwith "Not Implemented"
                    | Shl -> failwith "Not Implemented"
                    | Shr(_) -> failwith "Not Implemented"
                    | Eq -> if l = r then uint64 0 else uint64 1
                    | NotEq -> if l = r then uint64 1 else uint64 0
                    | Lt false -> if l < r then uint64 1 else uint64 0
                    | Lt true -> if int64 l < int64 r then uint64 1 else uint64 0
                    | LtEq false -> if int64 l <= int64 r then uint64 1 else uint64 0
                    | LtEq true -> if l <= r then uint64 1 else uint64 0
                    | GtEq false -> if l >= r then uint64 1 else uint64 0
                    | GtEq true -> if int64 l >= int64 r then uint64 1 else uint64 0
                    | Gt false -> if l > r then uint64 1 else uint64 0
                    | Gt true -> if int64 l > int64 r then uint64 1 else uint64 0

                Known value
        | Unary u ->
            match this.ValueOf u.Value with
            | Bottom -> Bottom
            | Top -> Top
            | Known c ->
                let value =
                    match u.Op with
                    | Neg -> uint64 0 - c
                    | Not -> ~~~c
                    | Ext(_) -> failwith "Not Implemented"

                Known value
        | Store -> failwith "Not Implemented"

let calc (var: Var[]) (param: int[]) (block: Block[]) (cfg: GraphNode[]) =
    let varValue = VarValue var.Length
    let blockReachable = Array.create block.Length false
    blockReachable[0] <- true

    for param in param do
        varValue.SetValue param Top

    let varList = WorkList(seq { 0 .. var.Length - 1 })
    let blockList = WorkList([ 0 ])

    while not (varList.IsEmpty()) || not (blockList.IsEmpty()) do
        match varList.Next() with
        | None -> ()
        | Some varId ->
            for { BlockId = blockId; Data = data } in var[varId].Use do
                if blockReachable[blockId] then
                    match data with
                    | InTx ->
                        match varValue.GetValue varId with
                        | Bottom -> ()
                        | Top ->
                            match block[blockId].Trans with
                            | Jump _
                            | Unreachable _ -> failwith "Unreachable"
                            | Return _ -> ()
                            | Branch b ->
                                let prevBlock = blockReachable[b.Zero]
                                blockReachable[b.Zero] <- true

                                if not prevBlock then
                                    blockList.Add b.Zero |> ignore

                                let prevBlock = blockReachable[b.One]
                                blockReachable[b.One] <- true

                                if not prevBlock then
                                    blockList.Add b.One |> ignore
                            | Switch s ->
                                for targetBlock, _ in s.Dest do
                                    let prevBlock = blockReachable[targetBlock]
                                    blockReachable[targetBlock] <- true

                                    if not prevBlock then
                                        blockList.Add targetBlock |> ignore
                        | Known v ->
                            match block[blockId].Trans with
                            | Jump _
                            | Unreachable _ -> failwith "Unreachable"
                            | Return _ -> ()
                            | Branch b ->
                                if v = uint64 0 then
                                    let prevBlock = blockReachable[b.Zero]
                                    blockReachable[b.Zero] <- true

                                    if not prevBlock then
                                        blockList.Add b.Zero |> ignore
                                else
                                    let prevBlock = blockReachable[b.One]
                                    blockReachable[b.One] <- true

                                    if not prevBlock then
                                        blockList.Add b.One |> ignore
                            | Switch s ->
                                for targetBlock, targetValue in s.Dest do
                                    if v = targetValue then
                                        let prevBlock = blockReachable[targetBlock]
                                        blockReachable[targetBlock] <- true

                                        if not prevBlock then
                                            blockList.Add targetBlock |> ignore
                    | InPhi phiVar ->
                        let phi = block[blockId].Phi[phiVar]
                        let idx = Array.findIndex ((=) (Binding varId)) phi
                        let prevValue = varValue.GetValue phiVar

                        match varValue.GetValue varId with
                        | Bottom -> ()
                        | Top ->
                            if blockReachable[cfg[blockId].Pred[idx]] then
                                varValue.SetValue phiVar Top

                                match prevValue with
                                | Top -> ()
                                | Known _
                                | Bottom -> varList.Add phiVar |> ignore
                        | Known v ->
                            let calcPhi res (idx, phiValue) =
                                let predBlock = cfg[blockId].Pred[idx]

                                if blockReachable[predBlock] then
                                    let value = varValue.ValueOf phiValue

                                    match res, value with
                                    | Known r, Known v when r = v -> Known r
                                    | Known _, Known _
                                    | Top, _
                                    | _, Top -> Top
                                    | Bottom, v
                                    | v, Bottom -> v
                                else
                                    res

                            let res = phi |> Array.indexed |> Array.fold calcPhi Bottom
                            varValue.SetValue phiVar res

                            match prevValue, res with
                            | Known _, Top
                            | Bottom, Known _
                            | Known _, Known _ when prevValue <> res -> varList.Add phiVar |> ignore
                            | _ -> ()

                    | ForTarget target ->
                        let prevValue = varValue.GetValue target
                        let instr = Array.find (fun (i: Instr) -> i.Target = target) block[blockId].Instr

                        let value = varValue.Eval instr

                        varValue.SetValue target value

                        match prevValue, value with
                        | Known _, Top
                        | Bottom, Known _
                        | Known _, Known _ when prevValue <> value -> varList.Add target |> ignore
                        | _ -> ()

        match blockList.Next() with
        | None -> ()
        | Some blockId ->
            for KeyValue(phiVar, value) in block[blockId].Phi do
                let prevValue = varValue.GetValue phiVar

                let calcPhi res (idx, phiValue) =
                    let predBlock = cfg[blockId].Pred[idx]

                    if blockReachable[predBlock] then
                        let value = varValue.ValueOf phiValue

                        match res, value with
                        | Known r, Known v when r = v -> Known r
                        | Known _, Known _
                        | Top, _
                        | _, Top -> Top
                        | Bottom, v
                        | v, Bottom -> v
                    else
                        res

                let res = value |> Array.indexed |> Array.fold calcPhi Bottom

                varValue.SetValue phiVar res

                match prevValue, res with
                | Known _, Top
                | Bottom, Known _
                | Known _, Known _ when prevValue <> res -> varList.Add phiVar |> ignore
                | _ -> ()

            for instr in block[blockId].Instr do
                let prevValue = varValue.GetValue instr.Target

                let value = varValue.Eval instr

                varValue.SetValue instr.Target value

                match prevValue, value with
                | Known _, Top
                | Bottom, Known _
                | Known _, Known _ when prevValue <> value -> varList.Add instr.Target |> ignore
                | _ -> ()

            match block[blockId].Trans with
            | Jump j ->
                let prevBlock = blockReachable[j.Target]
                blockReachable[j.Target] <- true

                if not prevBlock then
                    blockList.Add j.Target |> ignore
            | Branch b ->
                match varValue.ValueOf b.Value with
                | Bottom -> ()
                | Top ->
                    let prevBlock = blockReachable[b.Zero]
                    blockReachable[b.Zero] <- true

                    if not prevBlock then
                        blockList.Add b.Zero |> ignore

                    let prevBlock = blockReachable[b.One]
                    blockReachable[b.One] <- true

                    if not prevBlock then
                        blockList.Add b.One |> ignore
                | Known v ->
                    if v = uint64 0 then
                        let prevBlock = blockReachable[b.Zero]
                        blockReachable[b.Zero] <- true

                        if not prevBlock then
                            blockList.Add b.Zero |> ignore
                    else
                        let prevBlock = blockReachable[b.One]
                        blockReachable[b.One] <- true

                        if not prevBlock then
                            blockList.Add b.One |> ignore
            // TODO: switch default
            | Switch s ->
                match varValue.ValueOf s.Value with
                | Bottom -> ()
                | Top ->
                    for targetBlock, _ in s.Dest do
                        let prevBlock = blockReachable[targetBlock]
                        blockReachable[targetBlock] <- true

                        if not prevBlock then
                            blockList.Add targetBlock |> ignore
                | Known v ->
                    for targetBlock, targetValue in s.Dest do
                        if v = targetValue then
                            let prevBlock = blockReachable[targetBlock]
                            blockReachable[targetBlock] <- true

                            if not prevBlock then
                                blockList.Add targetBlock |> ignore
            | Return _
            | Unreachable _ -> ()

    varValue, blockReachable

let sccpImpl (f: Func) =
    let var = f.Var
    let param = f.Param
    let block = f.Block
    let cfg = f.CFG

    let varValue, blockReachable = calc var param block cfg

    let getVarValue id =
        match varValue.GetValue id with
        | Bottom -> None
        | Known c -> Some(Const c)
        | Top -> Some(Binding id)

    let varValue = seq { 0 .. var.Length - 1 } |> Seq.map getVarValue |> Array.ofSeq

    removeVarAndBlock f varValue (removeOnlyMapping blockReachable)

let sccp = transRegional sccpImpl
