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

    member _.Value = value

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
                | Eq -> Known(if l = r then uint64 0 else uint64 1)
                | NotEq -> Known(if l = r then uint64 1 else uint64 0)
                | Lt false -> Known(if l < r then uint64 1 else uint64 0)
                | Lt true -> Known(if int64 l < int64 r then uint64 1 else uint64 0)
                | LtEq(_) -> failwith "Not Implemented"
                | GtEq(_) -> failwith "Not Implemented"
                | Gt(_) -> failwith "Not Implemented"
        | Unary(_) -> failwith "Not Implemented"
        | Store -> failwith "Not Implemented"

let sccpImpl (f: Func) =
    let var = f.Var
    let block = f.Block
    let cfg = f.CFG

    let varValue = VarValue var.Length
    let blockReachable = Array.create block.Length false
    blockReachable[0] <- true

    for param in f.Param do
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
                            if blockReachable[f.CFG[blockId].Pred[idx]] then
                                varValue.SetValue phiVar Top

                                match prevValue with
                                | Top -> ()
                                | Known _
                                | Bottom -> varList.Add phiVar |> ignore
                        | Known v ->
                            let calcPhi res (idx, phiValue) =
                                let predBlock = f.CFG[blockId].Pred[idx]

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
                            | Known _, Known _ -> varList.Add phiVar |> ignore
                            | _ -> ()

                    | ForTarget target ->
                        let prevValue = varValue.GetValue target
                        let instr = Array.find (fun (i: Instr) -> i.Target = target) block[blockId].Instr

                        let value = varValue.Eval instr

                        varValue.SetValue target value

                        match prevValue, value with
                        | Known _, Top
                        | Bottom, Known _
                        | Known _, Known _ -> varList.Add target |> ignore
                        | _ -> ()

        match blockList.Next() with
        | None -> ()
        | Some blockId ->
            for KeyValue(phiVar, value) in block[blockId].Phi do
                let prevValue = varValue.GetValue phiVar

                let calcPhi res (idx, phiValue) =
                    let predBlock = f.CFG[blockId].Pred[idx]

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
                | Known _, Known _ -> varList.Add phiVar |> ignore
                | _ -> ()

            for instr in block[blockId].Instr do
                let prevValue = varValue.GetValue instr.Target

                let value = varValue.Eval instr

                varValue.SetValue instr.Target value

                match prevValue, value with
                | Known _, Top
                | Bottom, Known _
                | Known _, Known _ -> varList.Add instr.Target |> ignore
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

    let varMapping = Array.create var.Length -1
    let mutable currIdx = 0

    for id = 0 to var.Length - 1 do
        match varValue.GetValue id with
        | Known _
        | Bottom -> ()
        | Top ->
            varMapping[id] <- currIdx
            currIdx <- currIdx + 1

    let blockMapping = Array.create block.Length -1
    let mutable currIdx = 0

    for idx, reachable in Array.indexed blockReachable do
        if reachable then
            blockMapping[idx] <- currIdx
            currIdx <- currIdx + 1

    let cfg = cfg |> Array.map (fun _ -> { Pred = [||]; Succ = [||] })

    let choosePhi value =
        match value with
        | Const _ -> Some value
        | Binding id ->
            match varValue.GetValue id with
            | Bottom -> None
            | Known c -> Some(Const c)
            | Top -> Some(Binding varMapping[id])

    let rewriteBlock (idx: int, block: Block) =
        let rewritePhi (key, value) =
            match varValue.GetValue key with
            | Known _
            | Bottom -> None
            | Top -> Some(varMapping[key], Array.choose choosePhi value)

        let phi = block.Phi |> Seq.map (|KeyValue|) |> Seq.choose rewritePhi |> Map.ofSeq
        let rewriteDef id = varMapping[id]

        let rewriteUse value =
            match value with
            | Const c -> Const c
            | Binding i ->
                match varValue.GetValue i with
                | Bottom -> failwith "Unreachable"
                | Known v -> Const v
                | Top -> Binding varMapping[i]

        let rewriteTx tx =
            match tx with
            | Jump j ->
                Jump
                    { j with
                        Target = blockMapping[j.Target] }
            | Branch b ->
                let zero = blockMapping[b.Zero]
                let one = blockMapping[b.One]

                match b.Value with
                | Binding _ -> Branch { b with Zero = zero; One = one }
                | Const c ->
                    if c = uint64 0 then
                        Jump { Target = zero; Span = b.Span }
                    else
                        Jump { Target = one; Span = b.Span }

            | Switch(_) -> failwith "Not Implemented"
            | Return r -> Return r
            | Unreachable r -> Unreachable r

        if blockMapping[idx] = -1 then
            None
        else
            let block = block.Rewrite rewriteDef rewriteUse
            let instr = Array.filter (fun (instr: Instr) -> instr.Target <> -1) block.Instr
            let tx = rewriteTx block.Trans

            for target in tx.Target() do
                let idx = blockMapping[idx]

                cfg[idx] <-
                    { cfg[idx] with
                        Succ = Array.append cfg[idx].Succ [| target |] }

                cfg[target] <-
                    { cfg[target] with
                        Pred = Array.append cfg[target].Pred [| idx |] }

            Some { Instr = instr; Phi = phi; Trans = tx }

    let block = block |> Array.indexed |> Array.choose rewriteBlock

    let filterUse use_ =
        match use_.Data with
        | InTx ->
            Some
                { use_ with
                    BlockId = blockMapping[use_.BlockId] }
        | InPhi phi ->
            match varValue.GetValue phi with
            | Known _
            | Bottom -> None
            | Top ->
                Some
                    { BlockId = blockMapping[use_.BlockId]
                      Data = InPhi varMapping[phi] }
        | ForTarget target ->
            match varValue.GetValue target with
            | Known _
            | Bottom -> None
            | Top ->
                Some
                    { BlockId = blockMapping[use_.BlockId]
                      Data = ForTarget varMapping[target] }

    let filterVar idx =
        match varValue.GetValue idx with
        | Top ->
            Some
                { var[idx] with
                    Def = blockMapping[var[idx].Def]
                    Use = Array.choose filterUse var[idx].Use }
        | Known _
        | Bottom -> None

    let var = seq { 0 .. var.Length - 1 } |> Seq.choose filterVar |> Array.ofSeq
    let param = Array.map (fun id -> varMapping[id]) f.Param

    { f with
        Param = param
        Var = var
        Block = block
        CFG = cfg }

let sccp = transRegional sccpImpl
