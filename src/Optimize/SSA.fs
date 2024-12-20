module Optimize.SSA

open System.Collections.Generic

open Common.Span
open Optimize.FLIR
open Optimize.Util

type SSA(f: Func) =
    member _.PlacePhi(domFront: HashSet<int>[]) =
        let defVarInBlock = Dictionary<int, HashSet<int>>()
        let phiBlockOfVar = Dictionary<int, HashSet<int>>()

        let phiNode = Array.map (fun _ -> Dictionary()) f.Block

        for id, b in Array.indexed f.Block do
            if id = 0 then
                for p in f.Param do
                    if defVarInBlock.ContainsKey p then
                        defVarInBlock[p].Add id |> ignore
                    else
                        defVarInBlock.Add(p, HashSet [| id |])

            for instr in b.Instr do
                let t = instr.Target

                if defVarInBlock.ContainsKey t then
                    defVarInBlock[t].Add id |> ignore
                else
                    defVarInBlock.Add(t, HashSet [| id |])

        for KeyValue(var, defIn) in defVarInBlock do
            if defIn.Count > 1 then
                let todo = WorkList(defIn)

                for node in todo do
                    for front in domFront[node] do
                        if not (phiBlockOfVar.ContainsKey front) then
                            phiBlockOfVar.Add(front, HashSet())

                        if not (phiBlockOfVar[front].Contains var) then
                            phiBlockOfVar[front].Add var |> ignore
                            let value = Array.create f.CFG[front].Pred.Length var
                            phiNode[front].Add(var, value)

                            if not (defVarInBlock[var].Contains front) then
                                todo.Add front |> ignore

        phiNode

    member _.RewriteBlock (domTree: DomTree[]) (phiNode: Dictionary<int, int[]>[]) =
        let var = ResizeArray(f.Var)

        let addVar id =
            var.Add { var[id] with Use = [||] }
            var.Count - 1

        let defined = HashSet()

        for p in f.Param do
            defined.Add p |> ignore

        let newBlock = ResizeArray(f.Block)

        // rewrite block
        let rec rewrite env blockId =
            let currEnv = Dictionary()
            let newEnv = Array.append env [| currEnv |]

            if blockId = 0 then
                for p in f.Param do
                    currEnv.Add(p, p)

            let newPhi = Dictionary()

            for KeyValue(var, choose) in phiNode[blockId] do
                let newId = addVar var
                currEnv.Add(var, newId)
                newPhi.Add(newId, choose)

            phiNode[blockId] <- newPhi

            let reDef target =
                if defined.Contains target then
                    let newId = addVar target
                    currEnv[target] <- newId
                    newId
                else
                    defined.Add target |> ignore
                    currEnv.Add(target, target)
                    target

            let rec resolve (env: Dictionary<int, int>[]) var =
                let last = env.Length - 1

                if env[last].ContainsKey var then Some(env[last][var])
                else if last = 0 then None
                else resolve env[0 .. last - 1] var

            let reUse v =
                match v with
                | Const c -> Const c
                | Binding varId ->
                    if currEnv.ContainsKey varId then
                        Binding currEnv[varId]
                    else
                        resolve env varId |> Option.get |> Binding

            let reInstr (instrId, instr) =
                let instr =
                    match instr with
                    | Assign a ->
                        Assign
                            { a with
                                Value = reUse a.Value
                                Target = reDef a.Target }
                    | Unary u ->
                        Unary
                            { u with
                                Value = reUse u.Value
                                Target = reDef u.Target }
                    | Binary b ->
                        Binary
                            { b with
                                Left = reUse b.Left
                                Right = reUse b.Right
                                Target = reDef b.Target }
                    | Call c ->
                        Call
                            { c with
                                Arg = Array.map reUse c.Arg
                                Target = reDef c.Target }
                    | Load l ->
                        Load
                            { l with
                                Base = reUse l.Base
                                Offset = reUse l.Offset
                                Target = reDef l.Target }
                    | Store -> failwith "Not Implemented"
                    | Alloc -> failwith "Not Implemented"

                let target = instr.Target
                var[target] <- { var[target] with Def = blockId }

                let getBinding v =
                    match v with
                    | Binding i -> Some i
                    | Const _ -> None

                let binding = instr.Value |> Seq.choose getBinding |> Array.ofSeq

                for id in binding do
                    let useData =
                        { BlockId = blockId
                          Data = ForTarget target }

                    var[id] <- var[id].WithUse useData

                instr

            let block = newBlock[blockId]
            let instr = block.Instr |> Array.indexed |> Array.map reInstr

            let useInTrans v =
                match v with
                | Const _ -> ()
                | Binding id ->
                    let useData = { BlockId = blockId; Data = InTx }

                    var[id] <- var[id].WithUse useData

            let trans =
                match block.Trans with
                | Branch b ->
                    let value = reUse b.Value
                    useInTrans value
                    Branch { b with Value = value }
                | Return r ->
                    let value =
                        match r.Value with
                        | None -> None
                        | Some value ->
                            let value = reUse value
                            useInTrans value
                            Some value

                    Return { r with Value = value }
                | Indirect s ->
                    let value = reUse s.Value
                    useInTrans value
                    Indirect { s with Value = value }
                | Jump _
                | Unreachable _ -> block.Trans

            let block =
                { block with
                    Instr = instr
                    Trans = trans }

            newBlock[blockId] <- block

            for succ in f.CFG[blockId].Succ do
                let predIdx = Array.findIndex ((=) blockId) f.CFG[succ].Pred
                let currPhi = phiNode[succ]

                for varId in currPhi.Keys do
                    let choose = currPhi[varId]
                    let newVar = resolve newEnv choose[predIdx]

                    match newVar with
                    | Some newVar -> choose[predIdx] <- newVar
                    // only defined in one path
                    | None -> ()

            for child in domTree[blockId].Children do
                rewrite newEnv child

        rewrite [||] 0

        for idx in 0 .. newBlock.Count - 1 do
            let phi =
                phiNode[idx]
                |> Seq.map (fun (KeyValue(var, value)) -> var, Array.map Binding value)
                |> Map.ofSeq

            for KeyValue(phiVar, value) in phiNode[idx] do
                var[phiVar] <- { var[phiVar] with Def = idx }

                for value in value do
                    let use_ = { BlockId = idx; Data = InPhi phiVar }
                    var[value] <- var[value].WithUse use_

            newBlock[idx] <- { newBlock[idx] with Phi = phi }

        var, newBlock

    member _.EdgeSplit(block: ResizeArray<Block>) =
        let cfg = ResizeArray(f.CFG)

        for idx in 0 .. f.CFG.Length - 1 do
            for sIdx in cfg[idx].Succ do
                let node = cfg[idx]
                let succ = cfg[sIdx]

                if node.Succ.Length > 1 && succ.Pred.Length > 1 then
                    let newBlock =
                        let newBlock = block.Count

                        block.Add(
                            { Phi = Map.empty
                              Instr = [||]
                              Trans = Jump { Target = sIdx; Span = Span.dummy } }
                        )

                        cfg.Add { Pred = [||]; Succ = [| sIdx |] }

                        newBlock

                    let mapBlock id = if id = sIdx then newBlock else id

                    let newTx =
                        match block[idx].Trans with
                        | Jump _
                        | Return _
                        | Unreachable _ -> failwith "Unreachable"
                        | Branch b ->
                            let b =
                                if b.One = sIdx then
                                    { b with One = newBlock }
                                else
                                    { b with Zero = newBlock }

                            Branch b
                        | Indirect s ->
                            let newDest = Array.map mapBlock s.Dest

                            Indirect { s with Dest = newDest }

                    block[idx] <- { block[idx] with Trans = newTx }

                    let newSucc: int array = Array.map mapBlock node.Succ

                    cfg[idx] <- { cfg[idx] with Succ = newSucc }

                    cfg[newBlock] <-
                        { cfg[newBlock] with
                            Pred = Array.append cfg[newBlock].Pred [| idx |] }

                    let newPred = Array.map (fun id -> if id = idx then newBlock else id) succ.Pred

                    cfg[sIdx] <- { cfg[sIdx] with Pred = newPred }

        block, cfg

    member this.Transform() =
        let domTree, domFront = domFront f.CFG
        let phiNode = this.PlacePhi domFront
        let var, newBlock = this.RewriteBlock domTree phiNode
        let newBlock, cfg = this.EdgeSplit newBlock

        { f with
            Block = newBlock.ToArray()
            Var = var.ToArray()
            CFG = cfg.ToArray() }

let ssaImpl (f: Func) =
    let ssa = SSA f

    ssa.Transform()

let ssa = transRegional ssaImpl
