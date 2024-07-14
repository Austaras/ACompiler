module Optimize.SSA

open System.Linq
open System.Collections.Generic

open Common.WorkList
open Common.Util.Util
open Optimize.FLIR

type DomTree = { ImmDom: int; Children: int[] }

type SSA(f: Func) =
    member _.DomFront() =

        let blockIndex = f.Block |> Array.indexed |> Array.map fst

        // calc dominance tree
        let dom = ResizeArray()

        for _ in blockIndex do
            dom.Add(Set(blockIndex))

        let todo = WorkList(blockIndex)

        for id in todo do
            let cfgData = f.CFG[id]
            let currDom = Set([| id |])

            let predDom =
                if cfgData.Pred.Length > 0 then
                    cfgData.Pred |> Seq.map (fun id -> dom[id]) |> Set.intersectMany
                else
                    Set.empty

            let currDom = Set.union currDom predDom

            if currDom <> dom[id] then
                for s in cfgData.Succ do
                    todo.Add s

                dom[id] <- currDom

        let domTree = ResizeArray()

        for _ in blockIndex do
            domTree.Add { ImmDom = 0; Children = [||] }

        for id in blockIndex do
            let mutable immDom = 0

            for currDom in dom[id] do
                if currDom <> id && currDom <> immDom && dom[currDom].Contains immDom then
                    immDom <- currDom

            domTree[id] <- { domTree[id] with ImmDom = immDom }

            if immDom <> id then
                domTree[immDom] <-
                    { domTree[immDom] with
                        Children = Array.append domTree[immDom].Children [| id |] }

        // calc dominance frontier
        let domFront = ResizeArray()

        for _ in blockIndex do
            domFront.Add(HashSet())

        let rec dominate parent child =
            let child = domTree[child]

            if child.ImmDom = parent then true
            else if child.ImmDom = 0 then false
            else dominate parent child.ImmDom

        let rec calc blockId =
            let currDF = HashSet()

            for succBlock in f.CFG[blockId].Succ do
                if domTree[succBlock].ImmDom <> blockId then
                    currDF.Add succBlock |> ignore

            for child in domTree[blockId].Children do
                calc child

                for front in domFront[child] do
                    if not (dominate blockId front) then
                        currDF.Add front |> ignore

            domFront[blockId] <- currDF

        calc 0

        domTree, domFront

    member _.PlacePhi(domFront: ResizeArray<HashSet<int>>) =
        let defVarInBlock = Dictionary<int, HashSet<int>>()
        let phiBlockOfVar = Dictionary<int, HashSet<int>>()

        let phiNode = ResizeArray()

        for _ in f.Block do
            phiNode.Add(Dictionary())

        for id, b in Array.indexed f.Block do
            if id = 0 then
                for p in f.Param do
                    if defVarInBlock.ContainsKey p then
                        defVarInBlock[p].Add id |> ignore
                    else
                        defVarInBlock.Add(p, HashSet [| id |])

            for instr in b.Instr do
                match instr.Target with
                | Some t ->
                    if defVarInBlock.ContainsKey t then
                        defVarInBlock[t].Add id |> ignore
                    else
                        defVarInBlock.Add(t, HashSet [| id |])
                | None -> ()

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
                                todo.Add front

        phiNode

    member _.RewriteBlock (domTree: ResizeArray<DomTree>) (phiNode: ResizeArray<Dictionary<int, int[]>>) =
        let var = ResizeArray(f.Var)

        let addVar id =
            var.Add var[id]
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

            let block = newBlock[blockId]

            let block = block.Rewrite reDef reUse

            newBlock[blockId] <- block

            for succ in f.CFG[blockId].Succ do
                let predIdx = Array.findIndex ((=) blockId) f.CFG[succ].Pred
                let currPhi = phiNode[succ]

                for varId in currPhi.Keys do
                    let choose = currPhi[varId]
                    let newVar = resolve newEnv choose[predIdx]

                    match newVar with
                    | Some newVar ->
                        Array.set choose predIdx newVar
                        currPhi[varId] <- choose
                    // only defined in one path
                    | None -> ()

                newBlock[succ] <- newBlock[succ]

            for child in domTree[blockId].Children do
                rewrite newEnv child

        rewrite [||] 0

        var, newBlock

    member _.Minimize
        (phiNode: ResizeArray<Dictionary<int, int[]>>)
        (var: ResizeArray<Var>)
        (newBlock: ResizeArray<Block>)
        =
        let shouldRemove = HashSet(seq { 0 .. var.Count - 1 })

        for block, currPhi in Seq.zip newBlock phiNode do
            let def i = shouldRemove.Remove i |> ignore

            let use_ value =
                match value with
                | Binding i -> shouldRemove.Remove i |> ignore
                | Const _ -> ()

            for choose in currPhi.Values do
                for c in choose do
                    use_ (Binding c)

            block.Analyze def use_

        let varMapping = ResizeArray()
        let mutable currIdx = 0

        for id in 0 .. var.Count - 1 do
            if shouldRemove.Contains id then
                varMapping.Add -1
            else
                varMapping.Add currIdx
                currIdx <- currIdx + 1

        let mapVar id = varMapping[id]

        let chooseVar id =
            if shouldRemove.Contains id then
                None
            else
                Some varMapping[id]

        let minimize (currPhi: Dictionary<int, int[]>, block: Block) =
            let rewritePhi (key, value) =
                if shouldRemove.Contains key then
                    None
                else
                    Some(mapVar key, Array.choose chooseVar value)

            let currPhi = currPhi |> Seq.map (|KeyValue|) |> Seq.choose rewritePhi |> Map.ofSeq

            let def id = varMapping[id]

            let use_ value =
                match value with
                | Const c -> Const c
                | Binding i -> Binding varMapping[i]

            { block.Rewrite def use_ with
                Phi = currPhi }

        let newBlock = newBlock |> Seq.zip phiNode |> Seq.map minimize |> Array.ofSeq

        let filterVar (idx, var) =
            if not (shouldRemove.Contains idx) then Some var else None

        let var = var |> Seq.indexed |> Seq.choose filterVar |> Array.ofSeq

        var, newBlock

    member this.Transform() =
        let domTree, domFront = this.DomFront()
        let phiNode = this.PlacePhi domFront
        let var, newBlock = this.RewriteBlock domTree phiNode
        let var, newBlock = this.Minimize phiNode var newBlock

        { f with Block = newBlock; Var = var }

let ssaImpl (f: Func) =
    let ssa = SSA f

    ssa.Transform()

let ssa = transRegional ssaImpl
