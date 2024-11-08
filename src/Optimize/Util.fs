module Optimize.Util

open System.Collections.Generic
open Optimize.FLIR

type WorkList<'T>(init: IEnumerable<'T>) =
    let list = ResizeArray<'T>(init)
    let mutable idx = 0
    let set = HashSet<'T>(init)

    member _.Add data =
        let inserted = set.Add data

        if inserted then
            list.Add data

        inserted

    member _.Contain data = set.Contains data

    member _.Next() =
        if idx < list.Count then
            let data = list[idx]
            set.Remove data |> ignore
            idx <- idx + 1
            Some data
        else
            None

    member _.IsEmpty() = idx >= list.Count

    member _.ToSeq() =
        seq {
            while idx < list.Count do
                let data = list[idx]
                yield data
                set.Remove data |> ignore
                idx <- idx + 1
        }

    interface System.Collections.IEnumerable with

        member this.GetEnumerator() = this.ToSeq().GetEnumerator()

    interface IEnumerable<'T> with

        member this.GetEnumerator() = this.ToSeq().GetEnumerator()

type DomTree = { ImmDom: int; Children: int[] }

let domFront (graph: GraphNode[]) =
    // calc dfs span tree
    let dfNum = Array.create graph.Length 0
    let revDf = Array.create graph.Length 0
    let parent = Array.create graph.Length 0

    let rec dfs idx count =
        dfNum[idx] <- count
        revDf[count] <- idx

        let fold count next =
            if dfNum[next] = 0 then
                parent[next] <- idx
                dfs next (count + 1)
            else
                count

        Array.fold fold count graph[idx].Succ

    dfs 0 0 |> ignore

    let semiDom = Array.create graph.Length 0
    let ancestor = Array.create graph.Length 0
    let bucket = graph |> Array.map (fun _ -> HashSet())
    let immDom = Array.create graph.Length 0
    let sameDom = Array.create graph.Length 0
    let lowest = Array.create graph.Length 0

    let rec findLowest node =
        let ance = ancestor[node]

        if ancestor[ance] <> 0 then
            let newAnce = findLowest ance
            ancestor[node] <- ancestor[ance]

            if dfNum[semiDom[newAnce]] < dfNum[semiDom[lowest[node]]] then
                lowest[node] <- newAnce

        lowest[node]

    let link ance node =
        ancestor[node] <- ance
        lowest[node] <- node

    // calc semi dom
    for i = graph.Length - 1 downto 1 do
        let node = revDf[i]
        let parentNode = parent[node]

        let mutable semi = parentNode

        for pred in graph[node].Pred do
            let semiCandidate =
                if dfNum[pred] <= dfNum[node] then
                    pred
                else
                    semiDom[findLowest pred]

            if dfNum[semiCandidate] < dfNum[semi] then
                semi <- semiCandidate

        semiDom[node] <- semi
        bucket[semi].Add(node) |> ignore
        link parentNode node

        // calc dom from semi dom, part 1
        for node in bucket[parentNode] do
            let y = findLowest node

            if semiDom[y] = semiDom[node] then
                immDom[node] <- parentNode
            else
                sameDom[node] <- y

        bucket[parentNode].Clear()

    // calc dom from semi dom, part 2
    for i = 1 to graph.Length - 1 do
        let node = revDf[i]

        if sameDom[node] <> 0 then
            immDom[node] <- immDom[sameDom[node]]

    // calc dominance tree
    let domTree = Array.map (fun immDom -> { ImmDom = immDom; Children = [||] }) immDom

    for node, immDom in Seq.indexed immDom do
        if node <> 0 then
            domTree[immDom] <-
                { domTree[immDom] with
                    Children = Array.append domTree[immDom].Children [| node |] }

    // calc dominance frontier
    let domFront = graph |> Array.map (fun _ -> HashSet())

    let rec dominate parent child =
        let child = domTree[child]

        if child.ImmDom = parent then true
        else if child.ImmDom = 0 then false
        else dominate parent child.ImmDom

    let rec calc blockId =
        let currDF = HashSet()

        for succBlock in graph[blockId].Succ do
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

let cdg (f: Func) =
    let last = f.CFG.Length + 1

    let isRet (idx, b) =
        match b.Trans with
        | Return _ -> Some idx
        | _ -> None

    let retIdx = Array.indexed f.Block |> Array.choose isRet

    let mapIdx arr =
        Array.map (fun idx -> last - idx - 1) arr

    let create idx =
        let idx = last - idx

        if idx = 0 then
            { Pred = [| last - 1; 0 |]
              Succ = [||] }
        else if idx = last then
            { Pred = [||]
              Succ = retIdx |> mapIdx |> Array.append [| last |] }
        else
            let node = f.CFG[idx - 1]

            let pred = mapIdx node.Succ

            let pred =
                if Array.contains (idx - 1) retIdx then
                    Array.append pred [| 0 |]
                else
                    pred

            let succ = mapIdx node.Pred
            let succ = if idx = 1 then Array.append [| last |] succ else succ

            { Pred = pred; Succ = succ }

    let reverseCFG = seq { 0..last } |> Seq.map create |> Array.ofSeq

    let _, domFront = domFront reverseCFG

    let res = Array.map (fun _ -> { Pred = [||]; Succ = [||] }) f.CFG

    for (idx, domFront) in Array.indexed domFront do
        let idx = last - idx

        for front in domFront do
            let front = last - front

            if idx > 0 && idx <= res.Length && front > 0 && front <= res.Length then
                let pred = res[front - 1]

                res[front - 1] <-
                    { pred with
                        Succ = Array.append pred.Succ [| idx - 1 |] }

                let succ = res[idx - 1]

                res[idx - 1] <-
                    { succ with
                        Pred = Array.append succ.Pred [| front - 1 |] }

    res

let removeOnlyMapping arr =
    arr |> Array.indexed |> Array.map (fun (idx, live) -> if live then idx else -1)

let removeVarAndBlock (f: Func) (varValue: Option<Value>[]) (blockMap: int[]) =
    let var = f.Var
    let block = f.Block
    let cfg = f.CFG
    let param = f.Param

    let varMapping = Array.create var.Length -1
    let mutable currIdx = 0

    for id = 0 to f.Var.Length - 1 do
        match varValue[id] with
        | None
        | Some(Const _) -> ()
        | Some(Binding id) ->
            varMapping[id] <- currIdx
            currIdx <- currIdx + 1

    let blockRemoved = Dictionary()
    let mutable currIdx = 0

    let mapIdx (idx, replace) =
        if replace = idx then
            currIdx <- currIdx + 1
            currIdx - 1
        else
            blockRemoved[idx] <- replace
            -1

    let blockMap = blockMap |> Array.indexed |> Array.map mapIdx

    for KeyValue(from, toIdx) in blockRemoved do
        if toIdx <> -1 then
            blockMap[from] <- blockMap[toIdx]

    let cfg = cfg |> Array.map (fun _ -> { Pred = [||]; Succ = [||] })

    let choosePhi value =
        match value with
        | Const _ -> Some value
        | Binding id ->
            match varValue[id] with
            | None -> None
            | Some(Const c) -> Some(Const c)
            | Some(Binding id) -> Some(Binding varMapping[id])

    let rewriteBlock (idx: int, block: Block) =
        let rewritePhi (key, value) =
            match varValue[key] with
            | None
            | Some(Const _) -> None
            | Some(Binding key) -> Some(varMapping[key], Array.choose choosePhi value)

        let phi = block.Phi |> Seq.map (|KeyValue|) |> Seq.choose rewritePhi |> Map.ofSeq
        let rewriteDef id = varMapping[id]

        let rewriteUse value =
            match value with
            | Const c -> Const c
            | Binding i ->
                match varValue[i] with
                | None -> failwith "Unreachable"
                | Some(Const c) -> Const c
                | Some(Binding i) -> Binding varMapping[i]

        let rewriteTx tx =
            match tx with
            | Jump j -> Jump { j with Target = blockMap[j.Target] }
            | Branch b ->
                let zero = blockMap[b.Zero]
                let one = blockMap[b.One]

                match b.Value with
                | Binding _ -> Branch { b with Zero = zero; One = one }
                | Const c ->
                    if c = uint64 0 then
                        Jump { Target = zero; Span = b.Span }
                    else
                        Jump { Target = one; Span = b.Span }

            | Switch _ -> failwith "Not Implemented"
            | Return r -> Return r
            | Unreachable r -> Unreachable r

        if blockRemoved.ContainsKey idx then
            None
        else
            let block = block.Rewrite rewriteDef rewriteUse
            let instr = Array.filter (fun (instr: Instr) -> instr.Target <> -1) block.Instr
            let tx = rewriteTx block.Trans

            for target in tx.Target() do
                let idx = blockMap[idx]

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
                    BlockId = blockMap[use_.BlockId] }
        | InPhi phi ->
            match varValue[phi] with
            | None
            | Some(Const _) -> None
            | Some(Binding phi) ->
                Some
                    { BlockId = blockMap[use_.BlockId]
                      Data = InPhi varMapping[phi] }
        | ForTarget target ->
            match varValue[target] with
            | None
            | Some(Const _) -> None
            | Some(Binding target) ->
                Some
                    { BlockId = blockMap[use_.BlockId]
                      Data = ForTarget varMapping[target] }

    let filterVar idx =
        match varValue[idx] with
        | Some(Binding id) ->
            Some
                { var[id] with
                    Def = blockMap[var[id].Def]
                    Use = Array.choose filterUse var[id].Use }
        | None
        | Some(Const _) -> None

    let var = seq { 0 .. var.Length - 1 } |> Seq.choose filterVar |> Array.ofSeq
    let param = Array.map (fun id -> varMapping[id]) param

    { f with
        Param = param
        Var = var
        Block = block
        CFG = cfg[.. block.Length - 1] }
