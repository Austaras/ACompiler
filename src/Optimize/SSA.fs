module Optimize.SSA

open System.Linq
open System.Collections.Generic

open Common.WorkList
open Common.Util.Util
open Optimize.FLIR

type DomTree = { ImmDom: int; Children: int[] }

type SSA(f: Func) =
    member this.Transform() =
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

        // place phi node
        let defVarInBlock = Dictionary<int, HashSet<int>>()
        let phiBlockOfVar = Dictionary<int, HashSet<int>>()

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
                            let phi = f.Block[front].Phi
                            let value = Array.create f.CFG[front].Pred.Length var
                            let phi = Map.add var value phi
                            Array.set f.Block front { f.Block[front] with Phi = phi }

                            if not (defVarInBlock[var].Contains front) then
                                todo.Add front

        let var = ResizeArray(f.Var)

        let addVar id =
            var.Add var[id]
            var.Count - 1

        let defined = HashSet()

        for p in f.Param do
            defined.Add p |> ignore

        // rewrite block
        let rec rewrite env blockId =
            let currEnv = Dictionary()
            let newEnv = Array.append env [| currEnv |]

            if blockId = 0 then
                for p in f.Param do
                    currEnv.Add(p, p)

            let phi = Dictionary()

            let resDef target =
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

            let resUse v =
                match v with
                | Const c -> Const c
                | Binding varId ->
                    if currEnv.ContainsKey varId then
                        Binding currEnv[varId]
                    else if f.Block[blockId].Phi.ContainsKey varId then
                        let choose = f.Block[blockId].Phi[varId]
                        let newId = addVar varId
                        currEnv.Add(varId, newId)
                        phi.Add(newId, choose)
                        Binding newId
                    else
                        resolve env varId |> Option.get |> Binding

            let rewriteInstr instr =
                match instr with
                | Assign a ->
                    Assign
                        { a with
                            Value = resUse a.Value
                            Target = resDef a.Target }
                | Unary u ->
                    Unary
                        { u with
                            Value = resUse u.Value
                            Target = resDef u.Target }
                | Binary b ->
                    Binary
                        { b with
                            Left = resUse b.Left
                            Right = resUse b.Right
                            Target = resDef b.Target }
                | Call c ->
                    Call
                        { c with
                            Arg = Array.map resUse c.Arg
                            Target = resDef c.Target }
                | Load -> failwith "Not Implemented"
                | Store -> failwith "Not Implemented"
                | Alloc -> failwith "Not Implemented"

            let block = f.Block[blockId]

            let instr = Array.map rewriteInstr block.Instr

            let trans =
                match block.Trans with
                | Branch b -> Branch { b with Value = resUse b.Value }
                | Return r ->
                    let value =
                        match r.Value with
                        | None -> None
                        | Some v -> Some(resUse v)

                    Return { r with Value = value }
                | Switch s -> Switch { s with Value = resUse s.Value }
                | Jump _
                | Unreachable _ -> block.Trans

            for KeyValue(var, choose) in f.Block[blockId].Phi do
                if not (currEnv.ContainsKey var) then
                    let newId = addVar var
                    currEnv.Add(var, newId)
                    phi.Add(newId, choose)

            let newBlock =
                { block with
                    Phi = dictToMap phi
                    Instr = instr
                    Trans = trans }

            Array.set f.Block blockId newBlock

            for succ in f.CFG[blockId].Succ do
                let predIdx = Array.findIndex ((=) blockId) f.CFG[succ].Pred

                let rewritePhi (varId, choose: int[]) =
                    let newVar = resolve newEnv choose[predIdx]

                    match newVar with
                    | Some newVar ->
                        Array.set choose predIdx newVar
                        Some(varId, choose)
                    // only defined in one path
                    | None -> None

                let phi = f.Block[succ].Phi |> Map.toSeq |> Seq.choose rewritePhi |> Map.ofSeq

                let newBlock = { f.Block[succ] with Phi = phi }

                Array.set f.Block succ newBlock

            for child in domTree[blockId].Children do
                rewrite newEnv child

        rewrite [||] 0

        { f with Var = var.ToArray() }

let ssaImpl (f: Func) =
    let ssa = SSA f

    ssa.Transform()

let ssa = transRegional ssaImpl
