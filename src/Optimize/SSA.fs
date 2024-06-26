module Optimize.SSA

open System.Linq
open System.Collections.Generic

open Common.Util.Util
open Optimize.FLIR

type SSA(f: Func) =
    let var = ResizeArray(f.Var)
    let def = ResizeArray<Dictionary<int, int>>()
    let phi = ResizeArray<Dictionary<int, int[]>>()
    let defined = HashSet()

    do
        for _ in 0 .. f.Block.Length - 1 do
            def.Add(Dictionary())

        for p in f.Param do
            defined.Add p |> ignore

    member _.AddVar id =
        var.Add var[id]
        let newId = var.Count - 1
        newId

    member this.RewriteBlock blockId (b: Block) =
        let currDef = def[blockId]
        let phiRewrite = Dictionary()

        if blockId = 0 then
            for p in f.Param do
                currDef.Add(p, p)

        let resDef target =
            if currDef.ContainsKey target then
                let newId = this.AddVar target
                currDef[target] <- newId
                newId
            else if defined.Contains target then
                let newId = this.AddVar target
                currDef[target] <- newId
                newId
            else
                defined.Add target |> ignore
                currDef.Add(target, target)
                target

        let resUse v =
            match v with
            | Const c -> Const c
            | Binding varId ->
                if currDef.ContainsKey varId then
                    Binding currDef[varId]
                else if phi[blockId].ContainsKey varId then
                    let newId = this.AddVar varId
                    currDef.Add(varId, newId)
                    phiRewrite.Add(newId, varId)
                    Binding newId
                else
                    let visited = HashSet([| blockId |])
                    let todo = ResizeArray(f.CFG[blockId].Pred)
                    let mutable idx = 0
                    let mutable res = None

                    while idx < todo.Count && res = None do
                        let pred = todo[idx]

                        if def[pred].ContainsKey varId then
                            res <- Some(def[pred][varId])
                        else
                            for p in f.CFG[pred].Pred do
                                if not (visited.Contains p) then
                                    visited.Add p |> ignore
                                    todo.Add p

                        idx <- idx + 1

                    match res with
                    | None -> failwith "Unreachable"
                    | Some prev -> Binding prev

        let rewrite instr =
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

        let instr = Array.map rewrite b.Instr

        let trans =
            match b.Trans with
            | Branch b -> Branch { b with Value = resUse b.Value }
            | Return r ->
                let value =
                    match r.Value with
                    | None -> None
                    | Some v -> Some(resUse v)

                Return { r with Value = value }
            | Switch s -> Switch { s with Value = resUse s.Value }
            | Jump _
            | Unreachable _ -> b.Trans

        for varId in phi[blockId].Keys do
            if not (currDef.ContainsKey varId) then
                let newId = this.AddVar varId
                currDef.Add(varId, newId)
                phiRewrite.Add(newId, varId)

        { b with Instr = instr; Trans = trans }, phiRewrite

    member this.Transform() =
        let block = ResizeArray(f.Block)
        let accDef = ResizeArray()

        for id, b in Array.indexed f.Block do
            let currDef = Dictionary()

            for instr in b.Instr do
                match instr.Target with
                | Some t -> currDef[t] <- id
                | None -> ()

            accDef.Add currDef
            phi.Add(Dictionary())

        for p in f.Param do
            accDef[0][p] <- 0

        let todo = ResizeArray([| for i in 0 .. f.Block.Length - 1 -> i |])
        let mutable idx = 0

        while idx < todo.Count do
            let currBlock = todo[idx]
            let prevDef = Dictionary<int, HashSet<int>>()

            for p in f.CFG[currBlock].Pred do
                for KeyValue(var, blockId) in accDef[p] do
                    if prevDef.ContainsKey var then
                        prevDef[var].Add blockId |> ignore
                    else
                        prevDef[var] <- HashSet([| blockId |])

            let mutable changed = false

            for KeyValue(var, blockId) in prevDef do
                if blockId.Count > 1 then
                    phi[currBlock][var] <- blockId.ToArray()

                    if not (accDef[currBlock].ContainsKey var) then
                        accDef[currBlock].Add(var, currBlock)
                        changed <- true
                    else if accDef[currBlock][var] <> currBlock then
                        accDef[currBlock][var] <- currBlock
                        changed <- true

                else if not (accDef[currBlock].ContainsKey var) then
                    accDef[currBlock].Add(var, blockId.ToArray()[0])
                    changed <- true

            if changed then
                for s in f.CFG[currBlock].Succ do
                    todo.Add s

            idx <- idx + 1

        let phiRewrite = ResizeArray()

        for id in 0 .. block.Count - 1 do
            let newBlock, phi = this.RewriteBlock id block[id]
            block[id] <- newBlock
            phiRewrite.Add phi

        for id in 0 .. block.Count - 1 do
            let phiValue _ origin =
                let block = phi[id][origin]

                let resolve blockId =
                    let def = def[blockId]
                    if def.ContainsKey origin then Some def[origin] else None

                Array.choose resolve block

            let currPhi = phiRewrite[id] |> dictToMap |> Map.map phiValue
            block[id] <- { block[id] with Phi = currPhi }

        { f with
            Var = var.ToArray()
            Block = block.ToArray() }

let ssaImpl (f: Func) =
    let ssa = SSA f

    ssa.Transform()

let ssa = transRegional ssaImpl
