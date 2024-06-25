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

    member this.RewriteBlock id (b: Block) =
        let currDef = def[id]
        let currPhi = Dictionary()

        if id = 0 then
            for p in f.Param do
                currDef.Add(p, p)

        let resDef t =
            if currDef.ContainsKey t then
                let newId = this.AddVar t
                currDef[t] <- newId
                newId
            else if defined.Contains t then
                let newId = this.AddVar t
                currDef[t] <- newId
                newId
            else
                defined.Add t |> ignore
                currDef.Add(t, t)
                t

        let resUse v =
            match v with
            | Const c -> Const c
            | Binding i ->
                if currDef.ContainsKey i then
                    Binding currDef[i]
                else if phi[id].ContainsKey i then
                    let newId = this.AddVar i
                    currDef.Add(i, newId)
                    currPhi.Add(newId, [| i |])
                    Binding newId
                else
                    let visited = HashSet([| id |])
                    let todo = ResizeArray(f.CFG[id].Pred)
                    let mutable idx = 0
                    let mutable res = None

                    while idx < todo.Count && res = None do
                        let pred = todo[idx]

                        if def[pred].ContainsKey i then
                            res <- Some(def[pred][i])
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

        for var in phi[id].Keys do
            if not (currDef.ContainsKey var) then
                let newId = this.AddVar var
                currPhi.Add(newId, [| var |])

        { b with
            Phi = dictToMap currPhi
            Instr = instr
            Trans = trans }

    member this.Transform() =
        let block = ResizeArray(f.Block)
        let defInBlock = ResizeArray()

        for id, b in Array.indexed f.Block do
            let currDef = Dictionary()

            for instr in b.Instr do
                currDef[instr.Target] <- id

            defInBlock.Add currDef
            phi.Add(Dictionary())

        for p in f.Param do
            defInBlock[0][p] <- 0

        let todo = ResizeArray([| for i in 0 .. f.Block.Length - 1 -> i |])
        let mutable idx = 0

        while idx < todo.Count do
            let id = todo[idx]
            let prevDef = Dictionary<int, HashSet<int>>()

            for p in f.CFG[id].Pred do
                for KeyValue(var, blockId) in defInBlock[p] do
                    if prevDef.ContainsKey var then
                        prevDef[var].Add blockId |> ignore
                    else
                        prevDef[var] <- HashSet([| blockId |])

            let mutable changed = false

            for KeyValue(var, blockId) in prevDef do
                if blockId.Count > 1 then
                    phi[id][var] <- blockId.ToArray()

                    if not (defInBlock[id].ContainsKey var) then
                        defInBlock[id].Add(var, id)
                        changed <- true
                else if not (defInBlock[id].ContainsKey var) then
                    defInBlock[id].Add(var, blockId.ToArray()[0])
                    changed <- true

            if changed then
                for s in f.CFG[id].Succ do
                    todo.Add s

            idx <- idx + 1

        for id in 0 .. block.Count - 1 do
            block[id] <- this.RewriteBlock id block[id]

        for id in 0 .. block.Count - 1 do
            let phiValue _ (origin: int[]) =
                let origin = origin[0]
                let block = phi[id][origin]

                let resolve blockId =
                    let def = def[blockId]
                    if def.ContainsKey origin then Some def[origin] else None

                Array.choose resolve block

            let currPhi = Map.map phiValue block[id].Phi
            block[id] <- { block[id] with Phi = currPhi }

        { f with
            Var = var.ToArray()
            Block = block.ToArray() }

let ssaImpl (f: Func) =
    let ssa = SSA f

    ssa.Transform()

let ssa = transRegional ssaImpl
