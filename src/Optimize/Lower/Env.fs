module Optimize.Lower.Env

open System.Collections.Generic
open System.Linq

open Common.Span
open Syntax
open Optimize.FLIR
open Optimize.Util

type ScopeInfo =
    | Loop
    | Normal

type Scope =
    { CanBreak: bool
      CanContinue: bool
      Continue: ResizeArray<int * Span>
      Break: ResizeArray<int * Span> }

type BranchTarget =
    | One
    | Zero

type CFGData =
    { Pred: SortedSet<int>
      Succ: SortedSet<int> }

type Env() =
    let scope = Stack<Scope>()
    let var = ResizeArray<Var>()

    let varMap = Dictionary<AST.Id, int>(HashIdentity.Reference)

    let block = ResizeArray<Block>()

    let cfg =
        ResizeArray<CFGData>(
            [| { Pred = SortedSet()
                 Succ = SortedSet() } |]
        )

    let instr = ResizeArray<Instr>()

    member _.AddInstr i = instr.Add i

    member _.AddVar ty =
        let id = var.Count

        var.Add
            { Name = ""
              Type = ty
              Def = 0
              Use = [||] }

        id

    member this.OfTarget target ty =
        match target with
        | Some t -> t
        | None -> this.AddVar ty

    member _.DeclareVar ty (def: AST.Id) =
        let id = var.Count

        var.Add
            { Name = def.Sym
              Type = ty
              Def = 0
              Use = [||] }

        varMap.Add(def, id)
        id

    member _.GetVar def = varMap[def]

    member _.Pick picker =
        let rec loop (i: int) =
            let curr = scope.ElementAt i

            match picker curr with
            | Some r -> r
            | None when i + 1 = scope.Count -> failwithf "Unreachable"
            | None -> loop (i + 1)

        loop 0

    member _.CurrBlockId = block.Count

    member _.AddEdge from to_ =
        if to_ <> 0 then
            let fromNode =
                while from >= cfg.Count do
                    cfg.Add
                        { Succ = SortedSet()
                          Pred = SortedSet() }

                cfg[from]

            fromNode.Succ.Add to_ |> ignore

            let toNode =
                while to_ >= cfg.Count do
                    cfg.Add
                        { Succ = SortedSet()
                          Pred = SortedSet() }

                cfg[to_]

            toNode.Pred.Add from |> ignore

    member this.FinalizeBlock trans =
        let newBlock =
            { Phi = Map.empty
              Instr = instr.ToArray()
              Trans = trans }

        instr.Clear()

        block.Add newBlock

        let id = block.Count - 1

        match trans with
        | Jump j -> this.AddEdge id j.Target
        | Branch b ->
            this.AddEdge id b.One
            this.AddEdge id b.Zero
        | Switch s ->
            for t, _ in s.Dest do
                this.AddEdge id t

            this.AddEdge id s.Default
        | Return _
        | Unreachable _ -> ()

        id

    member this.Reverse(value: Value) =
        let target =
            match value with
            | Const _ -> this.AddVar(TInt I1)
            | Binding b -> b

        let addReverse () =
            instr.Add(
                Unary
                    { Target = target
                      Op = Not
                      Value = Binding target
                      Span = Span.dummy }
            )

        if instr.Count > 0 then
            let last = instr.Last()

            match last with
            | Binary({ Op = Eq | NotEq | Lt _ | LtEq _ | GtEq _ | Gt _ as binOp } as bin) when bin.Target = target ->
                let newOp =
                    match binOp with
                    | Eq -> NotEq
                    | NotEq -> Eq
                    | Lt s -> GtEq s
                    | LtEq s -> Gt s
                    | Gt s -> LtEq s
                    | GtEq s -> Lt s
                    | _ -> failwith "Unreachable"

                let bin = Binary { bin with Op = newOp }

                instr[instr.Count - 1] <- bin
            | _ -> addReverse ()
        else
            addReverse ()

        Binding target

    member this.ToNext span =
        if instr.Count > 0 then
            let trans =
                Jump
                    { Target = this.CurrBlockId + 1
                      Span = span }

            this.FinalizeBlock trans |> ignore

    member this.ModifyJmp id jmp =
        let b = block[id]

        block[id] <- { b with Trans = Jump jmp }

        this.AddEdge id jmp.Target

    member this.ModifyBr id target toId =
        let b = block[id]

        match b.Trans with
        | Branch br ->
            let br =
                match target with
                | One -> { br with One = toId }
                | Zero -> { br with Zero = toId }

            block[id] <- { b with Trans = Branch br }

            this.AddEdge id toId
        | _ -> failwith "Unreachable"

    member _.EnterScope(info: ScopeInfo) =
        scope.Push
            { Continue = ResizeArray()
              CanContinue = info = Loop
              Break = ResizeArray()
              CanBreak = info = Loop }

    member this.Continue span =
        let picker s =
            if s.CanContinue then Some s.Continue else None

        let register = this.Pick picker

        register.Add(this.CurrBlockId, span)

        this.FinalizeBlock(Unreachable Span.dummy) |> ignore

    member this.Break span =
        let picker s =
            if s.CanBreak then Some s.Break else None

        let register = this.Pick picker

        register.Add(this.CurrBlockId, span)

        this.FinalizeBlock(Unreachable Span.dummy) |> ignore

    member _.ExitScope() = scope.Pop()

    member _.FinalizeFn param ret span =
        let toCFG cfg : GraphNode =
            { Pred = cfg.Pred.ToArray()
              Succ = cfg.Succ.ToArray() }

        let ret =
            match ret with
            | Some ret -> Some var[ret].Type
            | None -> None

        let f =
            { Block = block.ToArray()
              CFG = cfg |> Seq.map toCFG |> Array.ofSeq
              Var = var.ToArray()
              Param = param
              Ret = ret
              Span = span }

        let shouldRemove = Dictionary()

        for idx, data in Seq.indexed cfg do
            if
                data.Pred.Count = 1
                && data.Succ.Count = 1
                && Array.length f.Block[idx].Instr = 0
            then
                shouldRemove.Add(idx, data.Succ |> Seq.head) |> ignore

        let varMapping =
            seq { 0 .. f.Var.Length - 1 }
            |> Seq.map (fun idx -> Some(Binding idx))
            |> Array.ofSeq

        let rec resolve idx =
            if shouldRemove.ContainsKey idx then
                resolve (shouldRemove[idx])
            else
                idx

        let blockMapping =
            seq { 0 .. f.Block.Length - 1 }
            |> Seq.map (fun idx -> resolve idx)
            |> Array.ofSeq

        let f = removeVarAndBlock f varMapping blockMapping

        block.Clear()
        var.Clear()

        f
