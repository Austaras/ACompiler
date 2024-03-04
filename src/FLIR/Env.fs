module FLIR.Env

open System.Collections.Generic
open System.Linq

open Common.Span
open FLIR

type ScopeInfo =
    | Loop of int
    | Normal

type Scope =
    { LoopStart: Option<int>
      Break: ResizeArray<int * Span>
      Binding: Dictionary<string, int> }

type Env() =
    let scope = Stack<Scope>()
    let var = ResizeArray<Var>()

    let block = ResizeArray<Block>()
    let phi = ResizeArray<unit>()
    let instr = ResizeArray<Instr>()

    member _.AddInstr i = instr.Add i

    member _.AddVar ty name =
        let id = var.Count
        var.Add { Name = name; Type = ty }

        match name with
        | Some name -> scope.Peek().Binding[ name ] <- id
        | None -> ()

        id

    member _.Pick picker =
        let rec loop (i: int) =
            let curr = scope.ElementAt i

            match picker curr with
            | Some r -> r
            | None when i + 1 = scope.Count -> failwithf "Unreachable"
            | None -> loop (i + 1)

        loop 0

    member this.GetBinding name =
        let picker s =
            if s.Binding.ContainsKey name then
                Some s.Binding[name]
            else
                None

        this.Pick picker |> Binding

    member _.CurrBlockId = block.Count

    member _.FinalizeBlock trans =
        let newBlock =
            { Phi = phi.ToArray()
              Instr = instr.ToArray()
              Trans = trans }

        phi.Clear()
        instr.Clear()

        block.Add newBlock

    member this.ToNext span =
        if instr.Count > 0 then
            let newBlock =
                { Phi = phi.ToArray()
                  Instr = instr.ToArray()
                  Trans =
                    Jump
                        { Target = this.CurrBlockId + 1
                          Span = span } }

            phi.Clear()
            instr.Clear()

            block.Add newBlock

    member _.ModifyTrans id trans =
        let b = block[id]

        block[id] <- { b with Trans = trans }

    member this.Continue span =
        let picker s = s.LoopStart

        let startId = this.Pick picker

        this.FinalizeBlock(Jump { Target = startId; Span = span })

    member this.Break span =
        let picker s =
            match s.LoopStart with
            | Some _ -> Some s.Break
            | None -> None

        let register = this.Pick picker
        register.Add(this.CurrBlockId, span)

        this.FinalizeBlock(Unreachable Span.dummy)

    member _.EnterScope(info: ScopeInfo) =
        scope.Push
            { LoopStart =
                match info with
                | Loop i -> Some i
                | Normal -> None
              Break = ResizeArray()
              Binding = Dictionary() }

    member this.ExitScope() =
        let last = scope.Pop()

        for id, span in last.Break do
            this.ModifyTrans
                id
                (Jump
                    { Target = this.CurrBlockId + 1
                      Span = span })

        ()

    member this.FinalizeFn param ret span =
        let f =
            { Block = block.ToArray()
              Var = var.ToArray()
              Param = param
              Ret = ret
              Span = span }

        block.Clear()
        var.Clear()

        f
