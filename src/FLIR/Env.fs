module FLIR.Env

open System.Collections.Generic
open System.Linq

open Common.Span
open AST
open FLIR
open Type

type ScopeInfo =
    | Loop
    | Normal

type Scope =
    { CanBreak: bool
      CanContinue: bool
      Continue: ResizeArray<int * Span>
      Break: ResizeArray<int * Span> }

type Env() =
    let scope = Stack<Scope>()
    let var = ResizeArray<Var>()

    let varMap = Dictionary<AST.Id, int>(HashIdentity.Reference)

    let block = ResizeArray<Block>()
    let phi = ResizeArray<unit>()
    let instr = ResizeArray<Instr>()

    member _.AddInstr i = instr.Add i

    member _.AddVar ty name =
        let id = var.Count
        var.Add { Name = name; Type = ty }
        id

    member _.DeclareVar ty (def: AST.Id) =
        let id = var.Count
        var.Add { Name = def.Sym; Type = ty }
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

    member _.FinalizeBlock trans =
        let newBlock =
            { Phi = phi.ToArray()
              Instr = instr.ToArray()
              Trans = trans }

        phi.Clear()
        instr.Clear()

        block.Add newBlock

    member this.Reverse(value: Value) =
        let target =
            match value with
            | Const _ -> this.AddVar (TInt I1) ""
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
            | Binary({ Op = Eq | NotEq | Lt _ | LtEq _ | GtEq _ | Gt _ as binOp } as bin) when last.Target = target ->
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

        this.FinalizeBlock(Unreachable Span.dummy)

    member this.Break span =
        let picker s =
            if s.CanBreak then Some s.Break else None

        let register = this.Pick picker

        register.Add(this.CurrBlockId, span)

        this.FinalizeBlock(Unreachable Span.dummy)

    member _.ExitScope() = scope.Pop()

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
