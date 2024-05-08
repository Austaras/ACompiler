module FLIR.Lower

open Common.Target
open Common.Span
open AST
open Semantic
open Type
open FLIR
open Env

let fromArith arith =
    match arith with
    | AST.Add -> Add
    | AST.Sub -> Sub
    | AST.Mul -> Mul
    | AST.Div -> Div
    | AST.Rem -> Rem
    | AST.BitAnd -> And
    | AST.BitOr -> Or
    | AST.BitXor -> Xor
    | AST.Shl -> Shl
    | AST.Shr -> failwith "Not Implemented"

type internal Lower(arch: Arch, m: AST.Module, sema: Semantic.SemanticInfo) =
    let layout = arch.Layout
    let habitable = Type.Habitable sema
    let toIrType = Type.FromSema sema layout

    let env = Env()

    member _.Pat(p: AST.Pat) =
        match p with
        | AST.IdPat i ->
            let ty = toIrType sema.DeclTy[i].Type
            env.DeclareVar ty i
        | _ -> failwith "Not Implmented"

    member this.Cond(c: AST.Cond) =
        match c with
        | AST.BoolCond b -> this.Expr b None
        | AST.LetCond _ -> failwith "Not Implemented"

    member this.Expr (e: AST.Expr) (target: Option<int>) =
        match e with
        | AST.Id i ->
            let v = env.GetVar sema.Binding[i] |> Binding

            match target with
            | Some t -> env.AddInstr(Assign { Target = t; Value = v; Span = i.Span })
            | None -> ()

            v
        | AST.LitExpr({ Value = AST.Int i; Span = span }) ->
            let v = Const i

            match target with
            | Some t -> env.AddInstr(Assign { Target = t; Value = v; Span = span })
            | None -> ()

            v
        | AST.Binary({ Op = AST.Logic op } as bin) ->
            let target =
                match target with
                | Some t -> t
                | None -> env.AddVar(TInt I1)

            let l = this.Expr bin.Left (Some target)

            let reverse =
                match op with
                | AST.And -> true
                | AST.Or -> false

            let lBlock = env.CurrBlockId

            env.FinalizeBlock(Unreachable Span.dummy)

            let _ = this.Expr bin.Right (Some target)

            env.ToNext bin.Right.Span

            env.ModifyTrans
                lBlock
                (Branch
                    { Value = l
                      Zero = if reverse then env.CurrBlockId else lBlock + 1
                      One = if reverse then lBlock + 1 else env.CurrBlockId
                      Span = bin.Span })

            Binding target
        | AST.Binary bin ->
            let l = this.Expr bin.Left None
            let r = this.Expr bin.Right None

            // TODO: trait
            let op, ty =
                match bin.Op with
                | AST.Arith op -> fromArith op, TInt I64
                | AST.Cmp AST.Gt -> Gt true, TInt I1
                | AST.Cmp AST.GtEq -> GtEq true, TInt I1
                | AST.Cmp AST.Lt -> Lt true, TInt I1
                | AST.Cmp AST.LtEq -> LtEq true, TInt I1
                | AST.Cmp AST.EqEq -> Eq, TInt I1
                | AST.Cmp AST.NotEq -> NotEq, TInt I1
                | AST.Logic _ -> failwith "Unreachable"
                | AST.Pipe -> failwith "Not Implemented"

            let target =
                match target with
                | Some t -> t
                | None -> env.AddVar ty

            env.AddInstr(
                Binary
                    { Left = l
                      Right = r
                      Op = op
                      Target = target
                      Span = bin.Span }
            )

            Binding target
        | AST.Assign a ->
            let t =
                match this.Expr a.Place None with
                | Binding i -> i
                | Const _ -> failwith "Unreachable"

            match a.Op with
            | Some op ->
                let value = this.Expr a.Value None

                let op = fromArith op

                env.AddInstr(
                    Binary
                        { Target = t
                          Left = Binding t
                          Op = op
                          Right = value
                          Span = a.Span }
                )

                Binding t
            | None -> this.Expr a.Value (Some t)

        | AST.If i ->
            let cond = this.Cond i.Cond

            if i.ElseIf.Length > 0 then
                failwith "Not Implemented"

            let condId = env.CurrBlockId

            match i.Else with
            | Some e ->
                env.FinalizeBlock(Unreachable Span.dummy)
                let _ = this.Block e target Normal
                let elseId = env.CurrBlockId
                env.FinalizeBlock(Unreachable Span.dummy)

                let _ = this.Block i.Then target Normal
                let next = env.CurrBlockId + 1

                env.FinalizeBlock(Jump { Target = next; Span = i.Then.Span })
                env.ModifyTrans elseId (Jump { Target = next; Span = e.Span })

                env.ModifyTrans
                    condId
                    (Branch
                        { Value = cond
                          Zero = condId + 1
                          One = elseId + 1
                          Span = i.Cond.Span })

                cond
            | None ->
                let cond = env.Reverse cond
                env.FinalizeBlock(Unreachable Span.dummy)
                let _ = this.Block i.Then target Normal
                env.ToNext i.Then.Span

                env.ModifyTrans
                    condId
                    (Branch
                        { Value = cond
                          Zero = condId + 1
                          One = env.CurrBlockId
                          Span = i.Cond.Span })

                cond

        | AST.While w ->
            env.ToNext Span.dummy

            let cond = this.Cond w.Cond
            let cond = env.Reverse cond
            let condId = env.CurrBlockId
            env.FinalizeBlock(Unreachable Span.dummy)

            let bodyStart = env.CurrBlockId
            let _, scope = this.Block w.Body target Loop

            if scope.Continue.Count > 0 then
                env.ToNext Span.dummy

            let endCondStart = env.CurrBlockId
            let endCond = this.Cond w.Cond
            let nextId = env.CurrBlockId + 1

            env.FinalizeBlock(
                Branch
                    { Value = endCond
                      Zero = nextId
                      One = bodyStart
                      Span = w.Cond.Span }
            )

            env.ModifyTrans
                condId
                (Branch
                    { Value = cond
                      Zero = bodyStart
                      One = nextId
                      Span = w.Cond.Span })

            for id, span in scope.Break do
                env.ModifyTrans id (Jump { Target = nextId; Span = span })

            for id, span in scope.Continue do
                env.ModifyTrans id (Jump { Target = endCondStart; Span = span })

            Const 0UL

        | AST.Continue c ->
            env.Continue c
            Const 0UL

        | AST.Break b ->
            env.Break b
            Const 0UL

        | _ -> failwith "Not Implemented"

    member this.Block (b: AST.Block) (target: Option<int>) (info: ScopeInfo) =
        env.EnterScope info

        let mutable res = None

        for (idx, stmt) in Array.indexed b.Stmt do
            match stmt with
            | AST.ExprStmt e ->
                let target = if idx = b.Stmt.Length - 1 then target else None

                let value = this.Expr e target
                res <- Some value
            | AST.DeclStmt(AST.Let l) ->
                let name = this.Pat l.Pat
                let _ = this.Expr l.Value (Some name)

                res <- None
            | _ -> ()

        res, env.ExitScope()

    member this.Fn(f: AST.Fn) =
        env.EnterScope Normal

        let fnTy =
            let scm = sema.DeclTy[f.Name]

            if scm.Generic.Length > 0 then
                failwith "Not Implemented"

            match scm.Type with
            | Semantic.TFn f -> f
            | _ -> failwith "Unreachable"

        let ret =
            if habitable fnTy.Ret > 1 then
                let ret = toIrType fnTy.Ret
                let id = env.AddVar ret
                Some id
            else
                None

        let param =
            let param = ResizeArray()

            for (ty, p) in Array.zip fnTy.Param f.Param do
                if habitable ty > 1 then
                    let id = this.Pat p.Pat
                    param.Add id

            param.ToArray()

        let _ = this.Block f.Body ret Normal
        env.FinalizeBlock(Return { Value = ret; Span = f.Body.Span })

        let _ = env.ExitScope()

        env.FinalizeFn param ret f.Span

    member this.Module() =
        let func = ResizeArray()

        for item in m.Item do
            match item.Decl with
            | AST.Use _ -> ()
            | AST.Let l -> ()
            | AST.Const c -> ()
            | AST.FnDecl f -> func.Add(this.Fn f)
            | AST.StructDecl _
            | AST.EnumDecl _
            | AST.TypeDecl _ -> ()
            | AST.Impl impl -> ()
            | AST.Trait t -> ()

        { Func = func.ToArray(); Static = [||] }

let lower (arch: Arch) (m: AST.Module) (sema: Semantic.SemanticInfo) =
    let t = Lower(arch, m, sema)
    t.Module()
