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

    member _.Pat (p: AST.Pat) (v: Value) =
        match p with
        | AST.IdPat i ->
            let target = env.AddVar (TInt I64) (Some i.Sym)

            env.AddInstr(
                Assign
                    { Target = target
                      Value = v
                      Span = i.Span }
            )
        | _ -> failwith "Not Implmented"

    member this.Expr (e: AST.Expr) (target: Option<int>) =
        match e with
        | AST.Id i ->
            let v = env.GetBinding i.Sym

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
                | None -> env.AddVar (TInt I1) None

            let l = this.Expr bin.Left (Some target)

            let op, reverse =
                match op with
                | AST.And -> And, true
                | AST.Or -> Or, false

            let lBlock = env.CurrBlockId

            env.FinalizeBlock(Unreachable Span.dummy)

            let r = this.Expr bin.Right None

            env.AddInstr(
                Binary
                    { Left = Binding target
                      Right = r
                      Op = op
                      Target = target
                      Span = bin.Span }
            )

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
                | None -> env.AddVar ty None

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
            let cond =
                match i.Cond with
                | AST.BoolCond b -> this.Expr b None
                | AST.LetCond _ -> failwith "Not Implemented"

            if i.ElseIf.Length > 0 then
                failwith "Not Implemented"

            let condId = env.CurrBlockId

            env.FinalizeBlock(Unreachable Span.dummy)

            match i.Else with
            | Some e ->
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
                let _ = this.Block i.Then target Normal
                env.ToNext i.Then.Span

                env.ModifyTrans
                    condId
                    (Branch
                        { Value = cond
                          Zero = env.CurrBlockId
                          One = condId + 1
                          Span = i.Cond.Span })

                cond

        | AST.While w ->
            env.ToNext Span.dummy

            let startId = env.CurrBlockId

            let cond =
                match w.Cond with
                | AST.BoolCond b -> this.Expr b None
                | AST.LetCond _ -> failwith "Not Implemented"

            let condId = env.CurrBlockId
            env.FinalizeBlock(Unreachable Span.dummy)

            let _ = this.Block w.Body target (Loop startId)
            env.FinalizeBlock(Jump { Target = startId; Span = w.Body.Span })

            env.ModifyTrans
                condId
                (Branch
                    { Value = cond
                      Zero = env.CurrBlockId
                      One = condId + 1
                      Span = w.Cond.Span })

            cond

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
                let name = env.AddVar (TInt I64) l.Pat.Name
                let _ = this.Expr l.Value (Some name)

                res <- None
            | _ -> ()

        env.ExitScope()

        res

    member this.Fn(f: AST.Fn) =
        env.EnterScope Normal

        let fnTy =
            let scm = sema.Binding[f.Name]

            if scm.Generic.Length > 0 then
                failwith "Not Implemented"

            match scm.Type with
            | Semantic.TFn f -> f
            | _ -> failwith "Unreachable"

        let ret =
            if habitable fnTy.Ret > 1 then
                let ret = toIrType fnTy.Ret
                let id = env.AddVar ret None
                Some id
            else
                None

        let param =
            let param = ResizeArray()

            for (ty, p) in Array.zip fnTy.Param f.Param do
                if habitable ty > 1 then
                    let ty = toIrType ty
                    let name = p.Pat.Name
                    let id = env.AddVar ty name

                    param.Add id

            param.ToArray()

        let _ = this.Block f.Body ret Normal
        env.FinalizeBlock(Return { Value = ret; Span = f.Body.Span })

        env.ExitScope()

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
