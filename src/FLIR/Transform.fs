module FLIR.Transform

open System.Collections.Generic
open System.Linq

open Common.Target
open Common.Span
open AST
open Semantic
open FLIR.Type
open FLIR.Op
open FLIR.FLIR

type internal Env(offset: int) =
    let var = ResizeArray()

    let scope: ResizeArray<Dictionary<string, int>> = ResizeArray()

    let block = ResizeArray()
    let instr = ResizeArray()

    member _.GetBinding sym =
        let rec get i =
            let s = scope[i]

            if s.ContainsKey sym then s[sym]
            else if i >= 0 then get (i - 1)
            else failwith "Unreachable"

        get (scope.Count - 1)

    member _.Var = var
    member _.Block = block

    member _.EnterBlock = scope.Add(Dictionary())
    member _.ExitBlock = scope.RemoveAt(scope.Count - 1)

    member _.InitChild parentScope parentVar =
        scope.AddRange(parentScope)
        var.AddRange(parentVar)

    member _.AddVar ty name =
        let id = var.Count
        var.Add { Name = name; Type = ty }

        match name with
        | Some name -> scope.Last()[name] <- id
        | None -> ()

        id

    member _.ModifyVarTy id ty = var[id] <- { var[id] with Type = ty }

    member _.AddInstr i = instr.Add i

    member _.Instr = instr

    member _.FinalizeBlock trans span =
        block.Add
            { Stm = instr |> Array.ofSeq
              Trans = trans
              Span = span }

        instr.Clear()

    member _.NextId = offset + block.Count + 1

    member this.NewChild(offset) =
        let child = Env(offset)

        child.InitChild scope var

        child

let rec habitable (sema: Semantic.SemanticInfo) (ty: Semantic.Type) =
    match ty with
    | Semantic.TInt _
    | Semantic.TFloat _
    | Semantic.TChar -> System.Int32.MaxValue
    | Semantic.TBool -> 2
    | Semantic.TStruct(s, _) -> System.Int32.MaxValue
    | Semantic.TEnum(e, _) -> sema.Enum[e].Variant.Count
    | Semantic.TTuple t -> if t.Length = 0 then 1 else System.Int32.MaxValue
    | Semantic.TFn _ -> System.Int32.MaxValue
    | Semantic.TRef t -> habitable sema t
    | Semantic.TNever -> 0
    | Semantic.TVar _ -> failwith "Type Variable should be substituted in previous pass"

let transform (arch: Arch) (m: AST.Module) (sema: Semantic.SemanticInfo) =
    let layout = arch.Layout
    let habitable = habitable sema
    let toIrType = Type.FromSema sema layout

    let processPat (env: Env) (p: AST.Pat) (v: Value) =
        match p with
        | AST.IdPat i ->
            let target = env.AddVar (TInt I64) (Some i.Sym)

            env.AddInstr(
                Assign
                    { Target = target
                      Value = v
                      Span = i.Span }
            )

    let rec processExpr (env: Env) (e: AST.Expr) (target: Option<int>) =
        let makeTarget ty =
            match target with
            | Some i ->
                env.ModifyVarTy i ty
                i
            | None -> env.AddVar ty None

        match e with
        | AST.Id i ->
            let v = env.GetBinding i.Sym |> Binding

            match target with
            | Some t -> env.AddInstr(Assign { Target = t; Value = v; Span = i.Span })
            | None -> ()

            v
        | AST.LitExpr(AST.Int i, _) -> Const i
        | AST.Binary bin ->
            let l = processExpr env bin.Left None
            let r = processExpr env bin.Right None

            // TODO: trait
            let op, ty =
                match bin.Op with
                | AST.Arithmetic AST.Add -> Add, TInt I64
                | AST.Arithmetic AST.Sub -> Sub, TInt I64
                | AST.Arithmetic AST.Mul -> Mul, TInt I64
                | AST.Gt -> Gt true, TInt I1
                | AST.GtEq -> GtEq true, TInt I1
                | AST.Lt -> Lt true, TInt I1
                | AST.LtEq -> LtEq true, TInt I1

            let target = makeTarget ty

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
                match processExpr env a.Place None with
                | Binding i -> i
                | Const _ -> failwith "Unreachable"

            match a.Op with
            | Some op ->
                let value = processExpr env a.Value None

                let op =
                    match op with
                    | AST.Add -> Add
                    | AST.Sub -> Sub
                    | AST.Mul -> Mul

                env.AddInstr(
                    Binary
                        { Target = t
                          Left = Binding t
                          Op = op
                          Right = value
                          Span = a.Span }
                )

                Binding t
            | None -> processExpr env a.Value (Some t)

        | AST.If i ->
            if i.ElseIf.Length > 0 then
                failwith "Not Implemented"

            let test =
                match i.Cond with
                | AST.BoolCond b -> processExpr env b None
                | AST.LetCond _ -> failwith "Not Implemented"

            let else_, elseSpan =
                match i.Else with
                | None -> failwith "Not Implemented"
                | Some else_ ->
                    let child = env.NewChild env.NextId
                    let _ = processBlock child else_ target
                    child, else_.Span

            let then_ =
                let child = env.NewChild(else_.NextId)
                let _ = processBlock child i.Then target
                child

            let br =
                Branch
                    { Value = test
                      Other = else_.NextId
                      Zero = env.NextId }

            env.FinalizeBlock br i.Cond.Span

            let nextId = then_.NextId
            else_.FinalizeBlock (Jump nextId) elseSpan
            then_.FinalizeBlock (Jump nextId) i.Then.Span

            env.Block.AddRange else_.Block
            env.Block.AddRange then_.Block

            test

        | AST.While w ->
            let test =
                if env.Instr.Count > 0 then
                    env.FinalizeBlock (Jump env.NextId) Span.dummy

                match w.Cond with
                | AST.BoolCond b -> processExpr env b None
                | AST.LetCond _ -> failwith "Not Implemented"

            let body =
                let body = env.NewChild env.NextId
                let _ = processBlock body w.Body None

                body

            let br =
                Branch
                    { Value = test
                      Zero = body.NextId
                      Other = env.NextId }

            body.FinalizeBlock (Jump(env.NextId - 1)) w.Body.Span

            env.FinalizeBlock br Span.dummy

            env.Block.AddRange body.Block

            test

        | _ -> failwith "Not Implemented"

    and processBlock (env: Env) (b: AST.Block) (target: Option<int>) =
        env.EnterBlock
        let mutable res = None

        for (idx, stmt) in Array.indexed b.Stmt do
            match stmt with
            | AST.ExprStmt e ->
                let target = if idx = b.Stmt.Length - 1 then target else None

                let value = processExpr env e target
                res <- Some value
            | AST.DeclStmt(AST.Let l) ->
                let name = env.AddVar (TInt I64) l.Pat.Name
                let value = processExpr env l.Value (Some name)

                if l.Mut then
                    env.AddInstr(
                        Assign
                            { Target = name
                              Value = value
                              Span = l.Span }
                    )

                res <- None
            | _ -> ()

        env.ExitBlock

        res

    let processFn (f: AST.Fn) =
        let env = Env(0)
        // for param
        env.EnterBlock

        let fnTy =
            match sema.Var[f.Name] with
            | Semantic.TFn f -> f
            | _ -> failwith "Unreachable"

        if fnTy.TVar.Length > 0 then
            failwith "Not Implemented"

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
                if habitable ty > 0 then
                    let ty = toIrType ty
                    let name = p.Pat.Name
                    let id = env.AddVar ty name

                    param.Add id

            Array.ofSeq param

        let _ = processBlock env f.Body ret
        env.FinalizeBlock (Ret ret) f.Span

        { Block = Array.ofSeq env.Block
          Var = Array.ofSeq env.Var
          Param = param
          Ret = ret
          Span = f.Span }

    let func = ResizeArray()

    for item in m.Item do
        match item.Decl with
        | AST.Use _ -> ()
        | AST.Let l -> ()
        | AST.Const c -> ()
        | AST.FnDecl f -> func.Add(processFn f)
        | AST.StructDecl _
        | AST.EnumDecl _
        | AST.TypeDecl _ -> ()
        | AST.Impl impl -> ()
        | AST.Trait t -> ()

    { Func = Array.ofSeq func
      Static = [||] }
