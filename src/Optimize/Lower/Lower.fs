module Optimize.Lower.Lower

open Common.Target
open Common.Span
open Syntax
open Semantic
open Optimize.FLIR
open Optimize.Lower.Env

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

type Habit =
    | Finite of int
    | Infinite

    static member (+)(a, b) =
        match a, b with
        | Finite a, Finite b -> Finite(a + b)
        | Infinite, _
        | _, Infinite -> Infinite

    static member (*)(a, b) =
        match a, b with
        | Finite a, Finite b -> Finite(a * b)
        | Infinite, _
        | _, Infinite -> Infinite

type internal Lower(arch: Arch, m: AST.Module, sema: Semantic.SemanticInfo) =
    let layout = arch.Layout
    let habitable = Type.Habitable sema

    let env = Env()

    member this.Pat(p: AST.Pat) =
        match p with
        | AST.IdPat i ->
            let ty = this.Type sema.DeclTy[i].Type
            env.DeclareVar ty i
        | _ -> failwith "Not Implmented"

    member this.Type(ty: Semantic.Type) =
        let size =
            match layout.PtrSize with
            | 4 -> I32
            | 8 -> I64
            | _ -> failwith "Not Implemented"
            |> TInt

        match ty with
        | Semantic.TBool -> TInt I1
        | Semantic.TInt(_, Semantic.I8) -> TInt I8
        | Semantic.TInt(_, Semantic.I32) -> TInt I32
        | Semantic.TInt(_, Semantic.I64) -> TInt I64
        | Semantic.TInt(_, Semantic.ISize) -> size
        | Semantic.TFloat Semantic.F32 -> TFloat F32
        | Semantic.TFloat Semantic.F64 -> TFloat F64
        | Semantic.TChar -> TInt I32
        | Semantic.TRef _
        | Semantic.TFn _
        | Semantic.TTrait _ -> TRef
        | Semantic.TSlice _
        | Semantic.TString -> TMany [| TRef; size |]
        | Semantic.TTuple t -> t |> Array.map this.Type |> TMany
        | Semantic.TArray(t, n) -> TSame(this.Type t, n)
        | Semantic.TStruct a ->
            let strukt = sema.Struct[a.Name]

            let trans (ty: Semantic.Type) =
                ty.Instantiate strukt.Generic a.Generic |> this.Type

            strukt.Field.Values
            |> Seq.map trans
            |> Array.ofSeq
            |> TMany
            |> _.OptLayout(layout)
        | Semantic.TEnum e ->
            let enum = sema.Enum[e.Name]
            failwith "Not Implemented"
        | Semantic.TNever
        | Semantic.TVar _
        | Semantic.TGen _ -> failwith "unreachable"

    member this.Cond(c: AST.Cond) =
        match c with
        | AST.BoolCond b -> this.BoolCond None b
        | AST.LetCond _ -> failwith "Not Implemented"

    member this.BoolCond (target: Option<int>) (e: AST.Expr) =
        let rec expr t f e =
            match e with
            | AST.Binary({ Op = AST.Logic AST.And } as a) ->
                let lt = ResizeArray()
                expr lt f a.Left

                for t, tar in lt do
                    env.ModifyBr t tar env.CurrBlockId

                expr t f a.Right
            | AST.Binary({ Op = AST.Logic AST.Or } as a) ->
                let lf = ResizeArray()
                expr t lf a.Left

                for t, tar in lf do
                    env.ModifyBr t tar env.CurrBlockId

                expr t f a.Right
            | AST.Unary({ Op = AST.Not } as u) -> expr f t u.Value
            | e ->
                let value = this.Expr target e

                let id =
                    env.FinalizeBlock(
                        Branch
                            { Value = value
                              One = 0
                              Zero = 0
                              Span = e.Span }
                    )

                t.Add(id, One)
                f.Add(id, Zero)

        let t = ResizeArray()
        let f = ResizeArray()

        expr t f e

        t, f

    member this.Expr (target: Option<int>) (e: AST.Expr) =
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
        | AST.Unary u ->
            let value = this.Expr target u.Value

            match u.Op with
            | AST.Neg ->
                let target = env.OfTarget target (TInt I64)

                env.AddInstr(
                    Unary
                        { Target = target
                          Op = Neg
                          Value = value
                          Span = u.Span }
                )

                Binding target
            | AST.Not ->
                let target = env.OfTarget target (TInt I1)

                env.AddInstr(
                    Unary
                        { Target = target
                          Op = Neg
                          Value = value
                          Span = u.Span }
                )

                Binding target
            | AST.Ref
            | AST.Deref -> failwith "Not Implemented"
        | AST.Binary({ Op = AST.Logic op } as bin) ->
            let target = env.OfTarget target (TInt I1)
            let t, f = this.BoolCond (Some target) e

            for t, tar in t do
                env.ModifyBr t tar env.CurrBlockId

            for f, tar in f do
                env.ModifyBr f tar env.CurrBlockId

            env.ModifyTrans
                (env.CurrBlockId - 1)
                (Jump
                    { Target = env.CurrBlockId
                      Span = bin.Span })

            Binding target
        | AST.Binary bin ->
            let l = this.Expr None bin.Left
            let r = this.Expr None bin.Right

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

            let target = env.OfTarget target ty

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
                match this.Expr None a.Place with
                | Binding i -> i
                | Const _ -> failwith "Unreachable"

            match a.Op with
            | Some op ->
                let value = this.Expr None a.Value

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
            | None -> this.Expr (Some t) a.Value

        | AST.If i ->
            let t, f = this.Cond i.Cond

            if i.ElseIf.Length > 0 then
                failwith "Not Implemented"

            match i.Else with
            | Some e ->
                let elseStart = env.CurrBlockId
                let _ = this.Block target Normal e
                let elseId = env.FinalizeBlock(Unreachable Span.dummy)

                let thenStart = env.CurrBlockId
                let _ = this.Block target Normal i.Then
                let next = env.CurrBlockId + 1

                let _ = env.FinalizeBlock(Jump { Target = next; Span = i.Then.Span })
                env.ModifyTrans elseId (Jump { Target = next; Span = e.Span })

                for t, tar in t do
                    env.ModifyBr t tar thenStart

                for f, tar in f do
                    env.ModifyBr f tar elseStart

                Const 0UL
            | None ->
                let thenStart = env.CurrBlockId
                let _ = this.Block target Normal i.Then
                env.ToNext i.Then.Span

                for t, tar in t do
                    env.ModifyBr t tar thenStart

                for f, tar in f do
                    env.ModifyBr f tar env.CurrBlockId

                Const 0UL

        | AST.While w ->
            let t, f = this.Cond w.Cond

            let bodyStart = env.CurrBlockId

            for t, tar in t do
                env.ModifyBr t tar bodyStart

            let _, scope = this.Block target Loop w.Body

            let endCondStart = env.CurrBlockId
            let et, ef = this.Cond w.Cond

            for t, tar in et do
                env.ModifyBr t tar bodyStart

            for f, tar in f do
                env.ModifyBr f tar env.CurrBlockId

            for f, tar in ef do
                env.ModifyBr f tar env.CurrBlockId

            for id, span in scope.Break do
                env.ModifyTrans
                    id
                    (Jump
                        { Target = env.CurrBlockId
                          Span = span })

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

    member this.Block (target: Option<int>) (info: ScopeInfo) (b: AST.Block) =
        env.EnterScope info

        let mutable res = None

        for (idx, stmt) in Array.indexed b.Stmt do
            match stmt with
            | AST.ExprStmt e ->
                let target = if idx = b.Stmt.Length - 1 then target else None

                let value = this.Expr target e
                res <- Some value
            | AST.DeclStmt(AST.Let l) ->
                let name = this.Pat l.Pat
                let _ = this.Expr (Some name) l.Value

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
                let ret = this.Type fnTy.Ret
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

        let _ = this.Block ret Normal f.Body
        let _ = env.FinalizeBlock(Return { Value = ret; Span = f.Body.Span })

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
