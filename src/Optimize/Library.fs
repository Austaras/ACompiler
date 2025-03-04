﻿module Optimize.FLIR

open System

open Common.Span
open Common.Target
open Semantic

type Integer =
    | I1
    | I8
    | I32
    | I64

type Float =
    | F32
    | F64

type Function = { Param: Type[]; Ret: Type }

and Type =
    | TInt of Integer
    | TFloat of Float
    | TFn of Function
    | TRef
    | TSame of Type * uint64
    | TMany of Type[]

    static member Habitable (sema: Semantic.SemanticInfo) (ty: Semantic.Type) =
        let field (ty: seq<Semantic.Type>) =
            ty |> Seq.map (Type.Habitable sema) |> Seq.fold (*) 1

        match ty with
        | Semantic.TInt _
        | Semantic.TFloat _
        | Semantic.TChar
        | Semantic.TString -> 10000
        | Semantic.TBool -> 2
        | Semantic.TStruct a ->
            let stru = sema.Struct[a.Name]
            let inst (t: Semantic.Type) = t.Instantiate stru.Generic a.Generic

            stru.Field.Values |> Seq.map inst |> field

        | Semantic.TEnum a ->
            let enum = sema.Enum[a.Name]

            let variant (ty: Semantic.Type[]) =
                let mapTy (ty: Semantic.Type) = ty.Instantiate enum.Generic a.Generic

                ty |> Array.map mapTy |> field

            enum.Variant.Values |> Seq.map variant |> Seq.sum

        | Semantic.TTuple t -> field t
        | Semantic.TTrait _
        | Semantic.TFn _ -> 10000
        | Semantic.TRef t
        | Semantic.TArray(t, _)
        | Semantic.TSlice t -> Type.Habitable sema t
        | Semantic.TNever -> 0
        | Semantic.TVar _
        | Semantic.TGen _ -> failwith "Type Variable should be substituted in previous pass"

    member internal this.SizeAndAlign(layout: Layout) =
        match this with
        | TInt I1 -> 1, layout.I1Align
        | TInt I8 -> 1, layout.I8Align
        | TInt I32 -> 4, layout.I32Align
        | TInt I64 -> 8, layout.I64Align
        | TFloat F32 -> 4, layout.F32Align
        | TFloat F64 -> 8, layout.F64Align
        | TFn _
        | TRef -> layout.PtrSize, layout.PtrAlign
        | TSame(s, n) ->
            let size, align = s.SizeAndAlign layout

            size * int n, align
        | TMany ty ->
            let sum (size, align) (ty: Type) =
                let s, a = ty.SizeAndAlign layout

                let padding = if size % a = 0 then 0 else s - size % s

                let align = if a > align then a else align

                size + padding + s, align

            Array.fold sum (0, 0) ty

    member this.Size(layout: Layout) =
        let size, align = this.SizeAndAlign layout

        if size % align = 0 then
            size
        else
            (size / align + 1) * align

    member this.Align(layout: Layout) = snd (this.SizeAndAlign layout)

    member this.OptLayout(layout: Layout) =
        match this with
        | TMany t ->
            let t = t |> Array.sortByDescending _.Size(layout)

            TMany t
        | t -> t

    member this.ToString =
        match this with
        | TInt I1 -> "i1"
        | TInt I8 -> "i8"
        | TInt I32 -> "i32"
        | TInt I64 -> "i64"
        | TFloat F32 -> "f32"
        | TFloat F64 -> "f64"
        | TFn(_) -> "fn"
        | TRef -> "ptr"
        | TSame(t, n) -> $"[{t.ToString}; {n}]"
        | TMany t ->
            let t = t |> Array.map _.ToString |> String.concat ", "

            $"({t})"

type MonoMode =
    | MSize of int
    | MType of Type

type Location =
    | Static
    | Unambiguous
    | Automatic
    | Irregular

type BinOp =
    | Add
    | Sub
    | Mul
    | Div
    | Rem
    | Xor
    | And
    | Or
    | Shl
    /// signed or not
    | Shr of bool
    | Eq
    | NotEq
    /// signed or not
    | Lt of bool
    /// signed or not
    | LtEq of bool
    /// signed or not
    | GtEq of bool
    /// signed or not
    | Gt of bool

    member this.ToString =
        match this with
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | Div -> "/"
        | Rem -> "%"
        | Xor -> "^"
        | And -> "&"
        | Or -> "|"
        | Shl -> "<<"
        | Shr true -> ">>"
        | Shr false -> ">>>"
        | Eq -> "=="
        | NotEq -> "!="
        | Lt true -> "<"
        | Lt false -> "u<"
        | LtEq true -> "<="
        | LtEq false -> "u<="
        | GtEq true -> ">="
        | GtEq false -> "u>="
        | Gt true -> ">"
        | Gt false -> "u>"

type UnaryOp =
    | Neg
    | Not
    | Ext of bool

    member this.ToString =
        match this with
        | Neg -> "-"
        | Not -> "!"
        | Ext true -> "sext"
        | Ext false -> "zext"

type UseData =
    | InTx
    | InPhi of int
    | ForTarget of int

type Use = { BlockId: int; Data: UseData }

type Var =
    { Name: string
      Type: Type
      Def: int
      Use: Use[] }

    member this.WithUse data =
        { this with
            Use = Array.append this.Use [| data |] }

    member this.WithoutUse data =
        { this with
            Use = Array.filter ((<>) data) this.Use }

type Value =
    | Const of uint64
    | Binding of int

type Assign =
    { Target: int
      Value: Value
      Span: Span }

type Binary =
    { Left: Value
      Right: Value
      Op: BinOp
      Target: int
      Span: Span }

type Unary =
    { Target: int
      Op: UnaryOp
      Value: Value
      Span: Span }

type Callee =
    | Fixed
    | CBinding of int

type Call =
    { Target: int
      Callee: Callee
      Arg: Value[]
      Span: Span }

type Load =
    { Target: int
      Base: Value
      Offset: Value }

/// Instrument
type Instr =
    | Assign of Assign
    | Binary of Binary
    | Unary of Unary
    | Call of Call
    | Load of Load
    | Store
    | Alloc

    member this.Target =
        match this with
        | Binary b -> b.Target
        | Assign a -> a.Target
        | Unary n -> n.Target
        | Call c -> c.Target
        | Load l -> l.Target
        | Store -> failwith "Not Implemented"
        | Alloc -> failwith "Not Implemented"

    member this.Value =
        seq {
            match this with
            | Binary b ->
                yield b.Left
                yield b.Right
            | Assign a -> yield a.Value
            | Unary u -> yield u.Value
            | Call c -> yield! c.Arg
            | Load l ->
                yield l.Base
                yield l.Offset
            | Store -> failwith "Not Implemented"
            | Alloc -> failwith "Not Implemented"
        }

type Jump = { Target: int; Span: Span }

type Branch =
    { Value: Value
      Zero: int
      One: int
      Span: Span }

type Indirect =
    { Value: Value
      Dest: int[]
      Span: Span }

type Ret = { Value: Option<Value>; Span: Span }

type Transfer =
    | Jump of Jump
    | Branch of Branch
    | Indirect of Indirect
    | Return of Ret
    | Unreachable of Span

    member this.Target() =
        seq {
            match this with
            | Jump j -> yield j.Target
            | Branch b ->
                yield b.One
                yield b.Zero
            | Indirect s ->
                for dest in s.Dest do
                    yield dest
            | Return _
            | Unreachable _ -> ()
        }

/// Basic block
type Block =
    { Phi: Map<int, Value[]>
      Instr: Instr[]
      Trans: Transfer }

    member this.Analyze def use_ =
        for instr in this.Instr do
            match instr with
            | Assign a ->
                use_ a.Value
                def a.Target
            | Unary u ->
                use_ u.Value
                def u.Target
            | Binary b ->
                use_ b.Left
                use_ b.Right
                def b.Target
            | Call c ->
                for arg in c.Arg do
                    use_ arg

                def c.Target
            | Load l ->
                use_ l.Base
                use_ l.Offset

                def l.Target
            | Store -> failwith "Not Implemented"
            | Alloc -> failwith "Not Implemented"

        match this.Trans with
        | Branch b -> use_ b.Value
        | Return r ->
            match r.Value with
            | None -> ()
            | Some v -> use_ v
        | Indirect s -> use_ s.Value
        | Jump _
        | Unreachable _ -> ()

    member this.Rewrite def use_ =
        let rewriteInstr instr =
            match instr with
            | Assign a ->
                Assign
                    { a with
                        Value = use_ a.Value
                        Target = def a.Target }
            | Unary u ->
                Unary
                    { u with
                        Value = use_ u.Value
                        Target = def u.Target }
            | Binary b ->
                Binary
                    { b with
                        Left = use_ b.Left
                        Right = use_ b.Right
                        Target = def b.Target }
            | Call c ->
                Call
                    { c with
                        Arg = Array.map use_ c.Arg
                        Target = def c.Target }
            | Load l ->
                Load
                    { l with
                        Base = use_ l.Base
                        Offset = use_ l.Offset
                        Target = def l.Target }
            | Store -> failwith "Not Implemented"
            | Alloc -> failwith "Not Implemented"

        let instr = Array.map rewriteInstr this.Instr

        let trans =
            match this.Trans with
            | Branch b -> Branch { b with Value = use_ b.Value }
            | Return r ->
                let value =
                    match r.Value with
                    | None -> None
                    | Some v -> Some(use_ v)

                Return { r with Value = value }
            | Indirect s -> Indirect { s with Value = use_ s.Value }
            | Jump _
            | Unreachable _ -> this.Trans

        { this with
            Instr = instr
            Trans = trans }

type GraphNode = { Pred: int[]; Succ: int[] }

type Func =
    { Block: Block[]
      CFG: GraphNode[]
      Param: int[]
      Var: Var[]
      Span: Span
      Ret: Option<Type> }

    member this.Print(tw: IO.TextWriter) =
        let labelToString id = "'" + string id

        let varToString id =
            let var = this.Var[id]
            let name = if var.Name.Length > 0 then var.Name else "_"
            name + string id

        let paramToString id =
            let name = varToString id
            let ty = this.Var[id].Type.ToString

            $"{name}: {ty}"

        let valueToString v =
            match v with
            | Const c -> string c
            | Binding i -> varToString i

        let param = this.Param |> Array.map paramToString |> String.concat ", "

        let ret =
            match this.Ret with
            | Some ret -> " -> " + ret.ToString
            | None -> ""

        let header = $"fn ({param}){ret} {{"

        tw.WriteLine(header)

        for idx, block in Array.indexed this.Block do
            let id = labelToString idx
            tw.WriteLine $"    {id}: {{"

            for KeyValue(var, choose) in block.Phi do
                tw.Write(String.replicate 8 " ")
                tw.Write(varToString var)
                tw.Write " = Φ("
                let choose = choose |> Array.map valueToString
                let choose = String.Join(", ", choose)

                tw.Write choose
                tw.WriteLine ")"

            for stm in block.Instr do
                tw.Write(String.replicate 8 " ")

                tw.Write(varToString stm.Target)

                tw.Write " = "

                let stm =
                    match stm with
                    | Binary bin ->
                        let left = valueToString bin.Left
                        let op = bin.Op.ToString
                        let right = valueToString bin.Right
                        $"{left} {op} {right}"
                    | Assign a ->
                        let v = valueToString a.Value
                        v
                    | Unary n ->
                        let v = valueToString n.Value
                        $"! {v}"
                    | Call c -> failwith "Not Implemented"
                    | Load l -> failwith "Not Implemented"
                    | Store -> failwith "Not Implemented"
                    | Alloc -> failwith "Not Implemented"

                tw.WriteLine stm

            let trans =
                String.replicate 8 " "
                + match block.Trans with
                  | Jump i ->
                      let l = labelToString i.Target
                      $"jmp {l}"
                  | Branch b ->
                      let v = valueToString b.Value
                      let t = labelToString b.One
                      let f = labelToString b.Zero
                      $"br {v} ? {t} : {f}"
                  | Return r ->
                      "ret"
                      + match r.Value with
                        | Some i -> $" {valueToString i}"
                        | None -> ""
                  | Indirect s -> failwith "Not Implemented"
                  | Unreachable _ -> "Unreachable"

            tw.WriteLine trans |> ignore

            tw.WriteLine "    }" |> ignore

        tw.WriteLine "}"

type Module =
    { Func: Func[]
      Static: int[] }

    member this.Print(tw: IO.TextWriter) =
        for func in this.Func do
            func.Print tw

let transLocal trans (m: Module) =
    let trans f =
        { f with
            Block = f.Block |> Array.indexed |> Array.map (trans f) }

    { m with Func = Array.map trans m.Func }

let transRegional trans (m: Module) =
    { m with Func = Array.map trans m.Func }
