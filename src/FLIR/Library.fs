module FLIR.FLIR

open System

open Common.Span
open FLIR.Type

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

type Var = { Name: Option<string>; Type: Type }

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

/// Instrument
type Instr =
    | Load
    | Store
    | Assign of Assign
    | Binary of Binary
    | Unary of Unary
    | Call
    | Alloc

    member this.Target =
        match this with
        | Binary b -> b.Target
        | Assign a -> a.Target
        | Unary n -> n.Target
        | Load -> failwith "Not Implemented"
        | Store -> failwith "Not Implemented"
        | Call -> failwith "Not Implemented"
        | Alloc -> failwith "Not Implemented"

type Jump = { Target: int; Span: Span }

type Branch =
    { Value: Value
      Zero: int
      One: int
      Span: Span }

type Switch =
    { Value: Value
      Dest: (int * Value)[]
      Default: int
      Span: Span }

type Ret = { Value: Option<int>; Span: Span }

type Transfer =
    | Jump of Jump
    | Branch of Branch
    | Switch of Switch
    | Return of Ret
    | Unreachable of Span

/// Basic block
type Block =
    { Phi: unit[]
      Instr: Instr[]
      Trans: Transfer }

type Func =
    { Block: Block[]
      Param: int[]
      Var: Var[]
      Span: Span
      Ret: Option<int> }

    member this.Print(tw: IO.TextWriter) =
        let labelToString id = "'" + string id

        let varToString id =
            let var = this.Var[id]

            match var.Name with
            | Some name -> name
            | None -> "_" + string id

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
            | Some ret -> " -> " + this.Var[ret].Type.ToString
            | None -> ""

        let header = $"fn ({param}){ret} {{"

        tw.WriteLine(header)

        for (idx, block) in Array.indexed this.Block do
            let id = labelToString idx
            tw.WriteLine $"    {id}: {{"

            for stm in block.Instr do
                let stm =
                    String.replicate 8 " "
                    + varToString stm.Target
                    + " "
                    + match stm with
                      | Binary bin ->
                          let left = valueToString bin.Left
                          let op = bin.Op.ToString
                          let right = valueToString bin.Right
                          $"= {left} {op} {right}"
                      | Assign a ->
                          let v = valueToString a.Value
                          $"= {v}"
                      | Unary n ->
                          let v = valueToString n.Value
                          $"= ! {v}"
                      | Load -> failwith "Not Implemented"
                      | Store -> failwith "Not Implemented"
                      | Call -> failwith "Not Implemented"
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
                        | Some i -> $" {varToString i}"
                        | None -> ""
                  | Switch s -> failwith "Not Implemented"
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
