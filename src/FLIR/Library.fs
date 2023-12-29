module FLIR.FLIR

open System

open Common.Span
open FLIR.Op
open FLIR.Type

type MonoMode =
    | MSize of int
    | MType of Type

type Location =
    | Static
    | Unambiguous
    | Automatic
    | Irregular

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

type Negative =
    { Target: int
      Value: Value
      Span: Span }

type Stm =
    | Load
    | Store
    | Assign of Assign
    | Binary of Binary
    | Negative of Negative
    | Call
    | Alloc

    member this.Target =
        match this with
        | Binary b -> b.Target
        | Assign a -> a.Target
        | Negative n -> n.Target
        | Load -> failwith "Not Implemented"
        | Store -> failwith "Not Implemented"
        | Call -> failwith "Not Implemented"
        | Alloc -> failwith "Not Implemented"

type Branch = { Value: Value; Zero: int; Other: int }

type Transfer =
    | Jump of int
    | Branch of Branch
    | Ret of Option<int>

type Block =
    { Stm: Stm[]
      Trans: Transfer
      Span: Span }

type Func =
    { Block: Block[]
      Param: int[]
      Var: Var[]
      Span: Span
      Ret: Option<int> }

    member this.ToString =
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

        let res = Text.StringBuilder()

        let param = this.Param |> Array.map paramToString |> String.concat ", "

        let header =
            $"fn ({param})"
            + match this.Ret with
              | Some ret -> " -> " + this.Var[ret].Type.ToString
              | None -> ""
            + " {"

        let _ = res.AppendLine(header)

        for (idx, block) in Array.indexed this.Block do
            let id = labelToString idx
            let _ = res.AppendLine $"    {id}: {{"

            for stm in block.Stm do
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
                      | Negative n ->
                          let v = valueToString n.Value
                          $"= ! {v}"
                      | Load -> failwith "Not Implemented"
                      | Store -> failwith "Not Implemented"
                      | Call -> failwith "Not Implemented"
                      | Alloc -> failwith "Not Implemented"

                res.AppendLine(stm) |> ignore

            let trans =
                String.replicate 8 " "
                + match block.Trans with
                  | Jump i ->
                      let l = labelToString i
                      $"jmp {l}"
                  | Branch b ->
                      let v = valueToString b.Value
                      let t = labelToString b.Other
                      let f = labelToString b.Zero
                      $"br {v} ? {t} : {f}"
                  | Ret v ->
                      "ret"
                      + match v with
                        | Some i -> $" {varToString i}"
                        | None -> ""

            res.AppendLine trans |> ignore

            res.AppendLine "    }" |> ignore

        let _ = res.AppendLine("}")

        res.ToString()

type Module =
    { Func: Func[]
      Static: int[] }

    member this.ToString =
        this.Func |> Array.map _.ToString |> String.concat Environment.NewLine
