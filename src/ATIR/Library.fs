module ATIR.ATIR

open Common.Span
open Intermediate.Op

type Const = { Value: int; Span: Span }

type Label =
    { Name: option<string>
      Id: int
      Span: Span }

type Temp = { Id: int; Span: Span }

type Bin =
    { Op: BinOp
      Left: Exp
      Right: Exp
      Span: Span }

and Call = { Callee: Exp; Arg: Exp[]; Span: Span }

and Mem = { Loc: Exp; Span: Span }

and ESeq = { Stm: Stm; Exp: Exp; Span: Span }

and Exp =
    | Const of Const
    | Name of Label
    | Temp of Temp
    | Bin of Bin
    | Mem of Mem
    | Call of Call
    | ESeq of ESeq

    member this.Span =
        match this with
        | Const c -> c.Span
        | Name n -> n.Span
        | Temp t -> t.Span
        | Bin b -> b.Span
        | Mem m -> m.Span
        | Call c -> c.Span
        | ESeq e -> e.Span

and Move = { From: Exp; To: Exp; Span: Span }

and Jump = { To: Exp; Label: Label[]; Span: Span }

and CJump =
    { Left: Exp
      Op: CmpOp
      Right: Exp
      TLabel: Label
      FLabel: Label
      Span: Span }

and Seq = { Fst: Stm; Snd: Stm; Span: Span }

and Stm =
    | Move of Move
    | Exp of Exp
    | Jump of Jump
    | CJump of CJump
    | Seq of Seq
    | Label of Label

    member this.Span =
        match this with
        | Move m -> m.Span
        | Exp e -> e.Span
        | Jump j -> j.Span
        | CJump c -> c.Span
        | Seq s -> s.Span
        | Label l -> l.Span
