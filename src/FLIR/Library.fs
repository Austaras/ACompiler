module FLIR.FLIR

open Common.Span
open AST

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
    | Shr of bool

type CmpOp =
    | Eq
    | Lt
    | LtEq of bool
    | NotEq of bool
    | GtEq of bool
    | Gt of bool

type Label = { Name: string; id: int; span: Span }

type Var = { Name: string; id: int; span: Span }

type Bin =
    { Op: BinOp
      Fst: Exp
      Snd: Exp
      Span: Span }

and Call = { Callee: Exp; Arg: Exp[]; Span: Span }

and Mem = { Loc: Exp; Span: Span }

and Seq = { Stm: Stm; Exp: Exp; Span: Span }

and Exp =
    | Const of int
    | Name of Label
    | Var of Var
    | Bin of Bin
    | Call of Call
    | Mem of Mem
    | ESeq of Seq

and Move = { From: Exp; To: Exp; Span: Span }

and Stm =
    | Move of Move
    | SExp of Exp
