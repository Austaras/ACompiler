module FLIR.FLIR

open FLIR.Type

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
    | Shr
    | Eq
    | Lt
    | LtEq
    | NotEq
    | GtEq
    | Gt

type Bin =
    { ty: Integer
      op: BinOp
      fst: string
      snd: string }

type FLIR = Bin of Bin
