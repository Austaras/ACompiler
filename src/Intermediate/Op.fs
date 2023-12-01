module Intermediate.Op

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

type CmpOp =
    | Eq
    | Lt
    /// signed or not
    | LtEq of bool
    /// signed or not
    | NotEq of bool
    /// signed or not
    | GtEq of bool
    /// signed or not
    | Gt of bool
