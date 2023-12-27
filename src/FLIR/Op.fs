module FLIR.Op

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
        | Shr false -> ">>"
        | Shr true -> ">>>"
        | Eq -> "=="
        | NotEq -> "!="
        | Lt _ -> "<"
        | LtEq _ -> "<="
        | GtEq _ -> ">="
        | Gt _ -> ">"
