module AST.AST

type Span =
    { first: int
      last: int }

    static member make first last = { first = first; last = last }

type Lit =
    | String of string
    | Char of char
    | Int of uint
    | Float of double
    | Bool of bool
