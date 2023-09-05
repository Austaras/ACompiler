module FLIR.Type

open AST

type Integer =
    | I8
    | I32
    | I64
    | ISize

type Primitive =
    /// bool signs if it's signed
    | Int of bool * Integer
    | Bool
    | F32
    | F64
    | Char

type Function = { param: Type[]; ret: Type }

and Type =
    | TPrim of Primitive
    | TEnum of AST.Id
    | Tuple of Type[]
    | TFn of Function
    | TRef of Type
    | TNever
