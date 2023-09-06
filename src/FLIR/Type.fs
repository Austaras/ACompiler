module FLIR.Type

type Integer =
    | I1
    | I8
    | I32
    | I64
    | ISize

type Primitive =
    | Int of Integer
    | F32
    | F64

type Function = { param: Type[]; ret: Type }

and Type =
    | TPrim of Primitive
    | TMany of Type[]
    | TFn of Function
    | TRef of Type
    | TNever
