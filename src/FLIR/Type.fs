module FLIR.Type

type Integer =
    | I1
    | I8
    | I32
    | I64

type Float =
    | F32
    | F64

type Function = { param: Type[]; ret: Type }

and Type =
    | TVoid
    | TInt of Integer
    | TFloat of Float
    | TMany of Type[]
    | TFn of Function
    | TRef of Type
    | TNever
