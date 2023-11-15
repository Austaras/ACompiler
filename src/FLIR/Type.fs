module FLIR.Type

type Integer =
    | I1
    | I8
    | I32
    | I64

type Float =
    | F32
    | F64

type Function = { Param: Type[]; Ret: Type }

and Type =
    | TInt of Integer
    | TFloat of Float
    | TMany of Type[]
    | TFn of Function
    | TRef of Type

type MonoMode =
    | MSize of int
    | MType of Type

type Location =
    | Static
    | Any
    | Stack
    | Heap
