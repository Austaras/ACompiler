module AST.Type

// TODO: Array
// TODO: generic

open Config.Config

type Integer =
    | I8
    | I32
    | I64
    | ISize

    member this.size(arch: Arch) =
        match this with
        | I8 -> 1
        | I32 -> 4
        | I64 -> 8
        | ISize -> arch.ptrSize

type Primitive =
    /// bool signs if it's signed
    | Int of bool * Integer
    | Bool
    | F32
    | F64
    | Char

    member this.size(arch: Arch) =
        match this with
        | Int(_, i) -> i.size arch
        | Bool -> 1
        | F32 -> 4
        | F64 -> 8
        | Char -> 4

    member this.str =
        match this with
        | Int(true, I8) -> "i8"
        | Int(false, I8) -> "u8"
        | Int(true, I32) -> "i32"
        | Int(false, I32) -> "u32"
        | Int(true, I64) -> "i64"
        | Int(false, I64) -> "u64"
        | Int(true, ISize) -> "isize"
        | Int(false, ISize) -> "usize"
        | Bool -> "bool"
        | F32 -> "f32"
        | F64 -> "f64"
        | Char -> "char"

type Function =
    { arg: Type[]
      ret: Type
      captureEnv: bool }

    member this.size(arch: Arch) =
        if this.captureEnv then arch.ptrSize * 2 else arch.ptrSize

and Type =
    | Primitive of Primitive
    | Struct of Map<string, Type>
    | Enum of Map<string, Type[]>
    | Tuple of Type[]
    | Function of Function
    | Reference of Type
    | Never
