module AST.Type

// TODO: Array
// TODO: generic

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

type Function = { arg: Type[]; ret: Type }

and Type =
    | Primitive of Primitive
    | Struct of Map<string, Type>
    | Enum of Map<string, Type[]>
    | Tuple of Type[]
    | Function of Function
    | Reference of Type
    | Never
