module AST.Type

// TODO: Array and String
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

type Function = { param: Type[]; ret: Type }

and Struct =
    { name: AST.Id
      field: Map<string, Type> }

and Enum =
    { name: AST.Id
      variant: Map<string, Type[]> }

and Type =
    | Primitive of Primitive
    | TStruct of Struct
    | TEnum of Enum
    | Tuple of Type[]
    | TFn of Function
    | TRef of Type
    | TVar of AST.Id
    | TNever

    member this.ToString =
        match this with
        | Primitive p -> p.str
        | TStruct s -> s.name.sym
        | TEnum(_) -> failwith "Not Implemented"
        | Tuple(_) -> failwith "Not Implemented"
        | TFn f ->
            let param = Array.map (fun (t: Type) -> t.ToString) f.param

            let param = String.concat ", " param

            $"|{param}| -> {f.ret.ToString}"
        | TRef r -> $"&{r.ToString}"
        | TVar v -> v.sym
        | TNever -> "!"

let UnitType = Tuple [||]

type ModuleType =
    { ty: Map<string, Type>
      var: Map<string, Type>
      module_: Map<string, ModuleType> }
