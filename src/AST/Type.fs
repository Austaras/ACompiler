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

type Function =
    { tvar: Var[]
      param: Type[]
      ret: Type }

    member this.Generalize scopeId =
        let rec find ty =
            match ty with
            | Primitive _ -> [||]
            | TVar v -> if v.scope = scopeId then [| v |] else [||]
            | TStruct s -> s.field |> Map.values |> Seq.map find |> Array.concat
            | TEnum(_) -> failwith "Not Implemented"
            | Tuple(_) -> failwith "Not Implemented"
            | TFn f ->
                let param = f.param |> Array.map find |> Array.concat
                Array.append param (find f.ret)
            | TRef r -> find r
            | TNever -> [||]

        let findTVar acc ty = Array.append acc (find ty)

        let tvar = Array.fold findTVar [||] this.param
        let tvar = Array.append tvar (find this.ret)

        { this with tvar = tvar }

    member this.Instantiate(makeTVar: unit -> Var) =
        let mapTVar tvar = tvar, makeTVar ()

        let map = this.tvar |> Array.map mapTVar |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TVar t
            | Some t -> TVar t

        { tvar = [||]
          ret = this.ret.Walk getMap
          param = Array.map (fun (t: Type) -> t.Walk getMap) this.param }

and Struct =
    { name: AST.Id
      field: Map<string, Type> }

and Enum =
    { name: AST.Id
      variant: Map<string, Type[]> }

and Var =
    { scope: int
      id: int
      span: AST.Span
      sym: Option<string> }

and Type =
    | Primitive of Primitive
    | TStruct of Struct
    | TEnum of Enum
    | Tuple of Type[]
    | TFn of Function
    | TRef of Type
    | TVar of Var
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
        | TVar v ->
            "T"
            + match v.sym with
              | Some s -> s
              | None -> $"{v.scope}{v.id}"
        | TNever -> "!"

    member this.Walk onvar =
        match this with
        | Primitive p -> Primitive p
        | TStruct s -> TStruct s
        | TEnum(_) -> failwith "Not Implemented"
        | Tuple(_) -> failwith "Not Implemented"
        | TFn f ->
            let param = Array.map (fun (t: Type) -> t.Walk onvar) f.param
            let ret = f.ret.Walk onvar

            TFn { f with param = param; ret = ret }
        | TRef r -> TRef(r.Walk onvar)
        | TVar v -> onvar v
        | TNever -> TNever

let UnitType = Tuple [||]

type ModuleType =
    { ty: Map<string, Type>
      var: Map<string, Type>
      module_: Map<string, ModuleType> }
