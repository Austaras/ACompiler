module Semantic.Type.Type

open System.Collections.Generic

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
    {
      // type variables waiting to be instantiated
      tvar: Var[]
      param: Type[]
      ret: Type }

    member this.Generalize scopeId =
        let ofScope (v: Var) = v.scope = scopeId

        let tvar =
            (TFn this).FindTVar |> Seq.filter ofScope |> Array.ofSeq |> Array.distinct

        { this with tvar = tvar }

    member this.Instantiate ty =
        let map = Array.zip this.tvar ty |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TVar t
            | Some t -> TVar t

        { tvar = [||]
          ret = this.ret.Walk getMap
          param = Array.map (fun (t: Type) -> t.Walk getMap) this.param }

and Struct =
    { name: AST.Id
      field: Map<string, Type>
      tvar: Var[] }

and Enum =
    { name: AST.Id
      variant: Map<string, Type[]>
      tvar: Var[] }

and Var =
    { scope: int
      id: int
      span: AST.Span
      sym: Option<string> }

    member this.ToString =
        "T"
        + match this.sym with
          | Some s -> s
          | None -> $"{this.scope}{this.id}"

and Symbol =
    { var: Dictionary<AST.Id, Type>
      ty: Dictionary<AST.Id, Type>
      stru: Dictionary<AST.Id, Struct>
      enum: Dictionary<AST.Id, Enum> }

and Type =
    | TPrim of Primitive
    /// named type can refer each other
    | TStruct of AST.Id * Type[]
    | TEnum of AST.Id * Type[]
    | Tuple of Type[]
    | TFn of Function
    | TRef of Type
    | TVar of Var
    | TNever

    member this.FindTVar =
        seq {
            match this with
            | TPrim _ -> ()
            | TVar v -> yield v
            | TStruct(_, v)
            | TEnum(_, v) ->
                for v in v do
                    yield! v.FindTVar
            | Tuple t ->
                for t in t do
                    yield! t.FindTVar
            | TFn f ->
                for p in f.param do
                    yield! p.FindTVar

                yield! f.ret.FindTVar
            | TRef r -> yield! r.FindTVar
            | TNever -> ()
        }

    member this.ToString =
        let toString (t: Type) = t.ToString

        match this with
        | TPrim p -> p.str
        | TStruct(t, v)
        | TEnum(t, v) ->
            if v.Length = 0 then
                t.sym
            else
                let tvar = Array.map toString v
                let tvar = String.concat "," tvar
                $"{t.sym}<{tvar}>"
        | Tuple t ->
            let element = t |> Array.map toString |> String.concat ", "

            $"({element})"
        | TFn f ->
            let param = f.param |> Array.map toString |> String.concat ", "

            let fstr = $"|{param}| -> {f.ret.ToString}"

            if f.tvar.Length = 0 then
                fstr
            else
                let tvar = Array.map (fun (v: Var) -> v.ToString) f.tvar
                let tvar = String.concat "," tvar
                $"<{tvar}>{fstr}"
        | TRef r -> $"&{r.ToString}"
        | TVar v -> v.ToString
        | TNever -> "!"

    member this.Walk onVar =
        let walk (t: Type) = t.Walk onVar

        match this with
        | TPrim p -> TPrim p
        | TStruct(s, v) -> TStruct(s, Array.map walk v)
        | TEnum(e, v) -> TEnum(e, Array.map walk v)
        | Tuple t -> Array.map walk t |> Tuple
        | TFn f ->
            let param = Array.map walk f.param
            let ret = f.ret.Walk onVar

            TFn { f with param = param; ret = ret }
        | TRef r -> TRef(r.Walk onVar)
        | TVar v -> onVar v
        | TNever -> TNever

    member this.Instantiate tvar inst =
        let map = Array.zip tvar inst |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TVar t
            | Some t -> t

        this.Walk getMap

    member this.StripRef =
        let rec stripRef ty =
            match ty with
            | TRef t -> stripRef t
            | _ -> ty

        stripRef this

let UnitType = Tuple [||]

type ModuleType =
    { ty: Map<string, Type>
      var: Map<string, Type>
      module_: Map<string, ModuleType> }
