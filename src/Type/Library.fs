﻿module Type.Type

open System.Collections.Generic

open AST

// TODO: generic struct and enum

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
        let ofScope (v: Var) = v.scope = scopeId

        let tvar = (TFn this).FindTVar |> Seq.filter ofScope |> Array.ofSeq

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

and Symbol =
    { var: Dictionary<AST.Id, Type>
      ty: Dictionary<AST.Id, Type>
      stru: Dictionary<AST.Id, Struct>
      enum: Dictionary<AST.Id, Enum> }

and Type =
    | TPrim of Primitive
    | TStruct of AST.Id
    | TEnum of AST.Id
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
            | TStruct s -> ()
            // s.field |> Map.values |> Seq.map find |> Array.concat
            | TEnum e -> ()
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
        | TStruct s -> s.sym
        | TEnum e -> e.sym
        | Tuple t ->
            let element = t |> Array.map toString |> String.concat ", "

            $"({element})"
        | TFn f ->
            let param = f.param |> Array.map toString |> String.concat ", "

            $"|{param}| -> {f.ret.ToString}"
        | TRef r -> $"&{r.ToString}"
        | TVar v ->
            "T"
            + match v.sym with
              | Some s -> s
              | None -> $"{v.scope}{v.id}"
        | TNever -> "!"

    member this.Walk onVar =
        let walk (t: Type) = t.Walk onVar

        match this with
        | TPrim p -> TPrim p
        | TStruct s -> TStruct s
        | TEnum e -> TEnum e
        | Tuple t -> Array.map walk t |> Tuple
        | TFn f ->
            let param = Array.map walk f.param
            let ret = f.ret.Walk onVar

            TFn { f with param = param; ret = ret }
        | TRef r -> TRef(r.Walk onVar)
        | TVar v -> onVar v
        | TNever -> TNever

    member this.StripRef =
        let rec stripRef ty n =
            match ty with
            | TRef t -> stripRef t (n + 1)
            | _ -> ty

        stripRef this 0

let UnitType = Tuple [||]

type ModuleType =
    { ty: Map<string, Type>
      var: Map<string, Type>
      module_: Map<string, ModuleType> }