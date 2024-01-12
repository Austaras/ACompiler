module Semantic.Semantic

open Common.Span
open AST.AST
open Util.MultiMap

type Integer =
    | I8
    | I32
    | I64
    | ISize

type Float =
    | F32
    | F64

type Function =
    {
        /// type variables waiting to be instantiated
        TVar: Var[]
        Param: Type[]
        Ret: Type
    }

    member this.Generalize scopeId =
        let ofScope (v: Var) = v.Scope = scopeId

        let tvar =
            (TFn this).FindTVar
            |> Seq.filter ofScope
            |> Array.ofSeq
            |> Array.append this.TVar
            |> Array.distinct

        { this with TVar = tvar }

    member this.Instantiate ty =
        let map = Array.zip this.TVar ty |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TVar t
            | Some t -> TVar t

        { TVar = [||]
          Ret = this.Ret.Walk getMap
          Param = this.Param |> Array.map _.Walk(getMap) }

and Struct =
    { Name: Id
      Field: Map<string, Type>
      TVar: Var[] }

and Enum =
    { Name: Id
      Variant: Map<string, Type[]>
      TVar: Var[] }

and Var =
    { Scope: int
      Id: int
      Span: Span
      Sym: Option<string> }

    member this.ToString =
        match this.Sym with
        | Some s -> if System.Char.IsUpper s[0] then s else "T" + s
        | None -> $"T{this.Scope}{this.Id}"

and Type =
    /// bool signs if it's signed
    | TInt of bool * Integer
    | TFloat of Float
    | TBool
    | TChar
    // named type can refer each other
    | TStruct of Id * Type[]
    | TEnum of Id * Type[]
    | TTuple of Type[]
    | TArray of Type * uint64
    | TFn of Function
    | TRef of Type
    | TSlice of Type
    | TVar of Var
    | TNever

    member this.FindTVar =
        seq {
            match this with
            | TInt _
            | TFloat _
            | TBool
            | TChar -> ()
            | TVar v -> yield v
            | TStruct(_, v)
            | TEnum(_, v) ->
                for v in v do
                    yield! v.FindTVar
            | TTuple t ->
                for t in t do
                    yield! t.FindTVar
            | TArray(t, _) -> yield! t.FindTVar
            | TFn f ->
                for p in f.Param do
                    yield! p.FindTVar

                yield! f.Ret.FindTVar
            | TRef r -> yield! r.FindTVar
            | TSlice s -> yield! s.FindTVar
            | TNever -> ()
        }

    member this.ToString =
        match this with
        | TInt(true, I8) -> "i8"
        | TInt(false, I8) -> "u8"
        | TInt(true, I32) -> "i32"
        | TInt(false, I32) -> "u32"
        | TInt(true, I64) -> "i64"
        | TInt(false, I64) -> "u64"
        | TInt(true, ISize) -> "int"
        | TInt(false, ISize) -> "uint"
        | TBool -> "bool"
        | TFloat F32 -> "f32"
        | TFloat F64 -> "f64"
        | TChar -> "char"
        | TStruct(t, v)
        | TEnum(t, v) ->
            if v.Length = 0 then
                t.Sym
            else
                let tvar = v |> Array.map _.ToString
                let tvar = String.concat ", " tvar
                $"{t.Sym}<{tvar}>"
        | TArray(t, c) -> $"[{t.ToString}; {c}]"
        | TTuple t ->
            let element = t |> Array.map _.ToString |> String.concat ", "

            $"({element})"
        | TFn f ->
            let param = f.Param |> Array.map _.ToString |> String.concat ", "

            let fstr = $"|{param}| -> {f.Ret.ToString}"

            if f.TVar.Length = 0 then
                fstr
            else
                let tvar = f.TVar |> Array.map _.ToString |> String.concat ", "
                $"<{tvar}>{fstr}"
        | TRef r -> $"&{r.ToString}"
        | TSlice s -> $"[{s.ToString}]"
        | TVar v -> v.ToString
        | TNever -> "!"

    member this.Walk onVar =
        match this with
        | TInt _
        | TFloat _
        | TBool
        | TChar -> this
        | TStruct(s, v) -> TStruct(s, v |> Array.map _.Walk(onVar))
        | TEnum(e, v) -> TEnum(e, v |> Array.map _.Walk(onVar))
        | TTuple t -> t |> Array.map _.Walk(onVar) |> TTuple
        | TArray(t, c) -> TArray(t.Walk onVar, c)
        | TFn f ->
            let param = f.Param |> Array.map _.Walk(onVar)
            let ret = f.Ret.Walk onVar

            TFn { f with Param = param; Ret = ret }
        | TRef r -> TRef(r.Walk onVar)
        | TSlice s -> TSlice(s.Walk onVar)
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

let UnitType = TTuple [||]

type ModuleType =
    { Ty: Map<string, Type>
      Var: Map<string, Type>
      Module: Map<string, ModuleType> }

type SemanticInfo =
    { Var: Map<Id, Type>
      Struct: Map<Id, Struct>
      Enum: Map<Id, Enum>
      Capture: MultiMap<Closure, Id>
      Module: ModuleType }

type Error =
    | Undefined of Id
    | UndefinedField of Span * string
    | UndefinedVariant of Id * Id
    | DuplicateDefinition of Id
    | DuplicateField of Id
    | DuplicateVariant of Id
    | LoopInDefintion of Id * Id
    | PrivatecInPublic of Id * Id
    | ExpectEnum of Id * Type
    | OrPatDifferent of Span * string[] * string[]
    | PayloadMismatch of Span * Enum
    | TupleLengthMismatch of Span * int * int
    | TypeMismatch of Type * Type * Span
    | GenericMismatch of Type * Type[] * Span
    | FailToUnify of Type * Type * Span
    | CalleeNotCallable of Type * Span
    | AssignImmutable of Id * Span
    | RefutablePat of Span
    | LoopInType of Id[]
    | CaptureDynamic of Id
