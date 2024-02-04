module Semantic.Semantic

open System.Collections.Generic

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
    { Param: Type[]
      Ret: Type }

    member this.Print() =
        let param = this.Param |> Array.map _.Print() |> String.concat ", "

        let fstr = $"|{param}| -> {this.Ret.Print()}"

        fstr

and Struct =
    { Name: Id
      Field: Map<string, Type>
      TVar: Var[] }

and Enum =
    { Name: Id
      Variant: Map<string, Type[]>
      TVar: Var[] }

and Var =
    { Level: int
      Id: int
      Span: Span
      Sym: Option<string> }

    member this.Print() =
        match this.Sym with
        | Some s -> if System.Char.IsUpper s[0] then s else "T" + s
        | None -> $"T{this.Id}"

and ADT = { Name: Id; Generic: Type[] }

and Type =
    /// bool signs if it's signed
    | TInt of bool * Integer
    | TFloat of Float
    | TBool
    | TChar
    | TString
    // named type can refer each other
    | TStruct of ADT
    | TEnum of ADT
    | TTuple of Type[]
    | TArray of Type * uint64
    | TFn of Function
    | TRef of Type
    | TSlice of Type
    | TVar of Var
    | TBound of Var
    | TNever

    member this.FindTVar() =
        seq {
            match this with
            | TInt _
            | TFloat _
            | TBool
            | TChar
            | TString -> ()
            | TVar v -> yield v
            | TBound t -> ()
            | TStruct a
            | TEnum a ->
                for v in a.Generic do
                    yield! v.FindTVar()
            | TTuple t ->
                for t in t do
                    yield! t.FindTVar()
            | TArray(t, _) -> yield! t.FindTVar()
            | TFn f ->
                for p in f.Param do
                    yield! p.FindTVar()

                yield! f.Ret.FindTVar()
            | TRef r -> yield! r.FindTVar()
            | TSlice s -> yield! s.FindTVar()
            | TNever -> ()
        }

    member this.Print() =
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
        | TString -> "string"
        | TStruct a
        | TEnum a ->
            if a.Generic.Length = 0 then
                a.Name.Sym
            else
                let tvar = a.Generic |> Array.map _.Print()
                let tvar = String.concat ", " tvar
                $"{a.Name.Sym}<{tvar}>"
        | TArray(t, c) -> $"[{t.Print}; {c}]"
        | TTuple t ->
            let element = t |> Array.map _.Print() |> String.concat ", "

            $"({element})"
        | TFn f -> f.Print()
        | TRef r -> $"&{r.Print()}"
        | TSlice s -> $"[{s.Print()}]"
        | TVar v
        | TBound v -> v.Print()
        | TNever -> "!"

    member this.Walk (onVar: Var -> Type) (onBound: Var -> Type) =
        let rec walk ty =
            match ty with
            | TInt _
            | TFloat _
            | TBool
            | TChar
            | TString -> ty
            | TStruct a ->
                TStruct
                    { a with
                        Generic = a.Generic |> Array.map walk }
            | TEnum a ->
                TEnum
                    { a with
                        Generic = a.Generic |> Array.map walk }
            | TTuple t -> t |> Array.map walk |> TTuple
            | TArray(t, c) -> TArray(walk t, c)
            | TFn f ->
                let param = f.Param |> Array.map walk
                let ret = walk f.Ret

                TFn { f with Param = param; Ret = ret }
            | TRef r -> TRef(walk r)
            | TSlice s -> TSlice(walk s)
            | TVar v -> onVar v
            | TBound t -> onBound t
            | TNever -> TNever

        walk this

    member this.Instantiate tvar inst =
        let map = Array.zip tvar inst |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TVar t
            | Some t -> t

        this.Walk TVar getMap

    member this.StripRef() =
        let rec stripRef ty =
            match ty with
            | TRef t -> stripRef t
            | _ -> ty

        stripRef this

let UnitType = TTuple [||]

type Trait = { Name: Id }

type Scheme =
    { Var: Var[]
      Ty: Type }

    member this.Print() =
        let ty = this.Ty.Print()

        if this.Var.Length = 0 then
            ty
        else
            let tvar = this.Var |> Array.map _.Print() |> String.concat ", "
            $"<{tvar}>{ty}"

type ModuleType =
    { Ty: Map<string, Type>
      Var: Map<string, Type>
      Module: Map<string, ModuleType> }

type SemanticInfo =
    { Binding: Dictionary<Id, Scheme>
      Expr: Dictionary<Expr, Scheme>
      Struct: Dictionary<Id, Struct>
      Enum: Dictionary<Id, Enum>
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
    | OverlapIml of Trait * Type * Type
