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
      Generic: Generic[] }

and Enum =
    { Name: Id
      Variant: Map<string, Type[]>
      Generic: Generic[] }

and Var = { Level: int; Id: int; Span: Span }

and Generic =
    { Id: int
      GroupId: int
      Sym: string }

    member this.Print() =
        if this.Sym.Length = 0 then $"T{this.Id}" else this.Sym

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
    | TGen of Generic
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
            | TGen _ -> ()
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
        | TString -> "str"
        | TStruct a
        | TEnum a ->
            if a.Generic.Length = 0 then
                a.Name.Sym
            else
                let tvar = a.Generic |> Array.map _.Print()
                let tvar = String.concat ", " tvar
                $"{a.Name.Sym}<{tvar}>"
        | TArray(t, c) -> $"[{t.Print()}; {c}]"
        | TTuple t ->
            let element = t |> Array.map _.Print() |> String.concat ", "

            $"({element})"
        | TFn f -> f.Print()
        | TRef r -> $"&{r.Print()}"
        | TSlice s -> $"[{s.Print()}]"
        | TVar _ -> "TVAR"
        | TGen b -> b.Print()
        | TNever -> "!"

    member this.Walk (onVar: Var -> Type) (onGen: Generic -> Type) =
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
            | TGen t -> onGen t
            | TNever -> TNever

        walk this

    member this.Instantiate gen inst =
        let map = Array.zip gen inst |> Map.ofArray

        let getMap t =
            match Map.tryFind t map with
            | None -> TGen t
            | Some t -> t

        this.Walk TVar getMap

    member this.StripRef() =
        let rec stripRef ty =
            match ty with
            | TRef t -> stripRef t
            | _ -> ty

        stripRef this

    member this.IsVar =
        match this with
        | TVar _ -> true
        | _ -> false

let UnitType = TTuple [||]

type Trait =
    { Name: Id
      Method: Map<string, Function>
      Super: Trait[] }

type Pred = { Trait: Trait; Type: Type }

type Scheme =
    { Generic: Generic[]
      Pred: Pred[]
      Type: Type }

    member this.Print() =
        let ty = this.Type.Print()

        if this.Generic.Length = 0 then
            ty
        else
            let tvar = this.Generic |> Array.map _.Print() |> String.concat ", "
            $"<{tvar}>{ty}"

type ModuleType =
    { Ty: Map<string, Type>
      Var: Map<string, Type>
      Module: Map<string, ModuleType> }

type SemanticInfo =
    { Binding: Dictionary<Id, Id>
      DeclTy: Dictionary<Id, Scheme>
      ExprTy: Dictionary<Expr, Scheme>
      Struct: Dictionary<Id, Struct>
      Enum: Dictionary<Id, Enum>
      Capture: MultiMap<Closure, Id>
      Trait: Dictionary<Id, Trait>
      Module: ModuleType }

type Error =
    | Undefined of Id
    | UndefinedField of Span * string
    | UndefinedMethod of Span * Type * string
    | UndefinedVariant of Id * Id
    | DuplicateDefinition of Id * Id
    | DuplicateField of Id
    | DuplicateVariant of Id
    | LoopInDefintion of Id * Id
    | PrivatecInPublic of Id * Id
    | ExpectEnum of Id * Type
    | ExpectStruct of Id * Type
    | OrPatDifferent of Span * string[] * string[]
    | LengthMismatch of Span * int * int
    | TypeMismatch of Type * Type * Span
    | GenericMismatch of Type * Type[] * Span
    | FailToUnify of Type * Type * Span
    | CalleeNotCallable of Type * Span
    | AssignImmutable of Id * Span
    | RefutablePat of Span
    | LoopInType of Id[]
    | CaptureDynamic of Id
    | OverlapImpl of Trait * Scheme * Scheme * Span
    | UnboundGeneric of Generic
    | TraitNotImpl of Trait * Type * Span
