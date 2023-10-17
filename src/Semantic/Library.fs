module Semantic.Semantic

open System.Collections.Generic

open Common.Span
open AST.AST
open Util.Util
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
      // type variables waiting to be instantiated
      TVar: Var[]
      Param: Type[]
      Ret: Type }

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
          Param = Array.map (fun (t: Type) -> t.Walk getMap) this.Param }

and Struct =
    { Name: Id
      Field: Map<string, Type>
      TVar: Var[] }

and Enum =
    { name: Id
      variant: Map<string, Type[]>
      tvar: Var[] }

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
    /// named type can refer each other
    | TStruct of Id * Type[]
    | TEnum of Id * Type[]
    | TTuple of Type[]
    | TFn of Function
    | TRef of Type
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
            | TFn f ->
                for p in f.Param do
                    yield! p.FindTVar

                yield! f.Ret.FindTVar
            | TRef r -> yield! r.FindTVar
            | TNever -> ()
        }

    member this.ToString =
        let toString (t: Type) = t.ToString

        match this with
        | TInt(true, I8) -> "i8"
        | TInt(false, I8) -> "u8"
        | TInt(true, I32) -> "i32"
        | TInt(false, I32) -> "u32"
        | TInt(true, I64) -> "i64"
        | TInt(false, I64) -> "u64"
        | TInt(true, ISize) -> "isize"
        | TInt(false, ISize) -> "usize"
        | TBool -> "bool"
        | TFloat F32 -> "f32"
        | TFloat F64 -> "f64"
        | TChar -> "char"
        | TStruct(t, v)
        | TEnum(t, v) ->
            if v.Length = 0 then
                t.Sym
            else
                let tvar = Array.map toString v
                let tvar = String.concat "," tvar
                $"{t.Sym}<{tvar}>"
        | TTuple t ->
            let element = t |> Array.map toString |> String.concat ", "

            $"({element})"
        | TFn f ->
            let param = f.Param |> Array.map toString |> String.concat ", "

            let fstr = $"|{param}| -> {f.Ret.ToString}"

            if f.TVar.Length = 0 then
                fstr
            else
                let tvar = Array.map (fun (v: Var) -> v.ToString) f.TVar
                let tvar = String.concat "," tvar
                $"<{tvar}>{fstr}"
        | TRef r -> $"&{r.ToString}"
        | TVar v -> v.ToString
        | TNever -> "!"

    member this.Walk onVar =
        let walk (t: Type) = t.Walk onVar

        match this with
        | TInt _
        | TFloat _
        | TBool
        | TChar -> this
        | TStruct(s, v) -> TStruct(s, Array.map walk v)
        | TEnum(e, v) -> TEnum(e, Array.map walk v)
        | TTuple t -> Array.map walk t |> TTuple
        | TFn f ->
            let param = Array.map walk f.Param
            let ret = f.Ret.Walk onVar

            TFn { f with Param = param; Ret = ret }
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

let UnitType = TTuple [||]

type ModuleType =
    { ty: Map<string, Type>
      var: Map<string, Type>
      module_: Map<string, ModuleType> }

type Location =
    | Static
    | Any
    | Stack
    | Heap

type VarInfo = { Ty: Type; Mut: bool; Loc: Location }

type SemanticInfo =
    { Var: Dictionary<Id, VarInfo>
      Ty: Dictionary<Id, Type>
      Struct: Dictionary<Id, Struct>
      Enum: Dictionary<Id, Enum>
      Capture: MultiMap<Either<Fn, Closure>, Id> }

    static member Empty() =
        { Var = Dictionary()
          Ty = Dictionary()
          Struct = Dictionary()
          Enum = Dictionary()
          Capture = MultiMap() }

    member this.AddVar(id, ty, ?mut, ?static_) =
        let mut =
            match mut with
            | Some m -> m
            | None -> false

        let loc =
            match static_ with
            | Some true -> Static
            | _ -> Any

        this.Var[id] <- { Ty = ty; Mut = mut; Loc = loc }

    member this.TypeOfVar id = this.Var[id].Ty

    member this.ModifyVarTy id mapper =
        let old = this.Var[id]
        this.Var[id] <- { old with Ty = mapper this.Var[id].Ty }

    member this.AddRef id =
        let old = this.Var[id]

        match old.Loc with
        | Any -> this.Var[id] <- { old with Loc = Stack }
        | _ -> ()

    member internal this.DetectLoop id =
        let visited = HashSet<Type>()

        match this.Ty[id] with
        | TVar _
        | TInt _
        | TFloat _
        | TBool
        | TChar
        | TRef _
        | TFn _
        | TNever -> None
        | TStruct(_, _) -> failwith "Not Implemented"
        | TEnum(_, _) -> failwith "Not Implemented"
        | TTuple(_) -> failwith "Not Implemented"

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
