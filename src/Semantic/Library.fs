module Semantic.Semantic

open System.Collections.Generic

open AST
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
      tvar: Var[]
      param: Type[]
      ret: Type }

    member this.Generalize scopeId =
        let ofScope (v: Var) = v.scope = scopeId

        let tvar =
            (TFn this).FindTVar |> Seq.filter ofScope |> Array.ofSeq |> Array.distinct

        { this with
            tvar = Array.append this.tvar tvar }

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
        match this.sym with
        | Some s -> if System.Char.IsUpper s[0] then s else "T" + s
        | None -> $"T{this.scope}{this.id}"

and Type =
    /// bool signs if it's signed
    | TInt of bool * Integer
    | TFloat of Float
    | TBool
    | TChar
    /// named type can refer each other
    | TStruct of AST.Id * Type[]
    | TEnum of AST.Id * Type[]
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
                for p in f.param do
                    yield! p.FindTVar

                yield! f.ret.FindTVar
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
                t.sym
            else
                let tvar = Array.map toString v
                let tvar = String.concat "," tvar
                $"{t.sym}<{tvar}>"
        | TTuple t ->
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
        | TInt _
        | TFloat _
        | TBool
        | TChar -> this
        | TStruct(s, v) -> TStruct(s, Array.map walk v)
        | TEnum(e, v) -> TEnum(e, Array.map walk v)
        | TTuple t -> Array.map walk t |> TTuple
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

type VarInfo = { ty: Type; mut: bool; loc: Location }

type SemanticInfo =
    { var: Dictionary<AST.Id, VarInfo>
      ty: Dictionary<AST.Id, Type>
      stru: Dictionary<AST.Id, Struct>
      enum: Dictionary<AST.Id, Enum>
      capture: MultiMap<Either<AST.Fn, AST.Closure>, AST.Id> }

    static member Empty() =
        { var = Dictionary()
          ty = Dictionary()
          stru = Dictionary()
          enum = Dictionary()
          capture = MultiMap() }

    member this.AddVar(id, ty, ?mut, ?static_) =
        let mut =
            match mut with
            | Some m -> m
            | None -> false

        let loc =
            match static_ with
            | Some true -> Static
            | _ -> Any

        this.var[id] <- { ty = ty; mut = mut; loc = loc }

    member this.TypeOfVar id = this.var[id].ty

    member this.ModifyVarTy id mapper =
        let old = this.var[id]
        this.var[id] <- { old with ty = mapper this.var[id].ty }

    member internal this.DetectLoop id =
        let visited = HashSet<Type>()

        match this.ty[id] with
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
