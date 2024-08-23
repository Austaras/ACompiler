module Semantic.Semantic

open System.Collections.Generic

open Common.Span
open Common.MultiMap
open Syntax.AST

[<ReferenceEquality>]
type Def =
    { Sym: string
      Span: Span }

    static member Create sym span = { Sym = sym; Span = span }

    static member FromId(id: Id) = { Sym = id.Sym; Span = id.Span }

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

and Var = { Level: int; Id: int; Span: Span }

and Generic =
    { Id: int
      GroupId: int
      Span: Span
      Sym: string }

    member this.Print() =
        if this.Sym.Length = 0 then $"T{this.Id}" else this.Sym

/// Type constructor
and Cons = { Name: Id; Generic: Type[] }

and Type =
    /// bool signs if it's signed
    | TInt of bool * Integer
    | TFloat of Float
    | TBool
    | TChar
    | TString
    // named type can refer each other
    | TStruct of Cons
    | TEnum of Cons
    | TTrait of Cons
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
            | TEnum a
            | TTrait a ->
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

    member this.FindTGen() =
        seq {
            match this with
            | TInt _
            | TFloat _
            | TBool
            | TChar
            | TString
            | TVar _ -> ()
            | TGen g -> yield g
            | TStruct a
            | TEnum a
            | TTrait a ->
                for v in a.Generic do
                    yield! v.FindTGen()
            | TTuple t ->
                for t in t do
                    yield! t.FindTGen()
            | TArray(t, _) -> yield! t.FindTGen()
            | TFn f ->
                for p in f.Param do
                    yield! p.FindTGen()

                yield! f.Ret.FindTGen()
            | TRef r -> yield! r.FindTGen()
            | TSlice s -> yield! s.FindTGen()
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
        | TEnum a
        | TTrait a ->
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
            | TTrait a ->
                TTrait
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

    member this.InstantiateWithMap map =

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

let UnitType = TTuple [||]

type Struct =
    { Name: Id
      Field: Map<string, Type>
      Generic: Generic[] }

and Enum =
    { Name: Id
      Variant: Map<string, Type[]>
      Generic: Generic[] }

and Trait =
    { Name: Id
      Method: Map<string, Function>
      Generic: Generic[]
      ObjectSafe: bool
      Super: Trait[]
      DepName: Id[] }

    member this.FreeVarLength = this.Generic.Length - this.DepName.Length

    member this.HasDep name =
        Array.exists (fun (d: Id) -> d.Sym = name) this.DepName

and Pred = { Trait: Trait; Type: Type[] }

type Impl =
    { Generic: Generic[]
      Pred: Pred[]
      Type: Type[] }

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
            let res = $"<{tvar}>{ty}"

            if this.Pred.Length = 0 then
                res
            else
                let print { Type = ty; Trait = tr } =
                    let bound = ty[0].Print() + ": " + tr.Name.Sym

                    if ty.Length = 1 then
                        bound
                    else
                        let print (idx, ty: Type) =
                            let ty = ty.Print()
                            let idx = idx + 1

                            if idx >= tr.FreeVarLength then
                                let name = tr.DepName[idx - tr.FreeVarLength].Sym
                                $"{name} = {ty}"
                            else
                                ty

                        let gen = ty[1..] |> Array.indexed |> Array.map print |> String.concat ", "
                        $"{bound}<{gen}>"

                let pred = this.Pred |> Array.map print |> String.concat ", "

                $"{res} where {pred}"

type ModuleType =
    { Ty: Map<string, Type>
      Var: Map<string, Type>
      Module: Map<string, ModuleType> }

type WellKnown =
    { Slice: Def
      String: Def
      Range: Def

      Int: Def
      Float: Def
      Num: Def
      mutable Eq: Def
      mutable Cmp: Def
      mutable Add: Def
      mutable Index: Def }

type SemanticInfo =
    { WellKnown: WellKnown
      Binding: Dictionary<Id, Id>
      DeclTy: Dictionary<Id, Scheme>
      ExprTy: Dictionary<Expr, Type>
      PatTy: Dictionary<Pat, Type>
      Struct: Dictionary<Id, Struct>
      Enum: Dictionary<Id, Enum>
      Capture: MultiMap<Closure, Id>
      Trait: Dictionary<Id, Trait>
      Module: ModuleType }

    static member Create() =
        let well =
            { Slice = Def.Create "slice" Span.dummy
              String = Def.Create "string" Span.dummy
              Range = Def.Create "Range" Span.dummy
              Int = Def.Create "Int" Span.dummy
              Float = Def.Create "Float" Span.dummy
              Num = Def.Create "Num" Span.dummy
              Eq = Def.Create "Eq" Span.dummy
              Cmp = Def.Create "Cmp" Span.dummy
              Add = Def.Create "Add" Span.dummy
              Index = Def.Create "Index" Span.dummy }

        let sema =
            { WellKnown = well
              Binding = Dictionary(HashIdentity.Reference)
              DeclTy = Dictionary(HashIdentity.Reference)
              ExprTy = Dictionary(HashIdentity.Reference)
              PatTy = Dictionary(HashIdentity.Reference)
              Struct = Dictionary(HashIdentity.Reference)
              Enum = Dictionary(HashIdentity.Reference)
              Capture = MultiMap(HashIdentity.Reference)
              Trait = Dictionary(HashIdentity.Reference)
              Module =
                { Ty = Map.empty
                  Var = Map.empty
                  Module = Map.empty } }

        sema

type Error =
    | AmbiguousTypeVar of Var
    | Undefined of Id
    | UndefinedField of Span * string
    | UndefinedMethod of Span * Type * string
    | UndefinedAssocType of Span * Id
    | UndefinedVariant of Id * Id
    | DuplicateDefinition of Id * Id
    | DuplicateField of Id
    | DuplicateVariant of Id
    | LoopInDefintion of Id * Id
    | PrivatecInPublic of Id * Id
    | ExpectEnum of Id * Type
    | ExpectStruct of Id * Type
    | OrPatDiff of Span * string[] * string[]
    | OrPatMutDiff of Id * Id
    | ParamLenMismatch of Span * int * int
    | TypeMismatch of Type * Type * Span
    | GenericMismatch of Type * Type[] * Span
    | FailToUnify of Type * Type * Span
    | CalleeNotCallable of Type * Span
    | AssignImmutable of Id * Span
    | RefutablePat of Span
    | LoopInType of Id[]
    | CaptureDynamic of Id
    | OverlapImpl of Trait * Type[] * Type[] * Span
    | UnboundGeneric of Generic
    | UnboundSelfType of Span
    | TraitNotImpl of Pred * Span
    | TraitMemberMissing of Id * Id * Span
