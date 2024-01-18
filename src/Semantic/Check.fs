module Semantic.Check

open System.Collections.Generic

// TODO: module system
// TODO: type alias
// TODO: trait, operator overloading and type alias
// TODO: pipe and compose operator

open Common.Span
open Util.Util
open Util.MultiMap
open AST.AST
open Semantic.Semantic

let internal primitive =
    [| TInt(true, I8)
       TInt(false, I8)
       TInt(true, I32)
       TInt(false, I32)
       TInt(true, I64)
       TInt(false, I64)
       TInt(true, ISize)
       TInt(false, ISize)
       TBool
       TFloat(F32)
       TFloat(F64)
       TChar
       TString |]

type internal NormalConstraint =
    { Expect: Type
      Actual: Type
      Span: Span }

type internal Constraint =
    | CNormal of NormalConstraint
    | CDeref of NormalConstraint

type internal FnScope = { Ret: Type }
type internal ClosureScope = { Closure: Closure; Ret: Type }

type internal ScopeData =
    | FnScope of FnScope
    | ClosureScope of ClosureScope
    | BlockScope
    | TypeScope
    | TopLevelScope

type internal VarInfo = { Def: Id; Mut: bool; Static: bool }

type internal Scope =
    { Id: int
      Ty: Dictionary<string, Type>
      Var: Dictionary<string, VarInfo>
      Field: MultiMap<string, Id>
      Constr: ResizeArray<Constraint>
      Data: ScopeData
      mutable VarId: int }

    member this.NewTVar sym span =
        let tvar =
            { Scope = this.Id
              Id = this.VarId
              Sym = sym
              Span = span }

        this.VarId <- this.VarId + 1

        tvar

    static member Create id data =
        { Id = id
          Ty = Dictionary()
          Var = Dictionary()
          Field = MultiMap()
          Constr = ResizeArray()
          Data = data
          VarId = 0 }

    static member Prelude =
        let scope = Scope.Create 0 TopLevelScope

        for p in primitive do
            scope.Ty[p.ToString] <- p

        scope

type internal ActiveScope =
    { Scope: Scope[] }

    member this.WithNew s =
        { Scope = Array.append this.Scope [| s |] }

    member this.Current = Array.last this.Scope

    member this.Pick picker = tryPickBack picker this.Scope

    member this.ResolveTy(id: Id) =
        let pickId scope =
            if scope.Ty.ContainsKey id.Sym then
                let id = scope.Ty[id.Sym]
                Some id
            else
                None

        this.Pick pickId

    member this.ResolveVar(id: Id) =
        let pickId scope =
            if scope.Var.ContainsKey id.Sym then
                let id = scope.Var[id.Sym]
                Some id
            else
                None

        this.Pick pickId

// union find set
type internal TyUnion() =
    let rel = Dictionary<Var, Type>()

    member _.Add k p = rel[k] <- p

    member this.Find k =
        if rel.ContainsKey k then
            let p = rel[k]

            match p with
            | TVar v ->
                let p = this.Find v
                rel[k] <- p
                p
            | p -> p
        else
            TVar k

    member this.Resolve ty =
        let onvar tvar =
            if rel.ContainsKey tvar then
                let p = this.Resolve rel[tvar]
                rel[tvar] <- p
                p
            else
                TVar tvar

        ty.Walk onvar

    member this.TryFind k =
        if rel.ContainsKey k then Some(this.Find k) else None

type internal LetPat = { Mut: bool; Static: bool }

type internal PatMode =
    | ParamPat
    | CondPat
    | LetPat of LetPat

type internal Checker(moduleMap: Dictionary<string, ModuleType>) =
    let mutable scopeId = 0

    let bindingRec = Dictionary(HashIdentity.Reference)
    let structRec: Dictionary<Id, Struct> = Dictionary(HashIdentity.Reference)
    let enumRec = Dictionary(HashIdentity.Reference)
    let captureRec = MultiMap(HashIdentity.Reference)

    let union = TyUnion()
    let error = ResizeArray<Error>()

    let newScope scopeData =
        scopeId <- scopeId + 1
        Scope.Create scopeId scopeData

    member this.Type (scope: ActiveScope) ty =
        let resolve id =
            match scope.ResolveTy id with
            | Some ty -> ty
            | None ->
                error.Add(Undefined id)
                TNever

        match ty with
        | NeverType _ -> TNever
        | IdType i -> resolve i
        | PathType p ->
            if p.Prefix <> None || p.Seg.Length > 1 then
                failwith "Not Implemented"

            let id, ty = p.Seg[0]

            let instType = Array.map (this.Type scope) ty

            let container = resolve id

            match container with
            | TStruct(id, gen) when gen.Length = instType.Length -> TStruct(id, instType)
            | TEnum(id, gen) when gen.Length = instType.Length -> TEnum(id, instType)
            | _ ->
                error.Add(GenericMismatch(container, instType, p.Span))

                TNever
        | TupleType t -> TTuple(Array.map (this.Type scope) t.Ele)
        | RefType r -> TRef(this.Type scope r.Ty)
        | InferedType span ->
            let newTVar = scope.Current.NewTVar None span

            TVar newTVar
        | LitType _ -> failwith "Not Implemented"
        | ArrayType _ -> failwith "Not Implemented"
        | FnType _ -> failwith "Not Implemented"
        | NegType(_) -> failwith "Not Implemented"

    member _.Pat (scope: ActiveScope) mode pat ty =
        let mut, mayShadow, isCond, static_ =
            match mode with
            | LetPat { Mut = mut; Static = static_ } -> mut, not static_, false, static_
            | ParamPat -> true, false, false, false
            | CondPat -> true, true, true, false

        let addSym sym (i: Id) (ty: Type) =
            if Map.containsKey i.Sym sym then
                error.Add(DuplicateDefinition i)

            Map.add i.Sym (i, ty) sym

        let currScope = scope.Current

        let rec proc sym ty pat =
            match pat with
            | IdPat i -> addSym sym i ty
            | LitPat l ->
                if not isCond then
                    error.Add(RefutablePat l.Span)

                let litTy =
                    match l.Value with
                    | Int _ -> TInt(true, ISize)
                    | Bool _ -> TBool
                    | Char _ -> TChar
                    | Float _ -> TFloat F64
                    | String _ -> failwith "Not Implemented"

                currScope.Constr.Add(
                    CNormal
                        { Actual = litTy
                          Expect = ty
                          Span = l.Span }
                )

                sym
            | RangePat { Span = span } -> failwith "Not Implemented"
            | CatchAllPat _ -> sym
            | TuplePat t ->
                let addBinding (pat: Pat) =
                    let sym = pat.Name
                    let newVar = currScope.NewTVar sym pat.Span |> TVar

                    newVar

                let patTy = t.Ele |> Array.map addBinding

                currScope.Constr.Add(
                    CNormal
                        { Actual = TTuple patTy
                          Expect = ty
                          Span = t.Span }
                )

                Array.fold2 proc sym patTy t.Ele
            | AsPat a ->
                let sym = addSym sym a.Id ty

                proc sym ty a.Pat
            | OrPat { Pat = pat; Span = span } ->
                if not isCond then
                    error.Add(RefutablePat span)

                let allSym = Array.map (proc Map.empty ty) pat

                let first = allSym[0]

                for (idx, sym) in Array.indexed allSym do
                    if idx > 0 then
                        let firstKey = first |> Map.keys |> Array.ofSeq
                        let currKey = sym |> Map.keys |> Array.ofSeq

                        if firstKey <> currKey then
                            error.Add(OrPatDifferent(pat[idx].Span, firstKey, currKey))

                        for key in firstKey do
                            let firstTy = snd first[key]
                            let id, currTy = sym[key]

                            currScope.Constr.Add(
                                CNormal
                                    { Expect = firstTy
                                      Actual = currTy
                                      Span = id.Span }
                            )

                let mergeSym sym curr =
                    Map.fold (fun sym _ (id, ty) -> addSym sym id ty) sym curr

                Array.fold mergeSym sym allSym
            | ArrayPat(_) -> failwith "Not Implemented"
            | PathPat(_) -> failwith "Not Implemented"
            | EnumPat e ->
                if e.Variant.Prefix <> None || e.Variant.Seg.Length <> 2 then
                    failwith "Not Implemented"

                if not isCond then
                    error.Add(RefutablePat e.Span)

                let enumId = e.Variant.Seg[0]
                let variant = e.Variant.Seg[1]

                let enumTy =
                    match scope.ResolveTy enumId with
                    | Some ty -> ty
                    | None ->
                        error.Add(Undefined enumId)
                        TNever

                let payloadTy =
                    match enumTy with
                    | TEnum(enum, v) ->
                        let enumData = enumRec[enum]
                        let inst = Array.map (fun _ -> TVar(currScope.NewTVar None e.Span)) v

                        if enumData.Variant.ContainsKey variant.Sym then
                            currScope.Constr.Add(
                                CNormal
                                    { Expect = TEnum(enum, inst)
                                      Actual = ty
                                      Span = e.Span }
                            )

                            let payload = enumData.Variant[variant.Sym]

                            if payload.Length <> e.Payload.Length then
                                error.Add(PayloadMismatch(e.Span, enumData))

                            let getTy idx _ =
                                if idx < payload.Length then
                                    payload[idx].Instantiate enumData.TVar inst
                                else
                                    TNever

                            Array.mapi getTy e.Payload
                        else
                            error.Add(UndefinedVariant(enumId, variant))

                            Array.map (fun _ -> TNever) e.Payload

                    | ty ->
                        error.Add(ExpectEnum(enumId, ty))

                        Array.map (fun _ -> TNever) e.Payload

                Array.fold2 proc sym payloadTy e.Payload
            | StructPat(_) -> failwith "Not Implemented"
            | SelfPat(_) -> failwith "Not Implemented"
            | RefSelfPat(_) -> failwith "Not Implemented"

        let map = proc Map.empty ty pat

        for (id, ty) in map.Values do
            if not mayShadow && currScope.Var.ContainsKey id.Sym then
                error.Add(DuplicateDefinition id)

            currScope.Var[id.Sym] <-
                { Def = id
                  Mut = mut
                  Static = static_ }

            bindingRec[id] <- ty

    member this.Expr (scope: ActiveScope) e =
        let currScope = scope.Current

        match e with
        | Id id ->
            let rec resolveVar captured canCapture i =
                let curr = scope.Scope[i]

                if curr.Var.ContainsKey id.Sym then
                    let info = curr.Var[id.Sym]

                    let captured =
                        if canCapture && not info.Static then
                            captured
                        else
                            if not info.Static then
                                error.Add(CaptureDynamic id)

                            [||]

                    Some(info, captured)
                else if i = 0 then
                    None
                else
                    let captured =
                        match curr.Data with
                        | ClosureScope { Closure = cl } -> Array.append captured [| cl |]
                        | _ -> captured

                    let canCapture =
                        match curr.Data with
                        | FnScope _ -> false
                        | _ -> canCapture

                    resolveVar captured canCapture (i - 1)

            match resolveVar [||] true (scope.Scope.Length - 1) with
            | None ->
                error.Add(Undefined id)
                TNever
            | Some({ Def = def }, captured) ->
                for c in captured do
                    captureRec.Add c def

                match bindingRec[def] with
                | TFn f ->
                    let newTVar = Array.map (fun _ -> currScope.NewTVar None id.Span) f.TVar
                    TFn(f.Instantiate newTVar)
                | t -> t

        | Binary b ->
            let l = this.Expr scope b.Left
            let r = this.Expr scope b.Right

            match b.Op with
            | Arith _ ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TInt(true, ISize)
                          Actual = l
                          Span = b.Left.Span }
                )

                currScope.Constr.Add(
                    CNormal
                        { Expect = TInt(true, ISize)
                          Actual = r
                          Span = b.Right.Span }
                )

                TInt(true, ISize)

            | Logic _ ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TBool
                          Actual = l
                          Span = b.Left.Span }
                )

                currScope.Constr.Add(
                    CNormal
                        { Expect = TBool
                          Actual = r
                          Span = b.Right.Span }
                )

                TBool

            | Cmp _ ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = l
                          Actual = r
                          Span = b.Span }
                )

                TBool
            | Pipe -> failwith "Not Implemented"

        | SelfExpr(_) -> failwith "Not Implemented"
        | LitExpr l ->
            match l.Value with
            | Int _ -> TInt(true, ISize)
            | Bool _ -> TBool
            | Char _ -> TChar
            | Float _ -> TFloat F64
            | String _ -> failwith "Not Implemented"

        | If i ->
            let then_ = this.Cond scope i.Cond i.Then

            for br in i.ElseIf do
                let elseif = this.Cond scope br.Cond br.Block

                currScope.Constr.Add(
                    CNormal
                        { Expect = then_
                          Actual = elseif
                          Span = i.Span }
                )

            match i.Else with
            | Some else_ ->
                let else_ = this.Block scope else_

                currScope.Constr.Add(
                    CNormal
                        { Expect = then_
                          Actual = else_
                          Span = i.Span }
                )
            | None ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = then_
                          Actual = UnitType
                          Span = i.Span }
                )

            then_
        | Match m ->
            let value = this.Expr scope m.Value

            let typeOfBranch (br: MatchBranch) =
                let newScope = newScope BlockScope
                let scope = scope.WithNew newScope

                this.Pat scope CondPat br.Pat value

                match br.Guard with
                | Some g ->
                    newScope.Constr.Add(
                        CNormal
                            { Actual = this.Expr scope g
                              Expect = TBool
                              Span = g.Span }
                    )
                | None -> ()

                let brTy = this.Expr scope br.Expr

                this.Unify newScope

                union.Resolve brTy

            if Array.length m.Branch = 0 then
                UnitType
            else
                let first = typeOfBranch m.Branch[0]

                for br in m.Branch[1..] do
                    let brTy = typeOfBranch br

                    currScope.Constr.Add(
                        CNormal
                            { Expect = first
                              Actual = brTy
                              Span = br.Span }
                    )

                first

        | Block b -> this.Block scope b
        | Call c ->
            let callee = this.Expr scope c.Callee

            let arg = Array.map (this.Expr scope) c.Arg
            let ret = TVar(currScope.NewTVar None c.Span)

            currScope.Constr.Add(
                CNormal
                    { Expect = TFn { Param = arg; Ret = ret; TVar = [||] }
                      Actual = callee
                      Span = c.Span }
            )

            ret
        | As _ -> failwith "Not Implemented"
        | Unary u ->
            match u.Op with
            | Not ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TBool
                          Actual = this.Expr scope u.Value
                          Span = u.Span }
                )

                TBool
            | Neg ->
                currScope.Constr.Add(
                    CNormal
                        { Expect = TInt(true, ISize)
                          Actual = this.Expr scope u.Value
                          Span = u.Span }
                )

                TInt(true, ISize)
            | Ref ->
                let rec getVar expr =
                    match expr with
                    | Id i -> Some i
                    | Field { Receiver = receiver } -> getVar receiver
                    | Index { Container = container } -> getVar container
                    | Unary { Op = Deref; Value = expr } -> getVar expr
                    | _ -> None

                TRef(this.Expr scope u.Value)
            | Deref ->
                let sym =
                    match u.Value with
                    | Id i -> Some i.Sym
                    | _ -> None

                let ptr = TVar(currScope.NewTVar sym u.Value.Span)

                currScope.Constr.Add(
                    CNormal
                        { Expect = TRef ptr
                          Actual = this.Expr scope u.Value
                          Span = u.Span }
                )

                ptr
        | Assign a ->
            let value = this.Expr scope a.Value
            let place = this.Expr scope a.Place

            currScope.Constr.Add(
                CNormal
                    { Expect = place
                      Actual = value
                      Span = a.Span }
            )

            let rec getVar expr =
                match expr with
                | Id i -> Some i
                | Field { Receiver = receiver } -> getVar receiver
                | Index { Container = container } -> getVar container
                | Unary { Op = Deref; Value = expr } -> getVar expr
                | _ -> None

            match getVar a.Place with
            | None -> ()
            | Some id ->
                match scope.ResolveVar id with
                | None -> ()
                | Some(info) ->
                    if not info.Mut then
                        error.Add(AssignImmutable(info.Def, a.Span))

            UnitType
        | Field f ->
            let receiver = this.Expr scope f.Receiver
            let key = f.Field.Sym

            match receiver with
            | TStruct(i, inst) ->
                let stru = structRec[i]

                match Map.tryFind key stru.Field with
                | Some f -> f.Instantiate stru.TVar inst
                | None ->
                    error.Add(UndefinedField(f.Span, key))

                    TNever
            | _ ->
                let findStruct scope =
                    match scope.Field.Get key with
                    | None -> None
                    | Some id -> Some structRec[id]

                let stru = scope.Pick findStruct

                match stru with
                | Some s ->
                    let inst = Array.map (fun _ -> TVar(currScope.NewTVar None f.Span)) s.TVar

                    currScope.Constr.Add(
                        CDeref
                            { Expect = TStruct(s.Name, inst)
                              Actual = receiver
                              Span = f.Span }
                    )

                    s.Field[key].Instantiate s.TVar inst
                | None ->
                    error.Add(UndefinedField(f.Span, key))
                    TNever

        | TupleAccess(_) -> failwith "Not Implemented"
        | Index(_) -> failwith "Not Implemented"
        | Array(_) -> failwith "Not Implemented"
        | ArrayRepeat(_) -> failwith "Not Implemented"
        | StructLit(_) -> failwith "Not Implemented"
        | Tuple s -> s.Ele |> Array.map (this.Expr scope) |> TTuple
        | Closure c ->
            let paramTy (p: Param) =
                match p.Ty with
                | Some ty -> this.Type scope ty
                | None ->
                    let sym = p.Pat.Name
                    let newTVar = currScope.NewTVar sym p.Span

                    TVar newTVar

            let paramTy = Array.map paramTy c.Param

            let retTy =
                match c.Ret with
                | Some ty -> this.Type scope ty
                | None -> TVar(currScope.NewTVar None c.Span)

            let closureScope = newScope (ClosureScope { Closure = c; Ret = retTy })

            let scope = scope.WithNew closureScope

            for (param, ty) in Array.zip c.Param paramTy do
                this.Pat scope ParamPat param.Pat ty

            let ret = this.Expr scope c.Body

            closureScope.Constr.Add(
                CNormal
                    { Expect = retTy
                      Actual = ret
                      Span = c.Span }
            )

            this.Unify closureScope

            let resolve ty = union.Resolve ty

            TFn
                { Param = Array.map resolve paramTy
                  Ret = resolve retTy
                  TVar = [||] }

        | Path p ->
            if p.Prefix <> None || p.Seg.Length <> 2 then
                failwith "Not Implemented"

            let enumId, _ = p.Seg[0]
            let variant, _ = p.Seg[1]

            let enumTy =
                match scope.ResolveTy enumId with
                | Some ty -> ty
                | None ->
                    error.Add(Undefined enumId)
                    TNever

            match enumTy with
            | TEnum(enum, _) ->
                let enumData = enumRec[enum]
                let inst = Array.map (fun _ -> TVar(currScope.NewTVar None e.Span)) enumData.TVar

                if enumData.Variant.ContainsKey variant.Sym then
                    let payload = enumData.Variant[variant.Sym]

                    if payload.Length = 0 then
                        TEnum(enum, inst)
                    else
                        let payload = Array.map (fun (t: Type) -> t.Instantiate enumData.TVar inst) payload

                        TFn
                            { Param = payload
                              Ret = TEnum(enum, inst)
                              TVar = [||] }
                else
                    error.Add(UndefinedVariant(enumId, variant))

                    TNever

            | ty ->
                error.Add(ExpectEnum(enumId, ty))

                TNever

        | Break _ -> TNever
        | Continue _ -> TNever
        | Return r ->
            let pickFn scope =
                match scope.Data with
                | FnScope f -> Some f
                | _ -> None

            let retTy =
                match scope.Pick pickFn with
                | Some { Ret = retTy } -> retTy
                | None -> failwith "Unreachable"

            let ty =
                match r.Value with
                | Some v -> this.Expr scope v
                | None -> UnitType

            currScope.Constr.Add(
                CNormal
                    { Expect = retTy
                      Actual = ty
                      Span = r.Span }
            )

            TNever
        | Range(_) -> failwith "Not Implemented"
        | For(_) -> TNever
        | While w ->
            let _ = this.Cond scope w.Cond w.Body

            TNever
        | TryReturn(_) -> failwith "Not Implemented"

    member this.Block (scope: ActiveScope) (b: Block) =
        let blockScope = newScope BlockScope

        let scope = scope.WithNew blockScope

        let chooseDecl s =
            match s with
            | DeclStmt d -> Some d
            | ExprStmt _ -> None

        let decl = Seq.choose chooseDecl b.Stmt

        this.HoistDecl scope decl

        let typeof _ stmt =
            match stmt with
            | DeclStmt d ->
                this.Decl scope d

                UnitType
            | ExprStmt e -> this.Expr scope e

        let ty = Array.fold typeof UnitType b.Stmt

        this.Unify blockScope

        union.Resolve ty

    member this.HoistDecl (scope: ActiveScope) (decl: seq<Decl>) =
        let currScope = scope.Current

        let topLevel =
            match currScope.Data with
            | TopLevelScope -> true
            | _ -> false

        // Process Type Decl Hoisted Name
        for d in decl do
            let dummyTVar _ =
                TVar
                    { Scope = 0
                      Id = 0
                      Sym = None
                      Span = Span.dummy }

            match d with
            | Let _
            | Const _
            | FnDecl _ -> ()
            | StructDecl s ->
                if currScope.Ty.ContainsKey s.Name.Sym then
                    error.Add(DuplicateDefinition s.Name)

                let tvar = Array.map dummyTVar s.TyParam
                currScope.Ty[s.Name.Sym] <- TStruct(s.Name, tvar)

                for field in s.Field do
                    currScope.Field.Add field.Name.Sym s.Name

            | EnumDecl e ->
                if currScope.Ty.ContainsKey e.Name.Sym then
                    error.Add(DuplicateDefinition e.Name)

                let tvar = Array.map dummyTVar e.TyParam
                currScope.Ty[e.Name.Sym] <- TEnum(e.Name, tvar)
            | TypeDecl t ->
                if currScope.Ty.ContainsKey t.Name.Sym then
                    error.Add(DuplicateDefinition t.Name)

                currScope.Ty[t.Name.Sym] <- TNever
            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        let staticItem = ResizeArray()

        // Process Type Decl
        for d in decl do
            match d with
            | Let _ ->
                if topLevel then
                    staticItem.Add d
            | Const _ -> ()
            | FnDecl _ -> staticItem.Add d
            | StructDecl s ->
                let scope, tvar =
                    if s.TyParam.Length > 0 then
                        let newScope = newScope TypeScope

                        let processParam (param: TyParam) =
                            let newTVar = newScope.NewTVar (Some param.Id.Sym) param.Id.Span

                            newScope.Ty[param.Id.Sym] <- TVar newTVar

                            newTVar

                        scope.WithNew newScope, Array.map processParam s.TyParam
                    else
                        scope, [||]

                let processField m (field: StructFieldDef) =
                    let name = field.Name.Sym

                    if Map.containsKey name m then
                        error.Add(DuplicateField field.Name)

                    Map.add name (this.Type scope field.Ty) m

                let field = Array.fold processField Map.empty s.Field

                let stru =
                    { Name = s.Name
                      Field = field
                      TVar = tvar }

                structRec[s.Name] <- stru

            | EnumDecl e ->
                let scope, tvar =
                    if e.TyParam.Length > 0 then
                        let newScope = newScope TypeScope

                        let processParam (param: TyParam) =
                            let newTVar = newScope.NewTVar (Some param.Id.Sym) param.Id.Span

                            newScope.Ty[param.Id.Sym] <- TVar newTVar

                            newTVar

                        scope.WithNew newScope, Array.map processParam e.TyParam
                    else
                        scope, [||]

                let processVariant m (variant: EnumVariantDef) =
                    let name = variant.Name.Sym

                    if Map.containsKey name m then
                        error.Add(DuplicateVariant variant.Name)

                    let payload = Array.map (this.Type scope) variant.Payload

                    Map.add name payload m

                let variant = Array.fold processVariant Map.empty e.Variant

                let enum =
                    { Name = e.Name
                      Variant = variant
                      TVar = tvar }

                enumRec[e.Name] <- enum

            | TypeDecl t -> currScope.Ty[t.Name.Sym] <- this.Type scope t.Ty

            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        let valueMap = Dictionary()
        let scopeMap = Dictionary()

        for item in staticItem do
            match item with
            | FnDecl f ->
                if currScope.Var.ContainsKey f.Name.Sym then
                    error.Add(DuplicateDefinition f.Name)

                currScope.Var[f.Name.Sym] <-
                    { Def = f.Name
                      Mut = false
                      Static = true }

                let newScope = newScope TypeScope

                let tvar =
                    let processParam (param: TyParam) =
                        let newTVar = newScope.NewTVar (Some param.Id.Sym) param.Id.Span

                        newScope.Ty.Add(param.Id.Sym, TVar newTVar)

                        newTVar

                    Array.map processParam f.TyParam

                let scope = scope.WithNew newScope

                let paramTy (p: Param) =
                    match p.Ty with
                    | Some ty -> this.Type scope ty
                    | None ->
                        let sym = p.Pat.Name
                        let newTVar = newScope.NewTVar sym p.Span

                        TVar newTVar

                let param = Array.map paramTy f.Param

                let ret =
                    match f.Ret with
                    | Some ty -> this.Type scope ty
                    | None -> TVar(newScope.NewTVar None f.Span)

                let newScope =
                    { newScope with
                        Data = FnScope { Ret = ret } }

                scopeMap.Add(f, newScope)

                let fnTy =
                    TFn
                        { Param = param
                          Ret = ret
                          TVar = tvar }

                bindingRec[f.Name] <- fnTy

            | Let l ->
                let ty =
                    match l.Ty with
                    | Some ty -> this.Type scope ty
                    | None ->
                        let sym = l.Pat.Name
                        let newTVar = currScope.NewTVar sym l.Span

                        TVar newTVar

                valueMap.Add(l.Pat, ty)
                this.Pat scope (LetPat { Mut = l.Mut; Static = true }) l.Pat ty
            | _ -> ()

        for item in staticItem do
            match item with
            | FnDecl f ->
                let newScope = scope.WithNew scopeMap[f]
                this.Fn newScope f
            | Let l ->
                let value = this.Expr scope l.Value

                currScope.Constr.Add(
                    CNormal
                        { Expect = valueMap[l.Pat]
                          Actual = value
                          Span = l.Span }
                )
            | _ -> ()

    member this.Decl (scope: ActiveScope) d =
        match d with
        | Let l ->
            let value = this.Expr scope l.Value

            let ty =
                match l.Ty with
                | Some ty ->
                    let ty = this.Type scope ty

                    scope.Current.Constr.Add(
                        CNormal
                            { Expect = ty
                              Actual = value
                              Span = l.Span }
                    )

                    ty
                | None -> value

            this.Pat scope (LetPat { Mut = l.Mut; Static = false }) l.Pat ty

        | Const _ -> failwith "Not Implemented"
        | Use _ -> failwith "Not Implemented"
        | FnDecl _
        | StructDecl _
        | EnumDecl _
        | TypeDecl _
        | Trait _
        | Impl _ -> ()

    member this.Cond (scope: ActiveScope) cond block =
        let currScope = scope.Current

        match cond with
        | BoolCond b ->
            currScope.Constr.Add(
                CNormal
                    { Expect = TBool
                      Actual = this.Expr scope b
                      Span = b.Span }
            )

            this.Block scope block
        | LetCond c ->
            let value = this.Expr scope c.Value
            let newScope = newScope BlockScope
            let scope = scope.WithNew newScope

            this.Pat scope CondPat c.Pat value

            let ty = this.Block scope block

            this.Unify newScope

            union.Resolve ty

    member this.Fn (scope: ActiveScope) (f: Fn) =
        let fnTy =
            match bindingRec[f.Name] with
            | TFn f -> f
            | _ -> failwith "Unreachable"

        let currScope = scope.Current

        for (param, ty) in Array.zip f.Param fnTy.Param do
            this.Pat scope ParamPat param.Pat ty

        let lastScope = scopeId

        let ret = this.Block scope f.Body

        currScope.Constr.Add(
            CNormal
                { Expect = fnTy.Ret
                  Actual = ret
                  Span = f.Name.Span }
        )

        this.Unify currScope

        let param = Array.map union.Resolve fnTy.Param

        let inScope (v: Var) =
            v.Scope = currScope.Id || v.Scope > lastScope

        let tvar =
            param
            |> Seq.map _.FindTVar
            |> Seq.concat
            |> Seq.filter inScope
            |> Seq.append fnTy.TVar
            |> Seq.distinct
            |> Array.ofSeq

        let toNever t =
            if inScope t && not (Array.contains t tvar) then
                TNever
            else
                TVar t

        let ret = union.Resolve fnTy.Ret
        let ret = ret.Walk toNever

        let fnTy =
            { TVar = tvar
              Param = param
              Ret = ret }

        bindingRec[f.Name] <- TFn fnTy

    member _.Unify scope =
        let rec unifyNormal c deref =
            let addUnion v ty =
                match union.TryFind v with
                | None -> union.Add v ty
                | Some prev ->
                    unifyNormal
                        { Expect = ty
                          Actual = prev
                          Span = c.Span }
                        deref

                    union.Add v (union.Resolve prev)

            match c.Expect, c.Actual with
            | p1, p2 when p1 = p2 -> ()
            | TVar v1 as t1, (TVar v2 as t2) ->
                if v1.Scope > v2.Scope then
                    addUnion v1 t2
                else if v1.Scope = v2.Scope then
                    if v1.Id > v2.Id then addUnion v1 t2 else addUnion v2 t1
                else
                    addUnion v2 t1
            | TVar v, ty
            | ty, TVar v ->
                match ty.FindTVar |> Seq.tryFind ((=) v) with
                | Some _ -> error.Add(FailToUnify(c.Expect, c.Actual, c.Span))
                | None -> addUnion v ty

            | TFn f1, TFn f2 ->
                if f1.Param.Length <> f2.Param.Length then
                    error.Add(TypeMismatch(c.Expect, c.Actual, c.Span))
                else
                    for (p1, p2) in (Array.zip f1.Param f2.Param) do
                        unifyNormal
                            { Expect = p1
                              Actual = p2
                              Span = c.Span }
                            deref

                    unifyNormal
                        { Expect = f1.Ret
                          Actual = f2.Ret
                          Span = c.Span }
                        false

            | TRef r1, TRef r2 ->
                unifyNormal
                    { Expect = r1
                      Actual = r2
                      Span = c.Span }
                    false

            | TRef r, t
            | t, TRef r when deref ->
                unifyNormal
                    { Expect = r.StripRef
                      Actual = t
                      Span = c.Span }
                    false

            | TNever, _
            | _, TNever -> ()
            | TStruct(id1, v1), TStruct(id2, v2)
            | TEnum(id1, v1), TEnum(id2, v2) when id1 = id2 ->
                for (v1, v2) in Array.zip v1 v2 do
                    unifyNormal
                        { Expect = v1
                          Actual = v2
                          Span = c.Span }
                        false

            | TTuple t1, TTuple t2 ->
                if t1.Length <> t2.Length then
                    error.Add(TupleLengthMismatch(c.Span, t1.Length, t2.Length))
                else
                    for (t1, t2) in Array.zip t1 t2 do
                        unifyNormal
                            { Expect = t1
                              Actual = t2
                              Span = c.Span }
                            false
            | _, _ -> error.Add(TypeMismatch(c.Expect, c.Actual, c.Span))

        for c in scope.Constr do
            match c with
            | CNormal c -> unifyNormal c false
            | CDeref c -> unifyNormal c true

    member this.Module(m: Module) =
        let topLevel = newScope TopLevelScope
        let scope = { Scope = [| Scope.Prelude; topLevel |] }

        let decl = m.Item |> Array.map _.Decl

        this.HoistDecl scope decl

        this.Unify topLevel

        for id in bindingRec.Keys do
            let oldTy = bindingRec[id]
            bindingRec[id] <- union.Resolve oldTy

        let sema =
            { Binding = dictToMap bindingRec
              Struct = dictToMap structRec
              Enum = dictToMap enumRec
              Capture = captureRec.ToMap
              Module =
                { Ty = Map.empty
                  Var = Map.empty
                  Module = Map.empty } }

        sema, error.ToArray()

let check (moduleMap: Dictionary<string, ModuleType>) (m: Module) =
    let checker = Checker moduleMap

    checker.Module m
