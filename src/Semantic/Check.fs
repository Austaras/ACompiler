module Semantic.Check

open System.Collections.Generic

// TODO: module system
// TODO: type alias
// TODO: trait, operator overloading and type alias
// TODO: pipe and compose operator

open Common.Span
open Util.MultiMap
open AST.AST
open Semantic
open Env

type internal LetPat = { Mut: bool; Static: bool }

type internal PatMode =
    | ParamPat
    | CondPat
    | LetPat of LetPat

type internal Traverse(moduleMap: Dictionary<string, ModuleType>) =
    let bindingRec = Dictionary(HashIdentity.Reference)
    let exprRec = Dictionary(HashIdentity.Reference)
    let structRec: Dictionary<Id, Struct> = Dictionary(HashIdentity.Reference)
    let enumRec = Dictionary(HashIdentity.Reference)
    let captureRec = MultiMap(HashIdentity.Reference)

    let error = ResizeArray<Error>()

    let env = Environment(error)

    member this.Type ty =
        let resolve id =
            match env.GetTy id with
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

            let instType = Array.map this.Type ty

            let container = resolve id

            match container with
            | TStruct(id, gen) when gen.Length = instType.Length -> TStruct(id, instType)
            | TEnum(id, gen) when gen.Length = instType.Length -> TEnum(id, instType)
            | _ ->
                error.Add(GenericMismatch(container, instType, p.Span))

                TNever
        | TupleType t -> TTuple(Array.map this.Type t.Ele)
        | RefType r -> TRef(this.Type r.Ty)
        | InferedType span ->
            let newTVar = env.NewTVar None span

            TVar newTVar
        | ArrayType a ->
            let ele = this.Type a.Ele

            match a.Len with
            | None -> TSlice ele
            | Some(LitType { Value = Int len }) -> TArray(ele, len)
            | Some _ -> failwith "Not Implemented"

        | FnType f ->
            let param = f.Param |> Array.map this.Type
            let ret = this.Type f.Ret

            TFn { Param = param; Ret = ret }

        | LitType _ -> failwith "Not Implemented"
        | NegType _ -> failwith "Not Implemented"

    member _.Pat mode pat ty =
        let mut, mayShadow, isCond, static_ =
            match mode with
            | LetPat { Mut = mut; Static = static_ } -> mut, not static_, false, static_
            | ParamPat -> true, false, false, false
            | CondPat -> true, true, true, false

        let addSym sym (i: Id) (ty: Type) =
            if Map.containsKey i.Sym sym then
                error.Add(DuplicateDefinition i)

            Map.add i.Sym (i, ty) sym

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

                env.Unify litTy ty l.Span

                sym
            | RangePat { Span = span } -> failwith "Not Implemented"
            | CatchAllPat _ -> sym
            | TuplePat t ->
                let addBinding (pat: Pat) =
                    let sym = pat.Name
                    let newVar = env.NewTVar sym pat.Span |> TVar

                    newVar

                let patTy = t.Ele |> Array.map addBinding

                env.Unify (TTuple patTy) ty t.Span

                Array.fold2 proc sym patTy t.Ele
            | AsPat a ->
                let sym = addSym sym a.Id ty

                proc sym ty a.Pat
            | OrPat { Pat = pat; Span = span } ->
                if not isCond then
                    error.Add(RefutablePat span)

                let allSym = Array.map (proc Map.empty ty) pat

                let first = allSym[0]
                let firstKey = first |> Map.keys |> Array.ofSeq

                for (idx, sym) in Array.indexed allSym do
                    if idx > 0 then
                        let currKey = sym |> Map.keys |> Array.ofSeq

                        if firstKey <> currKey then
                            error.Add(OrPatDifferent(pat[idx].Span, firstKey, currKey))

                        for key in firstKey do
                            let firstTy = snd first[key]
                            let id, currTy = sym[key]

                            env.Unify firstTy currTy id.Span

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
                    match env.GetTy enumId with
                    | Some ty -> ty
                    | None ->
                        error.Add(Undefined enumId)
                        TNever

                let payloadTy =
                    match enumTy with
                    | TEnum(enum, v) ->
                        let enumData = enumRec[enum]
                        let inst = Array.map (fun _ -> TVar(env.NewTVar None e.Span)) v

                        if enumData.Variant.ContainsKey variant.Sym then
                            env.Unify (TEnum(enum, inst)) ty e.Span

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
            let info =
                { Def = id
                  Mut = mut
                  Static = static_ }

            env.RegisterVar mayShadow info

            bindingRec[id] <- BTy ty

    member this.Expr e =
        match e with
        | Id id ->
            match env.GetVarInfoWithCapture id with
            | None ->
                error.Add(Undefined id)
                TNever
            | Some(def, captured) ->
                for c in captured do
                    captureRec.Add c def

                match bindingRec[def] with
                | BFn(tvar, fn) -> TFn(env.Instantiate id.Span tvar fn)
                | BTy t -> t

        | Binary b ->
            let l = this.Expr b.Left
            let r = this.Expr b.Right

            match b.Op with
            | Arith _ ->
                env.Unify (TInt(true, ISize)) l b.Left.Span
                env.Unify (TInt(true, ISize)) r b.Right.Span

                TInt(true, ISize)

            | Logic _ ->
                env.Unify TBool l b.Left.Span
                env.Unify TBool r b.Right.Span

                TBool

            | Cmp _ ->
                env.Unify l r b.Span

                TBool
            | Pipe -> failwith "Not Implemented"

        | SelfExpr(_) -> failwith "Not Implemented"
        | LitExpr l ->
            match l.Value with
            | Int _ -> TInt(true, ISize)
            | Bool _ -> TBool
            | Char _ -> TChar
            | Float _ -> TFloat F64
            | String _ -> TString

        | If i ->
            let then_ = this.Cond i.Cond i.Then

            for br in i.ElseIf do
                let elseif = this.Cond br.Cond br.Block

                env.Unify then_ elseif i.Span

            match i.Else with
            | Some else_ ->
                let else_ = this.Block else_

                env.Unify then_ else_ i.Span

            | None -> env.Unify then_ UnitType i.Span

            then_
        | Match m ->
            let value = this.Expr m.Value

            let typeOfBranch (br: MatchBranch) =
                env.EnterScope BlockScope

                this.Pat CondPat br.Pat value

                match br.Guard with
                | Some g -> env.Unify (this.Expr g) TBool g.Span
                | None -> ()

                let brTy = this.Expr br.Expr

                env.FinishScope()

                env.NormalizeTy brTy

            if Array.length m.Branch = 0 then
                UnitType
            else
                let first = typeOfBranch m.Branch[0]

                for br in m.Branch[1..] do
                    let brTy = typeOfBranch br

                    env.Unify first brTy br.Span

                first

        | Block b -> this.Block b
        | Call c ->
            match c.Callee with
            | Field f ->
                let receiver = this.Expr f.Receiver
                let callee = failwith "TODO: method"

                let arg = Array.map this.Expr c.Arg
                let ret = TVar(env.NewTVar None c.Span)

                env.Unify (TFn { Param = arg; Ret = ret }) callee c.Span

                ret
            | _ ->
                let callee = this.Expr c.Callee

                let arg = Array.map this.Expr c.Arg
                let ret = TVar(env.NewTVar None c.Span)

                env.Unify (TFn { Param = arg; Ret = ret }) callee c.Span

                ret
        | As _ -> failwith "Not Implemented"
        | Unary u ->
            let value = this.Expr u.Value

            match u.Op with
            | Not ->
                env.Unify TBool value u.Span

                TBool
            | Neg ->
                env.Unify (TInt(true, ISize)) value u.Span

                TInt(true, ISize)
            | Ref -> TRef value
            | Deref ->
                let sym =
                    match u.Value with
                    | Id i -> Some i.Sym
                    | _ -> None

                let ptr = TVar(env.NewTVar sym u.Value.Span)

                env.Unify (TRef ptr) value u.Span

                ptr
        | Assign a ->
            let value = this.Expr a.Value
            let place = this.Expr a.Place

            env.Unify place value a.Span

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
                match env.GetVarInfo id with
                | None -> error.Add(Undefined id)
                | Some(info) ->
                    if not info.Mut then
                        error.Add(AssignImmutable(info.Def, a.Span))

            UnitType
        | Field f ->
            let receiver = this.Expr f.Receiver
            let key = f.Field.Sym

            match receiver.StripRef() with
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

                let stru = env.Pick findStruct

                match stru with
                | Some s ->
                    let inst = Array.map (fun _ -> TVar(env.NewTVar None f.Span)) s.TVar

                    env.Unify (TStruct(s.Name, inst)) receiver f.Span

                    s.Field[key].Instantiate s.TVar inst
                | None ->
                    error.Add(UndefinedField(f.Span, key))
                    TNever

        | TupleAccess(_) -> failwith "Not Implemented"
        | Index(_) -> failwith "Not Implemented"
        | Array a ->
            if a.Ele.Length = 0 then
                let ele = env.NewTVar None a.Span
                TArray(TVar ele, 0UL)
            else
                let first = this.Expr a.Ele[0]

                for ele in a.Ele[1..] do
                    let ty = this.Expr ele
                    env.Unify first ty ele.Span

                TArray(first, uint64 a.Ele.Length)

        | ArrayRepeat a ->
            // TODO: clone trait
            let ty = this.Expr a.Ele

            match a.Len with
            | LitExpr { Value = Int len } -> TArray(ty, len)
            | _ -> failwith "Not Implemented"

        | StructLit(_) -> failwith "Not Implemented"
        | Tuple s -> s.Ele |> Array.map this.Expr |> TTuple
        | Closure c ->
            env.EnterScope TypeScope

            let paramTy (p: Param) =
                match p.Ty with
                | Some ty -> this.Type ty
                | None ->
                    let sym = p.Pat.Name
                    let newTVar = env.NewTVar sym p.Span

                    TVar newTVar

            let paramTy = Array.map paramTy c.Param

            let retTy =
                match c.Ret with
                | Some ty -> this.Type ty
                | None -> TVar(env.NewTVar None c.Span)

            env.ExitScope()

            let closureScope = ClosureScope { Closure = c; Ret = retTy }

            env.EnterScope closureScope

            for (param, ty) in Array.zip c.Param paramTy do
                this.Pat ParamPat param.Pat ty

            let ret = this.Expr c.Body

            env.Unify retTy ret c.Span

            env.FinishScope()

            let resolve ty = env.NormalizeTy ty

            TFn
                { Param = Array.map resolve paramTy
                  Ret = resolve retTy }

        | Path p ->
            if p.Prefix <> None || p.Seg.Length <> 2 then
                failwith "Not Implemented"

            let enumId, _ = p.Seg[0]
            let variant, _ = p.Seg[1]

            let enumTy =
                match env.GetTy enumId with
                | Some ty -> ty
                | None ->
                    error.Add(Undefined enumId)
                    TNever

            match enumTy with
            | TEnum(enum, _) ->
                let enumData = enumRec[enum]
                let inst = Array.map (fun _ -> TVar(env.NewTVar None e.Span)) enumData.TVar

                if enumData.Variant.ContainsKey variant.Sym then
                    let payload = enumData.Variant[variant.Sym]

                    if payload.Length = 0 then
                        TEnum(enum, inst)
                    else
                        let payload = Array.map (fun (t: Type) -> t.Instantiate enumData.TVar inst) payload

                        TFn
                            { Param = payload
                              Ret = TEnum(enum, inst) }
                else
                    error.Add(UndefinedVariant(enumId, variant))

                    TNever

            | ty ->
                error.Add(ExpectEnum(enumId, ty))

                TNever

        | Break _ -> TNever
        | Continue _ -> TNever
        | Return r ->
            let pickRet scope =
                match scope.Data with
                | FnScope { Ret = r }
                | ClosureScope { Ret = r } -> Some r
                | _ -> None

            let retTy =
                match env.Pick pickRet with
                | Some r -> r
                | None -> failwith "Unreachable"

            let ty =
                match r.Value with
                | Some v -> this.Expr v
                | None -> UnitType

            env.Unify retTy ty r.Span

            TNever
        | Range(_) -> failwith "Not Implemented"
        | For(_) -> TNever
        | While w ->
            let _ = this.Cond w.Cond w.Body

            TNever
        | TryReturn(_) -> failwith "Not Implemented"

    member this.Block(b: Block) =
        env.EnterScope BlockScope

        let chooseDecl s =
            match s with
            | DeclStmt d -> Some d
            | ExprStmt _ -> None

        let decl = Seq.choose chooseDecl b.Stmt

        this.HoistDecl decl false

        let typeof _ stmt =
            match stmt with
            | DeclStmt d ->
                this.Decl d

                UnitType
            | ExprStmt e -> this.Expr e

        let ty = Array.fold typeof UnitType b.Stmt

        env.FinishScope()

        env.NormalizeTy ty

    member _.TyParam(p: TyParam[]) =
        let proc (p: TyParam) =
            let newTVar = env.NewTVar (Some p.Id.Sym) p.Id.Span
            env.RegisterTy p.Id (TVar newTVar)
            newTVar

        let res = Array.map proc p

        res

    member this.HoistDecl (decl: seq<Decl>) topLevel =
        // Process Type Decl Hoisted Name
        for d in decl do
            let dummyTVar _ =
                TVar
                    { Level = 0
                      Id = 0
                      Sym = None
                      Span = Span.dummy }

            match d with
            | Let _
            | Const _
            | FnDecl _ -> ()
            | StructDecl s ->
                let tvar = Array.map dummyTVar s.TyParam
                env.RegisterTy s.Name (TStruct(s.Name, tvar))
                env.RegisterField s

            | EnumDecl e ->
                let tvar = Array.map dummyTVar e.TyParam
                env.RegisterTy e.Name (TEnum(e.Name, tvar))

            | TypeDecl _ -> failwith "Not Implemented"
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
                env.EnterScope TypeScope
                let tvar = this.TyParam s.TyParam

                let processField m (field: StructFieldDef) =
                    let name = field.Name.Sym

                    if Map.containsKey name m then
                        error.Add(DuplicateField field.Name)

                    Map.add name (this.Type field.Ty) m

                let field = Array.fold processField Map.empty s.Field

                env.ExitScope()

                let stru =
                    { Name = s.Name
                      Field = field
                      TVar = tvar }

                structRec[s.Name] <- stru

            | EnumDecl e ->
                env.EnterScope TypeScope
                let tvar = this.TyParam e.TyParam

                let processVariant m (variant: EnumVariantDef) =
                    let name = variant.Name.Sym

                    if Map.containsKey name m then
                        error.Add(DuplicateVariant variant.Name)

                    let payload = Array.map this.Type variant.Payload

                    Map.add name payload m

                let variant = Array.fold processVariant Map.empty e.Variant

                let enum =
                    { Name = e.Name
                      Variant = variant
                      TVar = tvar }

                env.ExitScope()

                enumRec[e.Name] <- enum

            | TypeDecl _ -> failwith "Not Implemented"
            | Use _ -> failwith "Not Implemented"
            | Trait _ -> failwith "Not Implemented"
            | Impl _ -> failwith "Not Implemented"

        let valueMap = Dictionary()

        for item in staticItem do
            match item with
            | FnDecl f ->
                let info =
                    { Def = f.Name
                      Mut = false
                      Static = true }

                env.RegisterVar false info

                env.EnterScope TypeScope

                let tvar = this.TyParam f.TyParam

                let paramTy (p: Param) =
                    match p.Ty with
                    | Some ty -> this.Type ty
                    | None ->
                        let sym = p.Pat.Name
                        let newTVar = env.NewTVar sym p.Span

                        TVar newTVar

                let param = Array.map paramTy f.Param

                let ret =
                    match f.Ret with
                    | Some ty -> this.Type ty
                    | None -> TVar(env.NewTVar None f.Span)

                env.ExitScope()

                let fnTy = { Param = param; Ret = ret }

                bindingRec[f.Name] <- BFn(tvar, fnTy)

            | Let l ->
                let ty =
                    match l.Ty with
                    | Some ty -> this.Type ty
                    | None ->
                        let sym = l.Pat.Name
                        let newTVar = env.NewTVar sym l.Span

                        TVar newTVar

                valueMap.Add(l.Pat, ty)
                this.Pat (LetPat { Mut = l.Mut; Static = true }) l.Pat ty
            | _ -> ()

        for item in staticItem do
            match item with
            | FnDecl f -> this.Fn f
            | Let l ->
                let value = this.Expr l.Value

                env.Unify valueMap[l.Pat] value l.Span
            | _ -> ()

    member this.Decl d =
        match d with
        | Let l ->
            let value = this.Expr l.Value

            let ty =
                match l.Ty with
                | Some ty ->
                    let ty = this.Type ty

                    env.Unify ty value l.Span

                    ty
                | None -> value

            this.Pat (LetPat { Mut = l.Mut; Static = false }) l.Pat ty

        | Const _ -> failwith "Not Implemented"
        | Use _ -> failwith "Not Implemented"
        | FnDecl _
        | StructDecl _
        | EnumDecl _
        | TypeDecl _
        | Trait _
        | Impl _ -> ()

    member this.Cond cond block =
        match cond with
        | BoolCond b ->
            env.Unify TBool (this.Expr b) b.Span

            this.Block block
        | LetCond c ->
            let value = this.Expr c.Value
            env.EnterScope BlockScope

            this.Pat CondPat c.Pat value

            let ty = this.Block block

            env.FinishScope()

            env.NormalizeTy ty

    member this.Fn(f: Fn) =
        let tvar, fnTy =
            match bindingRec[f.Name] with
            | BFn(tvar, f) -> tvar, f
            | _ -> failwith "Unreachable"

        env.EnterScope(FnScope { Ret = fnTy.Ret })

        for (param, ty) in Array.zip f.Param fnTy.Param do
            this.Pat ParamPat param.Pat ty

        let ret = this.Block f.Body

        env.Unify fnTy.Ret ret f.Name.Span

        env.FinishScope()

        let tvar, fnTy = env.Generalize tvar fnTy

        bindingRec[f.Name] <- BFn(tvar, fnTy)

    member this.Module(m: Module) =
        env.EnterScope TopLevelScope

        let decl = m.Item |> Array.map _.Decl

        this.HoistDecl decl true

        env.FinishScope()

        let toNever (generic: Var[]) (v: Var) =
            if Array.contains v generic then TVar v else TNever

        for id in bindingRec.Keys do
            let binding = bindingRec[id]

            let binding =
                match binding with
                | BTy ty -> env.NormalizeTy ty |> BTy
                | BFn(tvar, fn) ->
                    let param = Array.map env.NormalizeTy fn.Param
                    let ret = (env.NormalizeTy fn.Ret).Walk(toNever tvar)
                    BFn(tvar, { Param = param; Ret = ret })

            bindingRec[id] <- binding

        let sema =
            { Binding = bindingRec
              Expr = exprRec
              Struct = structRec
              Enum = enumRec
              Capture = captureRec
              Module =
                { Ty = Map.empty
                  Var = Map.empty
                  Module = Map.empty } }

        if error.Count = 0 then Ok sema else Error(error.ToArray())

let check (moduleMap: Dictionary<string, ModuleType>) (m: Module) =
    let traverse = Traverse moduleMap

    traverse.Module m
