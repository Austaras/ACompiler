module Semantic.Analysis

open System.Collections.Generic

// TODO: module system
// TODO: type alias
// TODO: operator overloading

open Syntax.AST
open Semantic
open Env

type internal LetPat = { Mut: bool; Static: bool }

type internal PatMode =
    | ParamPat of bool
    | CondPat
    | LetPat of LetPat

type internal Traverse(env: Environment) =

    member this.Type ty =
        let resolve (id: Id) =
            match env.GetTy id.Sym with
            | Some ty -> ty.Ty
            | None ->
                env.AddError(Undefined id)
                TNever

        match ty with
        | NeverType _ -> TNever
        | IdType i -> resolve i
        | PathType { Prefix = Some Self; Seg = seg } ->
            if seg.Length > 0 then
                failwith "Not Implemented"

            match env.GetSelfType() with
            | Some ty -> ty
            | None ->
                env.AddError(UnboundSelfType ty.Span)
                TNever
        | PathType p ->
            if p.Prefix <> None || p.Seg.Length > 1 then
                failwith "Not Implemented"

            let id, ty = p.Seg[0]

            let instType = Array.map this.Type ty

            let container = resolve id

            match container with
            | TStruct a when a.Generic.Length = instType.Length -> TStruct { a with Generic = instType }
            | TEnum a when a.Generic.Length = instType.Length -> TEnum { a with Generic = instType }
            | _ ->
                env.AddError(GenericMismatch(container, instType, p.Span))

                TNever
        | TupleType t -> TTuple(Array.map this.Type t.Ele)
        | RefType r -> TRef(this.Type r.Ty)
        | InferedType span -> env.NewTVar span |> TVar
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
        env.RegisterPat pat ty

        let mut, mayShadow, isCond, static_ =
            match mode with
            | LetPat { Mut = mut; Static = static_ } -> mut, not static_, false, static_
            | ParamPat mut -> mut, false, false, false
            | CondPat -> true, true, true, false

        let addSym sym (i: Id) (ty: Type) =
            if Map.containsKey i.Sym sym then
                env.AddError(DuplicateDefinition(i, (fst sym[i.Sym])))

            Map.add i.Sym (i, ty) sym

        let rec proc sym ty pat =
            match pat with
            | IdPat i -> addSym sym i ty
            | LitPat l ->
                if not isCond then
                    env.AddError(RefutablePat l.Span)

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
                    let newVar = env.NewTVar pat.Span |> TVar

                    newVar

                let patTy = t.Ele |> Array.map addBinding

                env.Unify (TTuple patTy) ty t.Span

                Array.fold2 proc sym patTy t.Ele
            | AsPat a ->
                let sym = addSym sym a.Id ty

                proc sym ty a.Pat
            | OrPat { Pat = pat; Span = span } ->
                if not isCond then
                    env.AddError(RefutablePat span)

                let allSym = Array.map (proc Map.empty ty) pat

                let first = allSym[0]
                let firstKey = first |> Map.keys |> Array.ofSeq

                for (idx, sym) in Array.indexed allSym do
                    if idx > 0 then
                        let currKey = sym |> Map.keys |> Array.ofSeq

                        if firstKey <> currKey then
                            env.AddError(OrPatDifferent(pat[idx].Span, firstKey, currKey))

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
                if e.Variant.Prefix <> None || e.Variant.Seg.Length > 1 then
                    failwith "Not Implemented"

                if not isCond then
                    env.AddError(RefutablePat e.Span)

                let variantId = e.Variant.Seg[0]

                let enumTy =
                    match env.GetVarTy variantId with
                    | Some ty ->
                        match ty with
                        | TFn({ Ret = TEnum _ } as variant) -> Some variant
                        | ty ->
                            env.AddError(ExpectEnum(variantId, ty))
                            None
                    | None ->
                        env.AddError(Undefined variantId)
                        None

                let payloadTy =
                    match enumTy with
                    | Some fn ->
                        if fn.Param.Length <> e.Payload.Length then
                            env.AddError(ParamLenMismatch(e.Span, fn.Param.Length, e.Payload.Length))

                        env.Unify fn.Ret ty e.Span

                        Array.mapi (fun idx _ -> if idx < fn.Param.Length then fn.Param[idx] else TNever) e.Payload

                    | None -> Array.map (fun _ -> TNever) e.Payload

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

            env.RegisterVar
                mayShadow
                info
                { Generic = [||]
                  Type = ty
                  Pred = [||] }

    member this.ExprInner e =
        match e with
        | Id id ->
            match env.GetVarTyWithCapture id with
            | None ->
                env.AddError(Undefined id)
                TNever
            | Some ty -> ty

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

                env.ExitScope()

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
            // method
            | Field f ->
                let receiver = this.Expr f.Receiver
                let arg = Array.map this.Expr c.Arg
                env.FindMethod receiver arg f.Field.Sym f.Span

            | _ ->
                let callee = this.Expr c.Callee

                let arg = Array.map this.Expr c.Arg
                let ret = TVar(env.NewTVar c.Span)

                env.Unify (TFn { Param = arg; Ret = ret }) callee c.Span

                env.NormalizeTy ret
        | As a ->
            let ty = this.Type a.Ty
            // As has three kinds of usage
            // 1. cast to another kind of number
            // 2. make trait object
            // 3. make slice from array
            failwith "Not Implemented"
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
                let ptr = TVar(env.NewTVar u.Value.Span)

                env.Unify (TRef ptr) value u.Span

                env.NormalizeTy ptr
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
                | None -> env.AddError(Undefined id)
                | Some(info) ->
                    if not info.Mut then
                        env.AddError(AssignImmutable(info.Def, a.Span))

            UnitType
        | Field f ->
            let receiver = (this.Expr f.Receiver).StripRef()
            let key = f.Field.Sym

            env.FindField receiver key f.Span

        | TupleAccess(_) -> failwith "Not Implemented"
        | Index idx ->
            let container = this.Expr idx.Container
            let index = this.Expr idx.Index
            env.Unify (TInt(true, ISize)) index idx.Index.Span
            let value = env.NewTVar idx.Span |> TVar
            env.Unify (TSlice value) container idx.Span
            env.NormalizeTy value
        | Array a ->
            if a.Ele.Length = 0 then
                let ele = env.NewTVar a.Span
                TSlice(TVar ele) // , 0UL)
            else
                let first = this.Expr a.Ele[0]

                for ele in a.Ele[1..] do
                    let ty = this.Expr ele
                    env.Unify first ty ele.Span

                TSlice(first) //, uint64 a.Ele.Length)

        | ArrayRepeat a ->
            // TODO: clone trait
            let ty = this.Expr a.Ele

            match a.Len with
            | LitExpr { Value = Int len } -> TSlice ty // len)
            | _ -> failwith "Not Implemented"

        | StructLit s ->
            if s.Struct.Prefix <> None || s.Struct.Seg.Length > 1 then
                failwith "Not Implemented"

            let stru, gen = s.Struct.Seg[0]
            let span = stru.Span

            match env.GetTy stru.Sym with
            | None ->
                env.AddError(Undefined stru)
                TNever
            | Some { Ty = TStruct sTy; Def = id } ->
                let stru = env.GetStruct id

                let gen =
                    if gen.Length > 0 then
                        Array.map this.Type gen
                    else
                        Array.map (fun _ -> TVar(env.NewTVar span)) stru.Generic

                let map = Array.zip stru.Generic gen |> Map.ofArray

                let sTy = TStruct { sTy with Generic = gen }

                for field in s.Field do
                    match field with
                    | ShorthandField v ->
                        if stru.Field.ContainsKey v.Sym then
                            let field = stru.Field[v.Sym].InstantiateWithMap map

                            match env.GetVarTyWithCapture id with
                            | None -> env.AddError(Undefined id)
                            | Some ty -> env.Unify field ty v.Span
                        else
                            env.AddError(UndefinedField(v.Span, v.Sym))
                    | KeyValueField kv ->
                        if stru.Field.ContainsKey kv.Name.Sym then
                            let field = stru.Field[kv.Name.Sym].InstantiateWithMap map
                            let ty = this.Expr kv.Value
                            env.Unify field ty kv.Span
                        else
                            env.AddError(UndefinedField(kv.Name.Span, kv.Name.Sym))
                    | RestField r ->
                        let ty = this.Expr r.Value
                        env.Unify sTy ty r.Span

                env.NormalizeTy sTy
            | Some ty ->
                env.AddError(ExpectStruct(stru, ty.Ty))
                TNever

        | Tuple t -> t.Ele |> Array.map this.Expr |> TTuple
        | Closure c ->
            let paramTy (p: Param) =
                match p.Ty with
                | Some ty -> this.Type ty
                | None ->
                    let newTVar = env.NewTVar p.Span

                    TVar newTVar

            let paramTy = Array.map paramTy c.Param

            let retTy =
                match c.Ret with
                | Some ty -> this.Type ty
                | None -> TVar(env.NewTVar c.Span)

            let closureScope = ClosureScope { Closure = c; Ret = retTy }

            env.EnterScope closureScope

            for (param, ty) in Array.zip c.Param paramTy do
                this.Pat (ParamPat param.Mut) param.Pat ty

            let ret = this.Expr c.Body

            env.Unify retTy ret c.Span

            env.ExitScope()

            TFn
                { Param = Array.map env.NormalizeTy paramTy
                  Ret = env.NormalizeTy retTy }

        | Path _ -> failwith "Not Implemented"
        | Break _ -> TNever
        | Continue _ -> TNever
        | Return r ->
            let retTy =
                match env.GetReturn() with
                | Some ty -> ty
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

    member this.Expr e =
        let ty = this.ExprInner e
        env.RegisterExpr e ty
        ty

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

        env.ExitScope()

        env.NormalizeTy ty

    member _.TyParam(p: TyParam[]) =
        let group = env.NewGenGroup()

        let gen = ResizeArray()
        let pred = ResizeArray()

        for (idx, p) in Array.indexed p do
            let generic =
                { GroupId = group
                  Id = idx
                  Sym = p.Id.Sym }

            env.RegisterTy p.Id (TGen generic)

            gen.Add generic

            for b in p.Bound do
                if b.Prefix <> None || b.Seg.Length > 1 then
                    failwith "Not Implemented"

                let name = fst b.Seg[0]

                let tr = env.GetTrait (fst b.Seg[0]).Sym

                match tr with
                | None -> env.AddError(Undefined name)
                | Some tr ->
                    let p = { Trait = tr; Type = TGen generic }
                    pred.Add p
                    env.AddPred p

        gen.ToArray(), pred.ToArray()

    member this.HoistDecl (decl: seq<Decl>) topLevel =
        let genMap = Dictionary()
        let fnMap = Dictionary()

        let makeGen group (idx, id: Id) =
            { GroupId = group
              Id = idx
              Sym = id.Sym }

        // Process Type Decl Hoisted Name
        for d in decl do
            match d with
            | Let _
            | Const _
            | FnDecl _ -> ()
            | StructDecl s ->
                let group = env.NewGenGroup()
                let gen = s.TyParam |> Array.indexed |> Array.map (makeGen group)
                genMap.Add(s.Name, gen)

                env.RegisterTy
                    s.Name
                    (TStruct
                        { Name = s.Name
                          Generic = Array.map TGen gen })

            | EnumDecl e ->
                let group = env.NewGenGroup()
                let gen = e.TyParam |> Array.indexed |> Array.map (makeGen group)
                genMap.Add(e.Name, gen)

                env.RegisterTy
                    e.Name
                    (TEnum
                        { Name = e.Name
                          Generic = Array.map TGen gen })

            | TypeDecl _ -> failwith "Not Implemented"
            | Use _ -> failwith "Not Implemented"
            | Trait t ->
                let group = env.NewGenGroup()

                let makeGen (idx, p: TyParam) =
                    { GroupId = group
                      Id = idx + 1
                      Sym = p.Id.Sym }

                let self =
                    { GroupId = group
                      Id = 0
                      Sym = "self" }

                let gen = t.TyParam |> Array.indexed |> Array.map makeGen
                genMap.Add(t.Name, Array.append [| self |] gen)

                env.RegisterTy
                    t.Name
                    (TTrait
                        { Name = t.Name
                          Generic = Array.map TGen gen })
            | Impl _ -> ()

        // Process Type Decl
        for d in decl do
            match d with
            | Let l when topLevel ->
                let ty: Type =
                    match l.Ty with
                    | Some ty -> this.Type ty
                    | None -> env.NewTVar l.Span |> TVar

                this.Pat (LetPat { Mut = l.Mut; Static = true }) l.Pat ty
            | Let _ -> ()
            | Const _ -> ()
            | FnDecl f ->
                env.EnterScope TypeScope
                let gen, pred = this.TyParam f.TyParam

                let paramTy (p: Param) =
                    match p.Ty with
                    | Some ty -> this.Type ty
                    | None ->
                        let newTVar = env.NewTVar p.Span
                        TVar newTVar

                let param = Array.map paramTy f.Param

                let ret =
                    match f.Ret with
                    | Some ty -> this.Type ty
                    | None -> TVar(env.NewTVar f.Span)

                env.ExitScope()

                let info =
                    { Def = f.Name
                      Mut = false
                      Static = true }

                let fnTy = { Param = param; Ret = ret }

                let fnScope =
                    { Param = param
                      Ret = ret
                      Fixed = f.TyParam.Length > 0
                      Name = f.Name }

                fnMap.Add(f.Name, fnScope)

                env.RegisterVar
                    false
                    info
                    { Generic = gen
                      Type = TFn fnTy
                      Pred = pred }
            | StructDecl s ->
                let gen = genMap[s.Name]

                env.EnterScope(
                    AdtScope
                        { Self =
                            TStruct
                                { Name = s.Name
                                  Generic = Array.map TGen gen } }
                )

                for idx, p in Array.indexed s.TyParam do
                    env.RegisterTy p (TGen gen[idx])

                let processField m (field: StructFieldDef) =
                    let name = field.Name.Sym

                    if Map.containsKey name m then
                        env.AddError(DuplicateField field.Name)

                    Map.add name (this.Type field.Ty) m

                let field = Array.fold processField Map.empty s.Field

                env.ExitScope()

                let stru =
                    { Name = s.Name
                      Field = field
                      Generic = gen }

                env.RegisterStruct s stru

            | EnumDecl e ->
                let gen = genMap[e.Name]

                env.EnterScope(
                    AdtScope
                        { Self =
                            TStruct
                                { Name = e.Name
                                  Generic = Array.map TGen gen } }
                )

                for idx, p in Array.indexed e.TyParam do
                    env.RegisterTy p (TGen gen[idx])

                let processVariant m (variant: EnumVariantDef) =
                    let name = variant.Name.Sym

                    if Map.containsKey name m then
                        env.AddError(DuplicateVariant variant.Name)

                    let payload = Array.map this.Type variant.Payload

                    Map.add name payload m

                let variant = Array.fold processVariant Map.empty e.Variant

                env.ExitScope()

                let enum =
                    { Name = e.Name
                      Variant = variant
                      Generic = gen }

                env.RegisterEnum e enum

            | TypeDecl _ -> failwith "Not Implemented"
            | Use _ -> failwith "Not Implemented"
            | Trait t ->
                let gen = genMap[t.Name]

                env.EnterScope(TraitScope { Self = TGen gen[0] })

                for idx, p in Array.indexed t.TyParam do
                    env.RegisterTy p.Id (TGen gen[idx + 1])

                let super = ResizeArray()

                for path in t.Super do
                    if path.Prefix <> None || path.Seg.Length > 1 then
                        failwith "Not Implemented"

                    let id = (fst path.Seg[0])

                    let tr = env.GetTrait id.Sym

                    match tr with
                    | Some s -> super.Add s
                    | None -> env.AddError(Undefined id)

                let super = super.ToArray()

                let processParam (p: Param) = p.Ty |> Option.get |> this.Type

                let processMember (method: Map<string, Function>) (m: TraitMember) =
                    match m with
                    | TraitMethod m ->
                        match m.Default with
                        | Some _ -> failwith "Not Implemented"
                        | None -> ()

                        let param = Array.map processParam m.Param[1..]

                        let ret =
                            match m.Ret with
                            | Some r -> this.Type r
                            | None -> UnitType

                        let f = { Param = param; Ret = ret }

                        Map.add m.Name.Sym f method
                    | TraitType t -> method
                    | _ -> failwith "Not Implemented"

                let method = t.Item |> Array.map _.Member |> Array.fold processMember Map.empty

                let methodSafe f =
                    (TFn f).FindTGen() |> Seq.forall (fun g -> g.Id <> 0)

                let safe = method |> Map.values |> Seq.forall methodSafe

                env.ExitScope()

                env.RegisterTrait
                    { Name = t.Name
                      Method = method
                      Generic = gen
                      ObjectSafe = safe
                      Super = super }
            | Impl i ->
                let trait_ =
                    match i.Trait with
                    | None -> failwith "Not Implemented"
                    | Some t ->
                        if t.Prefix <> None || t.Seg.Length > 1 || (snd t.Seg[0]).Length > 0 then
                            failwith "Not Implemented"

                        fst t.Seg[0]

                env.EnterScope TypeScope

                let gen, pred = this.TyParam i.TyParam
                let ty = this.Type i.Ty

                let scm =
                    { Generic = gen
                      Type = ty
                      Pred = pred }

                match env.GetTrait trait_.Sym with
                | None -> env.AddError(Undefined trait_)
                | Some t -> env.ImplTrait t scm i.Span

                env.ExitScope()

        for item in decl do
            match item with
            | FnDecl f ->
                let fnScope = fnMap[f.Name]

                env.EnterScope(FnScope fnScope)

                for (param, ty) in Array.zip f.Param fnScope.Param do
                    this.Pat (ParamPat param.Mut) param.Pat ty

                let ret = this.Block f.Body

                env.Unify fnScope.Ret ret f.Name.Span

                env.ExitScope()

            | Let l when topLevel ->
                let value = this.Expr l.Value

                env.Unify (env.GetPatTy l.Pat) value l.Span
            | _ -> ()

        for name in fnMap.Keys do
            env.ToNever name

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

            env.ExitScope()

            env.NormalizeTy ty

    member this.Module(m: Module) =
        env.EnterScope TopLevelScope

        let decl = m.Item |> Array.map _.Decl

        this.HoistDecl decl true

        env.ExitScope()

let analysis (sema: SemanticInfo) (m: Module) =
    let error = ResizeArray()
    let env = Environment(sema, error)

    let traverse = Traverse env

    traverse.Module m

    for id in sema.DeclTy.Keys do
        let scm = sema.DeclTy[id]

        let ty = env.NormalizeTy scm.Type

        sema.DeclTy[id] <- { scm with Type = ty }

    if error.Count = 0 then Ok sema else Error(error.ToArray())
