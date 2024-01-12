module AST.Dump

open System.IO

open Common.Span
open AST.AST

let span (s: Span) = $"@{s.First}..{s.Last}"

let indent (tw: TextWriter) level =
    for _ in 0 .. level - 1 do
        tw.Write "    "

let id i = $"{i.Sym}{span i.Span}"

let lit (l: Literal) =
    let value =
        match l.Value with
        | Bool b -> string b
        | Int i -> string i
        | Float f -> $"{f}f"
        | Char c -> $"'{c}'"
        | String s -> "\"" + s + "\""

    value + span l.Span

let rec pat (tw: TextWriter) level (p: Pat) =
    let s = span p.Span
    let propIdent () = indent tw (level + 1)
    let childIdent () = indent tw (level + 2)

    let path level (p: PathPat) =
        match p.Prefix with
        | None -> ()
        | Some p ->
            indent tw level
            tw.WriteLine("prefix: " + p.ToString)

        for s in p.Seg do
            indent tw level
            tw.WriteLine("seg: " + id s)

    match p with
    | IdPat i -> tw.WriteLine(id i)
    | LitPat l -> tw.WriteLine(lit l)
    | TuplePat t ->
        tw.WriteLine("Tuple" + s)

        for p in t.Ele do
            propIdent ()
            pat tw (level + 1) p

    | ArrayPat a ->
        tw.WriteLine("Array" + s)

        for p in a.Ele do
            propIdent ()
            pat tw (level + 1) p

    | AsPat a ->
        tw.WriteLine("As" + s)

        propIdent ()
        tw.Write "pat: "
        pat tw (level + 1) a.Pat

        propIdent ()
        tw.WriteLine("id: " + id a.Id)

    | PathPat p -> path (level + 1) p
    | EnumPat e ->
        tw.WriteLine("Enum" + s)

        propIdent ()
        tw.WriteLine("variant" + span e.Variant.Span)
        path (level + 2) e.Variant

        for p in e.Payload do
            propIdent ()
            tw.Write "payload: "
            pat tw (level + 1) p

    | StructPat stru ->
        tw.WriteLine("Struct" + s)

        propIdent ()
        tw.WriteLine("struct" + span stru.Struct.Span)
        path (level + 2) stru.Struct

        for f in stru.Field do
            propIdent ()
            tw.Write $"field: "

            match f with
            | ShorthandPat s -> tw.WriteLine(id s)
            | KeyValuePat k ->
                tw.WriteLine("key value" + span k.Span)

                childIdent ()
                tw.WriteLine $"key: {id k.Id}"

                childIdent ()
                tw.Write $"value: "
                pat tw (level + 2) k.Pat

    | OrPat o ->
        tw.WriteLine("Or" + s)

        for p in o.Pat do
            propIdent ()
            pat tw (level + 1) p

    | CatchAllPat _ -> tw.WriteLine("_" + s)
    | RangePat r ->
        tw.WriteLine("Range" + s)

        match r.From with
        | None -> ()
        | Some f ->
            propIdent ()
            tw.Write "from: "
            pat tw (level + 1) f

        match r.To with
        | None -> ()
        | Some t ->
            propIdent ()
            tw.Write "to: "
            pat tw (level + 1) t

    | SelfPat _ -> tw.WriteLine("self" + s)
    | RefSelfPat _ -> tw.WriteLine("ref self" + s)

let rec path (tw: TextWriter) level (p: Path) =
    match p.Prefix with
    | None -> ()
    | Some p ->
        indent tw level
        tw.WriteLine("prefix: " + p.ToString)

    for (i, t) in p.Seg do
        indent tw level
        tw.WriteLine $"seg: {id i}"

        for t in t do
            indent tw level
            tw.Write "type arg: "
            ty tw (level) t

and ty (tw: TextWriter) level (t: Type) =
    let s = span t.Span
    let propIdent () = indent tw (level + 1)

    match t with
    | IdType i -> tw.WriteLine(id i)
    | LitType l -> tw.WriteLine(lit l)
    | PathType p ->
        tw.WriteLine("Path" + s)

        path tw (level + 1) p
    | InferedType _ -> tw.WriteLine("_" + s)
    | NeverType _ -> tw.WriteLine("!" + s)
    | NegType r ->
        tw.WriteLine("Neg" + s)
        propIdent ()
        ty tw (level + 1) r.Ty
    | RefType r ->
        tw.WriteLine("Ref" + s)
        propIdent ()
        ty tw (level + 1) r.Ty

    | TupleType t ->
        tw.WriteLine("Tuple" + s)

        for t in t.Ele do
            propIdent ()
            ty tw (level + 1) t

    | ArrayType a ->
        tw.WriteLine("Array" + s)

        propIdent ()
        tw.Write "element: "
        ty tw (level + 1) a.Ele

        match a.Len with
        | None -> ()
        | Some l ->
            propIdent ()
            tw.WriteLine $"length{span l.Span}"
            indent tw (level + 2)
            ty tw (level + 2) l

    | FnType f ->
        tw.WriteLine("Fn" + s)

        for t in f.Param do
            propIdent ()
            tw.Write("param: ")
            ty tw (level + 1) t

        propIdent ()
        tw.Write "ret: "
        ty tw (level + 1) f.Ret

and tyParam (tw: TextWriter) level (p: TyParam) =
    indent tw level
    tw.WriteLine("id: " + id p.Id)

    if p.Const then
        indent tw level
        tw.WriteLine("const: true")

    for b in p.Bound do
        indent tw level
        tw.WriteLine("bound" + span b.Span)
        path tw (level + 1) b

let param (tw: TextWriter) level (p: Param) =
    indent tw level
    tw.Write "pat: "
    pat tw (level + 1) p.Pat

    match p.Ty with
    | None -> ()
    | Some t ->
        indent tw level
        tw.Write "type: "
        ty tw (level + 1) t

let rec cond (tw: TextWriter) level (c: Cond) =
    let propIdent () = indent tw (level + 1)

    match c with
    | BoolCond e -> expr tw level e
    | LetCond l ->
        tw.WriteLine $"Let{span l.Span}"

        propIdent ()
        tw.Write "pat: "
        pat tw (level + 1) l.Pat

        propIdent ()
        tw.Write "value: "
        expr tw (level + 1) l.Value

and expr (tw: TextWriter) level (e: Expr) =
    let s = span e.Span
    let propIdent () = indent tw (level + 1)
    let childIdent () = indent tw (level + 2)

    match e with
    | Id i -> tw.WriteLine(id i)
    | SelfExpr _ -> tw.WriteLine("Self" + s)
    | LitExpr l -> tw.WriteLine(lit l)
    | Call c ->
        tw.WriteLine("Call" + s)

        propIdent ()
        tw.Write $"callee: "
        expr tw (level + 1) c.Callee

        for arg in c.Arg do
            propIdent ()
            tw.Write "arg: "
            expr tw (level + 1) arg

    | Unary u ->
        tw.WriteLine("Unary" + s)

        propIdent ()
        tw.WriteLine("op: " + u.Op.ToString)

        propIdent ()
        tw.Write "value: "
        expr tw (level + 1) u.Value

    | Assign a ->
        tw.WriteLine("Assign" + s)

        propIdent ()
        tw.Write "place: "
        expr tw (level + 1) a.Place

        propIdent ()

        match a.Op with
        | Some op -> tw.WriteLine $"op: {op.ToString}="
        | None -> tw.WriteLine "op: ="

        propIdent ()
        tw.Write "value: "
        expr tw (level + 1) a.Value

    | Binary b ->
        tw.WriteLine("Binary" + s)

        propIdent ()
        tw.Write "left: "
        expr tw (level + 1) b.Left

        propIdent ()
        tw.WriteLine("op: " + b.Op.ToString)

        propIdent ()
        tw.Write "right: "
        expr tw (level + 1) b.Right

    | Field f ->
        tw.WriteLine("Field" + s)

        propIdent ()
        tw.Write "receiver: "
        expr tw (level + 1) f.Receiver

        propIdent ()
        tw.Write "field: "
        tw.WriteLine(id f.Field)

    | TupleAccess t ->
        tw.WriteLine("TupleAccess" + s)

        propIdent ()
        tw.Write "receiver: "
        expr tw (level + 1) t.Receiver

        propIdent ()
        let idx, s = t.Index
        tw.WriteLine $"field: {idx}{span s}"

    | Index i ->
        tw.WriteLine("Index" + s)

        propIdent ()
        tw.Write "container: "
        expr tw (level + 1) i.Container

        propIdent ()
        tw.Write $"index: "
        expr tw (level + 1) i.Index

    | Array a ->
        tw.WriteLine("Array" + s)

        for item in a.Ele do
            propIdent ()
            expr tw (level + 1) item

    | ArrayRepeat a ->
        tw.WriteLine("Array" + s)

        propIdent ()
        tw.Write "ele: "
        expr tw (level + 1) a.Ele

        propIdent ()
        tw.Write "length: "
        expr tw (level + 1) a.Len

    | Tuple t ->
        tw.WriteLine("Tuple" + s)

        for item in t.Ele do
            propIdent ()
            expr tw (level + 1) item

    | Range r ->
        tw.WriteLine("Range" + s)

        match r.From with
        | Some from ->
            propIdent ()
            tw.Write "from: "
            expr tw (level + 1) from
        | None -> ()

        propIdent ()
        tw.WriteLine("exclusive: " + string r.Exclusive)

        match r.To with
        | Some to_ ->
            propIdent ()
            tw.Write "to: "
            expr tw (level + 1) to_
        | None -> ()

    | StructLit stru ->
        tw.WriteLine("Struct" + s)

        propIdent ()
        tw.WriteLine("struct" + span stru.Struct.Span)
        path tw (level + 2) stru.Struct

        for f in stru.Field do
            propIdent ()
            tw.Write $"field: "

            match f with
            | ShorthandField s -> tw.WriteLine(id s)
            | KeyValueField k ->
                tw.WriteLine("key value" + span k.Span)

                childIdent ()
                tw.WriteLine $"key: {id k.Name}"

                childIdent ()
                tw.Write $"value: "
                expr tw (level + 2) k.Value
            | RestField s ->
                tw.WriteLine("rest" + span s.Span)
                childIdent ()
                expr tw (level + 2) s.Value

    | Closure c ->
        tw.WriteLine("Closure" + s)

        for p in c.Param do
            propIdent ()
            tw.WriteLine("param" + span p.Span)
            param tw (level + 2) p

        match c.Ret with
        | None -> ()
        | Some r ->
            propIdent ()
            tw.Write $"ret: "
            ty tw (level + 1) r

        propIdent ()
        tw.Write $"body: "
        expr tw (level + 1) c.Body

    | Path p ->
        tw.WriteLine("Path" + s)

        path tw (level + 1) p
    | Break _ -> tw.WriteLine("Break" + s)
    | Continue _ -> tw.WriteLine("Continue" + s)
    | Return r ->
        tw.WriteLine("Return" + s)

        match r.Value with
        | Some v ->
            propIdent ()
            tw.Write "value: "
            expr tw (level + 1) v
        | None -> ()

    | TryReturn t ->
        tw.WriteLine("TryReturn" + s)

        propIdent ()
        expr tw (level + 1) t.Base

    | Block b ->
        tw.WriteLine("Block" + s)
        block tw (level + 1) b

    | If i ->
        tw.WriteLine("If" + s)

        propIdent ()
        tw.Write "cond: "
        cond tw (level + 1) i.Cond

        propIdent ()
        tw.WriteLine("then" + span i.Then.Span)
        block tw (level + 2) i.Then

        for e in i.ElseIf do
            propIdent ()
            tw.WriteLine("else if" + span e.Span)

            childIdent ()
            tw.Write "cond: "
            cond tw (level + 2) e.Cond

            childIdent ()
            tw.WriteLine("body" + span e.Block.Span)
            block tw (level + 3) i.Then

        match i.Else with
        | Some e ->
            propIdent ()
            tw.WriteLine("else" + span e.Span)
            block tw (level + 2) e
        | None -> ()

    | Match m ->
        tw.WriteLine("Match" + s)

        propIdent ()
        tw.Write "value: "
        expr tw (level + 1) m.Value

        for b in m.Branch do
            propIdent ()
            tw.WriteLine("branch" + span b.Span)

            childIdent ()
            tw.Write "pat: "
            pat tw (level + 2) b.Pat

            match b.Guard with
            | None -> ()
            | Some g ->
                childIdent ()
                tw.Write "guard: "
                expr tw (level + 2) g

            childIdent ()
            tw.Write "expr: "
            expr tw (level + 2) b.Expr

    | While w ->
        tw.WriteLine("While" + s)

        propIdent ()
        tw.Write "cond: "
        cond tw (level + 1) w.Cond

        propIdent ()
        tw.WriteLine("body" + span w.Body.Span)
        block tw (level + 2) w.Body

    | For f ->
        tw.WriteLine("For" + s)

        propIdent ()
        tw.Write "pat: "
        pat tw (level + 1) f.Pat

        propIdent ()
        tw.Write "iterator: "
        expr tw (level + 1) f.Iter

        propIdent ()
        tw.WriteLine("body" + span f.Body.Span)
        block tw (level + 2) f.Body

and block (tw: TextWriter) level (b: Block) =
    for s in b.Stmt do
        indent tw level
        stmt tw level s

and stmt (tw: TextWriter) level s =
    match s with
    | ExprStmt e -> expr tw level e
    | DeclStmt d -> decl tw level d

and decl (tw: TextWriter) level (decl: Decl) =
    let s = span decl.Span
    let propIdent () = indent tw (level + 1)
    let childIdent () = indent tw (level + 2)

    let name (i: Id) =
        propIdent ()
        tw.WriteLine("name: " + id i)

    let tyParam level (param: TyParam[]) =
        for p in param do
            propIdent ()
            tw.WriteLine("type param" + span p.Span)
            tyParam tw (level + 1) p

    let func level (f: Fn) =
        indent tw level
        tw.WriteLine("name: " + id f.Name)

        tyParam level f.TyParam

        for p in f.Param do
            indent tw level
            tw.WriteLine("param" + span p.Span)
            param tw (level + 1) p

        match f.Ret with
        | None -> ()
        | Some r ->
            indent tw level
            tw.Write "ret: "
            ty tw (level + 1) r

        indent tw level
        tw.WriteLine("body" + span f.Body.Span)
        block tw (level + 1) f.Body

    match decl with
    | Let l ->
        tw.WriteLine("Let" + s)

        if l.Mut then
            propIdent ()
            tw.WriteLine "mut: true"

        propIdent ()
        tw.Write "pat: "
        pat tw (level + 1) l.Pat

        match l.Ty with
        | None -> ()
        | Some t ->
            propIdent ()
            tw.Write "type: "
            ty tw (level + 1) t

        propIdent ()
        tw.Write "value: "
        expr tw (level + 1) l.Value

    | Const _ -> failwith "Not Implemented"
    | FnDecl f ->
        tw.WriteLine("Function" + s)
        func (level + 1) f

    | StructDecl stru ->
        tw.WriteLine("Struct" + s)

        name stru.Name

        tyParam (level + 1) stru.TyParam

        for p in stru.Field do
            propIdent ()
            tw.WriteLine("field" + span p.Span)

            childIdent ()
            tw.WriteLine("vis: " + p.Vis.ToString)

            childIdent ()
            tw.WriteLine("name: " + id p.Name)

            childIdent ()
            tw.Write "type: "
            ty tw (level + 2) p.Ty

    | EnumDecl e ->
        tw.WriteLine("Enum" + s)

        name e.Name

        tyParam (level + 1) e.TyParam

        for p in e.Variant do
            propIdent ()
            tw.WriteLine("variant" + span p.Span)

            childIdent ()
            tw.WriteLine("name: " + id p.Name)

            for p in p.Payload do
                childIdent ()
                tw.Write "payload: "
                ty tw (level + 2) p

    | TypeDecl t ->
        tw.WriteLine("Type" + s)

        name t.Name

        propIdent ()
        tw.WriteLine("type" + span t.Ty.Span)
        ty tw (level + 1) t.Ty

    | Use u ->
        tw.WriteLine("Use" + s)

        match u.Prefix with
        | None -> ()
        | Some p ->
            propIdent ()
            tw.WriteLine("prefix: " + p.ToString)

        for s in u.Seg do
            propIdent ()
            tw.WriteLine("seg: " + id s)

        propIdent ()
        tw.WriteLine("item" + span u.Item.Span)

    | Trait t ->
        tw.WriteLine("Trait" + s)

        name t.Name

        tyParam (level + 1) t.TyParam

        for s in t.Super do
            propIdent ()
            tw.WriteLine("super" + span s.Span)
            path tw (level + 2) s

        for i in t.Item do
            propIdent ()
            tw.Write("item: ")

            let s = span i.Span

            match i with
            | TraitMethod m ->
                tw.WriteLine("trait method" + s)

                childIdent ()
                tw.WriteLine("name: " + id m.Name)

                for p in m.Param do
                    childIdent ()
                    tw.WriteLine("param" + span p.Span)
                    param tw (level + 3) p

                match m.Ret with
                | None -> ()
                | Some r ->
                    childIdent ()
                    tw.Write "ret: "
                    ty tw (level + 3) r

                match m.Default with
                | None -> ()
                | Some f ->
                    childIdent ()
                    tw.WriteLine("body" + span f.Span)
                    block tw (level + 3) f

            | TraitType t -> tw.WriteLine("trait type" + s)
            | TraitValue v -> tw.WriteLine("trait value" + s)

    | Impl i ->
        tw.WriteLine("Impl" + s)

        tyParam (level + 1) i.TyParam

        match i.Trait with
        | None -> ()
        | Some t ->
            propIdent ()
            tw.WriteLine("trait" + span t.Span)
            path tw (level + 2) t

        propIdent ()
        tw.Write "type: "
        ty tw (level + 1) i.Ty

        for i in i.Item do
            propIdent ()
            tw.WriteLine("visibility: " + i.Vis.ToString)

            propIdent ()
            tw.Write("item: ")

            let s = span i.Span

            match i.Item with
            | Method f ->
                tw.WriteLine("method" + s)
                func (level + 2) f

            | AssocType(_) -> failwith "Not Implemented"
            | AssocValue(_) -> failwith "Not Implemented"

let moduleItem (tw: TextWriter) level (item: ModuleItem) =
    let propIdent () = indent tw (level + 1)

    tw.WriteLine $"ModuleItem{span item.Span}"

    propIdent ()
    tw.WriteLine("visibility: " + item.Vis.ToString)

    propIdent ()
    tw.Write "item: "
    decl tw (level + 1) item.Decl

let dump (tw: TextWriter) (m: Module) =
    tw.WriteLine $"Module{span m.Span}"

    for item in m.Item do
        indent tw 1

        moduleItem tw 1 item
