module AST.Dump

open System.IO

open Common.Span
open AST.AST


type Dump(tw: TextWriter) =
    let mutable level = 0

    member _.Span(s: Span) = $"@{s.First}..{s.Last}"

    member this.Id i =
        tw.WriteLine $"{i.Sym}{this.Span i.Span}"

    member _.Indent() =
        for _ in 0 .. level - 1 do
            tw.Write "    "

    member this.Prop name =
        this.Indent()
        tw.Write(name + ": ")

    member this.Child name span cb payload =
        this.Indent()
        tw.WriteLine(name + this.Span span)
        level <- level + 1
        cb payload
        level <- level - 1

    member this.Lit(l: Literal) =
        let value =
            match l.Value with
            | Bool b -> string b
            | Int i -> string i
            | Float f -> $"{f}f"
            | Char c -> $"'{c}'"
            | String s -> "\"" + s + "\""

        value + this.Span l.Span

    member this.Pat(p: Pat) =
        let s = this.Span p.Span

        let path (p: PathPat) =
            match p.Prefix with
            | None -> ()
            | Some p ->
                this.Prop "prefix"
                tw.WriteLine p.ToString

            for s in p.Seg do
                this.Prop "seg"
                this.Id s

        level <- level + 1

        match p with
        | IdPat i -> this.Id i
        | LitPat l -> tw.WriteLine(this.Lit l)
        | TuplePat t ->
            tw.WriteLine("Tuple" + s)

            for p in t.Ele do
                this.Indent()
                this.Pat p

        | ArrayPat a ->
            tw.WriteLine("Array" + s)

            for p in a.Ele do
                this.Indent()
                this.Pat p

        | AsPat a ->
            tw.WriteLine("As" + s)

            this.Prop "pat"
            this.Pat a.Pat

            this.Prop "id"
            this.Id a.Id

        | PathPat p -> path p
        | EnumPat e ->
            tw.WriteLine("Enum" + s)

            this.Child "variant" e.Variant.Span path e.Variant

            for p in e.Payload do
                this.Prop "payload"
                this.Pat p

        | StructPat stru ->
            tw.WriteLine("Struct" + s)

            this.Child "struct" stru.Struct.Span path stru.Struct

            for f in stru.Field do
                this.Prop "field"

                match f with
                | ShorthandPat s -> this.Id s
                | KeyValuePat k ->
                    tw.WriteLine("key value" + this.Span k.Span)

                    level <- level + 1

                    this.Prop "key"
                    this.Id k.Id

                    this.Prop "value"
                    this.Pat k.Pat
                    level <- level - 1

        | OrPat o ->
            tw.WriteLine("Or" + s)

            for p in o.Pat do
                this.Indent()
                this.Pat p

        | CatchAllPat _ -> tw.WriteLine("_" + s)
        | RangePat r ->
            tw.WriteLine("Range" + s)

            match r.From with
            | None -> ()
            | Some f ->
                this.Prop "from"
                this.Pat f

            match r.To with
            | None -> ()
            | Some t ->
                this.Prop "to"
                this.Pat t

        | SelfPat _ -> tw.WriteLine("self" + s)
        | RefSelfPat _ -> tw.WriteLine("ref self" + s)

        level <- level - 1

    member this.Path(p: Path) =
        match p.Prefix with
        | None -> ()
        | Some p ->
            this.Prop "prefix"
            tw.WriteLine p.ToString

        for (i, t) in p.Seg do
            this.Prop "seg"
            this.Id i

            for t in t do
                this.Prop "type arg"
                this.Type t

    member this.Type(t: Type) =
        let s = this.Span t.Span

        level <- level + 1

        match t with
        | IdType i -> this.Id i
        | LitType l -> tw.WriteLine(this.Lit l)
        | PathType p ->
            tw.WriteLine("Path" + s)
            this.Path p
        | InferedType _ -> tw.WriteLine("_" + s)
        | NeverType _ -> tw.WriteLine("!" + s)
        | NegType r ->
            tw.WriteLine("Neg" + s)
            this.Indent()
            this.Type r.Ty
        | RefType r ->
            tw.WriteLine("Ref" + s)
            this.Indent()
            this.Type r.Ty

        | TupleType t ->
            tw.WriteLine("Tuple" + s)

            for t in t.Ele do
                this.Indent()
                this.Type t

        | ArrayType a ->
            tw.WriteLine("Array" + s)

            this.Prop "element"
            this.Type a.Ele

            match a.Len with
            | None -> ()
            | Some l ->
                this.Indent()
                tw.WriteLine("length" + this.Span l.Span)
                level <- level + 1
                this.Indent()
                this.Type l
                level <- level - 1

        | FnType f ->
            tw.WriteLine("Fn" + s)

            for t in f.Param do
                this.Prop "param"
                this.Type t

            this.Prop "ret"
            this.Type f.Ret

        level <- level - 1

    member this.TyParam(p: TyParam) =
        this.Prop "id"
        this.Id p.Id

        if p.Const then
            this.Prop "const"
            tw.WriteLine("true")

        for b in p.Bound do
            this.Child "bound" b.Span this.Path b

    member this.Param(p: Param) =
        level <- level + 1

        this.Prop "pat"
        this.Pat p.Pat

        match p.Ty with
        | None -> ()
        | Some t ->
            this.Prop "type"
            this.Type t

        level <- level - 1

    member this.Cond(c: Cond) =
        match c with
        | BoolCond e -> this.Expr e
        | LetCond l ->
            tw.WriteLine("Let" + this.Span l.Span)

            level <- level + 1

            this.Prop "pat"
            this.Pat l.Pat

            this.Prop "value"
            this.Expr l.Value
            level <- level - 1

    member this.Expr(e: Expr) =
        let s = this.Span e.Span

        level <- level + 1

        match e with
        | Id i -> this.Id i
        | SelfExpr _ -> tw.WriteLine("Self" + s)
        | LitExpr l -> tw.WriteLine(this.Lit l)
        | Call c ->
            tw.WriteLine("Call" + s)

            this.Prop "callee"
            this.Expr c.Callee

            for arg in c.Arg do
                this.Prop "arg"
                this.Expr arg

        | As a ->
            tw.WriteLine("As" + s)

            this.Prop "value"
            this.Expr a.Value

            this.Prop "type"
            this.Type a.Ty

        | Unary u ->
            tw.WriteLine("Unary" + s)

            this.Prop "op"
            tw.WriteLine u.Op.ToString

            this.Prop "value"
            this.Expr u.Value

        | Assign a ->
            tw.WriteLine("Assign" + s)

            this.Prop "place"
            this.Expr a.Place

            this.Prop "op"

            match a.Op with
            | Some op -> tw.Write op.ToString
            | None -> ()

            tw.WriteLine "="

            this.Prop "value"
            this.Expr a.Value

        | Binary b ->
            tw.WriteLine("Binary" + s)

            this.Prop "left"
            this.Expr b.Left

            this.Prop "op"
            tw.WriteLine b.Op.ToString

            this.Prop "right"
            this.Expr b.Right

        | Field f ->
            tw.WriteLine("Field" + s)

            this.Prop "receiver"
            this.Expr f.Receiver

            this.Prop "field"
            this.Id f.Field

        | TupleAccess t ->
            tw.WriteLine("TupleAccess" + s)

            this.Prop "receiver"
            this.Expr t.Receiver

            this.Prop "field"
            let idx, s = t.Index
            tw.WriteLine $"{idx}{this.Span s}"

        | Index i ->
            tw.WriteLine("Index" + s)

            this.Prop "container"
            this.Expr i.Container

            this.Prop "index"
            this.Expr i.Index

        | Array a ->
            tw.WriteLine("Array" + s)

            for item in a.Ele do
                this.Indent()
                this.Expr item

        | ArrayRepeat a ->
            tw.WriteLine("Array" + s)

            this.Prop "ele"
            this.Expr a.Ele

            this.Prop "length"
            this.Expr a.Len

        | Tuple t ->
            tw.WriteLine("Tuple" + s)

            for item in t.Ele do
                this.Indent()
                this.Expr item

        | Range r ->
            tw.WriteLine("Range" + s)

            match r.From with
            | Some from ->
                this.Prop "from"
                this.Expr from
            | None -> ()

            this.Prop "exclusive"
            tw.WriteLine(string r.Exclusive)

            match r.To with
            | Some to_ ->
                this.Prop "to"
                this.Expr to_
            | None -> ()

        | StructLit stru ->
            tw.WriteLine("Struct" + s)

            this.Child "struct" stru.Struct.Span this.Path stru.Struct

            for f in stru.Field do
                this.Prop "field"

                level <- level + 1

                match f with
                | ShorthandField s -> this.Id s
                | KeyValueField k ->
                    tw.WriteLine("key value" + this.Span k.Span)

                    this.Prop "key"
                    this.Id k.Name

                    this.Prop "value"
                    this.Expr k.Value
                | RestField s ->
                    tw.WriteLine("rest" + this.Span s.Span)
                    this.Indent()
                    this.Expr s.Value

                level <- level - 1

        | Closure c ->
            tw.WriteLine("Closure" + s)

            for p in c.Param do
                this.Indent()
                tw.WriteLine("param" + this.Span p.Span)
                this.Param p

            match c.Ret with
            | Some r ->
                this.Prop "ret"
                this.Type r
            | None -> ()

            this.Prop "body"
            this.Expr c.Body

        | Path p ->
            tw.WriteLine("Path" + s)
            this.Path p

        | Break _ -> tw.WriteLine("Break" + s)
        | Continue _ -> tw.WriteLine("Continue" + s)
        | Return r ->
            tw.WriteLine("Return" + s)

            match r.Value with
            | Some v ->
                this.Prop "value"
                this.Expr v
            | None -> ()

        | TryReturn t ->
            tw.WriteLine("TryReturn" + s)
            this.Indent()
            this.Expr t.Base

        | Block b ->
            tw.WriteLine("Block" + s)
            this.Block b

        | If i ->
            tw.WriteLine("If" + s)

            this.Prop "cond"
            this.Cond i.Cond

            this.Child "then" i.Then.Span this.Block i.Then

            for e in i.ElseIf do
                this.Indent()
                tw.WriteLine("else if" + this.Span e.Span)

                level <- level + 1

                this.Prop "cond"
                this.Cond e.Cond

                this.Child "body" e.Block.Span this.Block e.Block

                level <- level - 1

            match i.Else with
            | Some e -> this.Child "else" e.Span this.Block e
            | None -> ()

        | Match m ->
            tw.WriteLine("Match" + s)

            this.Prop "value"
            this.Expr m.Value

            for b in m.Branch do
                this.Indent()
                tw.WriteLine("branch" + this.Span b.Span)

                level <- level + 1
                this.Prop "pat"
                this.Pat b.Pat

                match b.Guard with
                | None -> ()
                | Some g ->
                    this.Prop "guard"
                    this.Expr g

                this.Prop "expr"
                this.Expr b.Expr

                level <- level - 1

        | While w ->
            tw.WriteLine("While" + s)

            this.Prop "cond"
            this.Cond w.Cond

            this.Child "body" w.Body.Span this.Block w.Body

        | For f ->
            tw.WriteLine("For" + s)

            this.Prop "pat"
            this.Pat f.Pat

            this.Prop "iterator"
            this.Expr f.Iter

            this.Child "body" f.Body.Span this.Block f.Body

        level <- level - 1

    member this.Block(b: Block) =
        for s in b.Stmt do
            this.Indent()
            this.Stmt s

    member this.Stmt s =
        match s with
        | ExprStmt e -> this.Expr e
        | DeclStmt d -> this.Decl d

    member this.Decl(decl: Decl) =
        let s = this.Span decl.Span
        level <- level + 1

        let name (i: Id) =
            this.Prop "name"
            this.Id i

        let tyParam (param: TyParam[]) =
            for p in param do
                this.Child "type param" p.Span this.TyParam p

        let func (f: Fn) =
            name f.Name

            tyParam f.TyParam

            for p in f.Param do
                this.Indent()
                tw.WriteLine("param" + this.Span p.Span)
                this.Param p

            match f.Ret with
            | None -> ()
            | Some r ->
                this.Prop "ret"
                level <- level + 1
                this.Type r
                level <- level - 1

            this.Child "body" f.Body.Span this.Block f.Body

        match decl with
        | Let l ->
            tw.WriteLine("Let" + s)

            if l.Mut then
                this.Prop "mut"
                tw.WriteLine "true"

            this.Prop "pat"
            this.Pat l.Pat

            match l.Ty with
            | None -> ()
            | Some t ->
                this.Prop "type"
                this.Type t

            this.Prop "value"
            this.Expr l.Value

        | Const _ -> failwith "Not Implemented"
        | FnDecl f ->
            tw.WriteLine("Function" + s)
            func f

        | StructDecl stru ->
            tw.WriteLine("Struct" + s)

            name stru.Name

            tyParam stru.TyParam

            for p in stru.Field do
                this.Indent()
                tw.WriteLine("field" + this.Span p.Span)

                level <- level + 1
                this.Prop "visibility"
                tw.WriteLine p.Vis.ToString

                name p.Name

                this.Prop "type"
                this.Type p.Ty
                level <- level - 1

        | EnumDecl e ->
            tw.WriteLine("Enum" + s)

            name e.Name

            tyParam e.TyParam

            for v in e.Variant do
                this.Indent()
                tw.WriteLine("variant" + this.Span v.Span)

                level <- level + 1

                name v.Name

                match v.Tag with
                | Some v ->
                    this.Indent()
                    tw.WriteLine("tag" + this.Span v.Span)
                    level <- level + 1
                    this.Indent()
                    this.Expr v
                    level <- level - 1
                | None -> ()

                for p in v.Payload do
                    this.Prop "payload"
                    this.Type p

                level <- level - 1

        | TypeDecl t ->
            tw.WriteLine("Type" + s)

            name t.Name

            this.Child "type" t.Ty.Span this.Type t.Ty

        | Use u ->
            tw.WriteLine("Use" + s)

            match u.Prefix with
            | None -> ()
            | Some p ->
                this.Prop "prefix"
                tw.WriteLine p.ToString

            for s in u.Seg do
                this.Prop "seg"
                this.Id s

            let rec item i =
                this.Prop "item"
                let s = this.Span u.Item.Span

                match i with
                | UseAll _ -> tw.WriteLine("*" + s)
                | UseSelf _ -> tw.WriteLine("self" + s)
                | UseItem i -> tw.WriteLine(i.Sym + s)
                | UseMany(_, m) ->
                    tw.WriteLine("many item" + s)

                    level <- level + 1

                    for path in m do
                        for i in path.Seg do
                            this.Prop "seg"
                            this.Id i

                        item path.Item

                    level <- level - 1

            item u.Item

        | Trait t ->
            tw.WriteLine("Trait" + s)

            name t.Name

            tyParam t.TyParam

            for s in t.Super do
                this.Child "super" s.Span this.Path s

            for i in t.Item do
                this.Prop "item"

                let s = this.Span i.Span

                level <- level + 1

                match i.Decl with
                | TraitMethod m ->
                    tw.WriteLine("trait method" + s)

                    name m.Name

                    for p in m.Param do
                        this.Indent()
                        tw.WriteLine("param" + this.Span p.Span)
                        this.Param p

                    match m.Ret with
                    | None -> ()
                    | Some r ->
                        this.Prop "ret"
                        this.Type r

                    match m.Default with
                    | None -> ()
                    | Some f -> this.Child "body" f.Span this.Block f

                | TraitType t -> tw.WriteLine("trait type" + s)
                | TraitValue v -> tw.WriteLine("trait value" + s)

                level <- level - 1

        | Impl i ->
            tw.WriteLine("Impl" + s)

            tyParam i.TyParam

            match i.Trait with
            | None -> ()
            | Some t -> this.Child "trait" t.Span this.Path t

            this.Prop "type"
            this.Type i.Ty

            for i in i.Item do
                this.Prop "visibility"
                tw.WriteLine i.Vis.ToString

                this.Prop "item"

                let s = this.Span i.Span

                level <- level + 1

                match i.Item with
                | Method f ->
                    tw.WriteLine("method" + s)
                    func f

                | AssocType(_) -> failwith "Not Implemented"
                | AssocValue(_) -> failwith "Not Implemented"

                level <- level - 1

        level <- level - 1

    member this.ModuleItem(item: ModuleItem) =
        tw.WriteLine $"ModuleItem{this.Span item.Span}"

        tw.WriteLine("visibility: " + item.Vis.ToString)

        tw.Write "item: "
        this.Decl item.Decl

    member this.Module(m: Module) =
        tw.WriteLine $"Module{this.Span m.Span}"
        level <- level + 1

        for item in m.Item do
            this.Indent()
            this.ModuleItem item

        level <- level - 1

let dump (tw: TextWriter) (m: Module) =
    let d = Dump(tw)
    d.Module m
