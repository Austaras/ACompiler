module FLIR.Type

open Common.Target
open Semantic

type Integer =
    | I1
    | I8
    | I32
    | I64

type Float =
    | F32
    | F64

type Function = { Param: Type[]; Ret: Type }

and Type =
    | TInt of Integer
    | TFloat of Float
    | TFn of Function
    | TRef
    | TSame of Type * uint64
    | TMany of Type[]

    static member Habitable (sema: Semantic.SemanticInfo) (ty: Semantic.Type) =
        let field (ty: seq<Semantic.Type>) =
            ty |> Seq.map (Type.Habitable sema) |> Seq.fold (*) 1

        match ty with
        | Semantic.TInt _
        | Semantic.TFloat _
        | Semantic.TChar
        | Semantic.TString -> 10000
        | Semantic.TBool -> 2
        | Semantic.TStruct a ->
            let stru = sema.Struct[a.Name]
            let inst (t: Semantic.Type) = t.Instantiate stru.Generic a.Generic

            stru.Field.Values |> Seq.map inst |> field

        | Semantic.TEnum a ->
            let enum = sema.Enum[a.Name]

            let variant (ty: Semantic.Type[]) =
                let mapTy (ty: Semantic.Type) = ty.Instantiate enum.Generic a.Generic

                ty |> Array.map mapTy |> field

            enum.Variant.Values |> Seq.map variant |> Seq.sum

        | Semantic.TTuple t -> field t
        | Semantic.TFn _ -> 10000
        | Semantic.TRef t
        | Semantic.TArray(t, _)
        | Semantic.TSlice t -> Type.Habitable sema t
        | Semantic.TNever -> 0
        | Semantic.TVar _
        | Semantic.TGen _ -> failwith "Type Variable should be substituted in previous pass"

    static member FromSema (semantic: Semantic.SemanticInfo) (layout: Layout) (ty: Semantic.Type) =
        let size =
            match layout.PtrSize with
            | 4 -> I32
            | 8 -> I64
            | _ -> failwith "Not Implemented"
            |> TInt

        match ty with
        | Semantic.TBool -> TInt I1
        | Semantic.TInt(_, Semantic.I8) -> TInt I8
        | Semantic.TInt(_, Semantic.I32) -> TInt I32
        | Semantic.TInt(_, Semantic.I64) -> TInt I64
        | Semantic.TInt(_, Semantic.ISize) -> size
        | Semantic.TFloat Semantic.F32 -> TFloat F32
        | Semantic.TFloat Semantic.F64 -> TFloat F64
        | Semantic.TChar -> TInt I32
        | Semantic.TRef _
        | Semantic.TFn _ -> TRef
        | Semantic.TSlice _
        | Semantic.TString -> TMany [| TRef; size |]
        | Semantic.TTuple t -> t |> Array.map (Type.FromSema semantic layout) |> TMany
        | Semantic.TArray(t, n) -> TSame(Type.FromSema semantic layout t, n)
        | Semantic.TStruct a ->
            let strukt = semantic.Struct[a.Name]

            let trans (ty: Semantic.Type) =
                ty.Instantiate strukt.Generic a.Generic |> Type.FromSema semantic layout

            strukt.Field.Values
            |> Seq.map trans
            |> Array.ofSeq
            |> TMany
            |> _.OptLayout(layout)
        | Semantic.TEnum e ->
            let enum = semantic.Enum[e.Name]
            failwith "Not Implemented"
        | Semantic.TNever
        | Semantic.TVar _
        | Semantic.TGen _ -> failwith "unreachable"

    member internal this.SizeAndAlign(layout: Layout) =
        match this with
        | TInt I1 -> 1, layout.I1Align
        | TInt I8 -> 1, layout.I8Align
        | TInt I32 -> 4, layout.I32Align
        | TInt I64 -> 8, layout.I64Align
        | TFloat F32 -> 4, layout.F32Align
        | TFloat F64 -> 8, layout.F64Align
        | TFn _
        | TRef -> layout.PtrSize, layout.PtrAlign
        | TSame(s, n) ->
            let size, align = s.SizeAndAlign layout

            size * int n, align
        | TMany ty ->
            let sum (size, align) (ty: Type) =
                let s, a = ty.SizeAndAlign layout

                let padding = if size % a = 0 then 0 else s - size % s

                let align = if a > align then a else align

                size + padding + s, align

            Array.fold sum (0, 0) ty

    member this.Size(layout: Layout) =
        let size, align = this.SizeAndAlign layout

        if size % align = 0 then
            size
        else
            (size / align + 1) * align

    member this.Align(layout: Layout) = snd (this.SizeAndAlign layout)

    member this.OptLayout(layout: Layout) =
        match this with
        | TMany t ->
            let t = t |> Array.sortByDescending _.Size(layout)

            TMany t
        | t -> t

    member this.ToString =
        match this with
        | TInt I1 -> "i1"
        | TInt I8 -> "i8"
        | TInt I32 -> "i32"
        | TInt I64 -> "i64"
        | TFloat F32 -> "f32"
        | TFloat F64 -> "f64"
        | TFn(_) -> "fn"
        | TRef -> "ptr"
        | TSame(t, n) -> $"[{t.ToString}; {n}]"
        | TMany t ->
            let t = t |> Array.map _.ToString |> String.concat ", "

            $"({t})"
