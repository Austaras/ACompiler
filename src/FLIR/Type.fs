module FLIR.Type

open Common.Target
open Semantic

type Integer =
    | I1
    | I8
    | I32
    | I64
    | I128

type Float =
    | F32
    | F64

type Function = { Param: Type[]; Ret: Type }

and Type =
    | TInt of Integer
    | TFloat of Float
    | TFn of Function
    | TRef of Type
    | TSame of Type * int
    | TMany of Type[]

    member internal this.SizeAndAlign(layout: Layout) =
        match this with
        | TInt I1 -> 1, layout.I1Align
        | TInt I8 -> 1, layout.I8Align
        | TInt I32 -> 4, layout.I32Align
        | TFloat F32 -> 4, layout.F32Align
        | TInt I64 -> 8, layout.I64Align
        | TInt I128 -> 16, layout.I64Align
        | TFloat F64 -> 8, layout.F64Align
        | TFn _
        | TRef _ -> layout.PtrSize, layout.PtrAlign
        | TSame(s, n) ->
            let size, align = s.SizeAndAlign layout

            size * n, align
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

    static member FromSema (semantic: Semantic.SemanticInfo) (layout: Layout) (ty: Semantic.Type) =
        match ty with
        | Semantic.TBool -> TInt I1
        | Semantic.TInt(_, Semantic.I8) -> TInt I8
        | Semantic.TInt(_, Semantic.I32) -> TInt I32
        | Semantic.TInt(_, Semantic.I64) -> TInt I64
        | Semantic.TInt(_, Semantic.ISize) ->
            match layout.PtrSize with
            | 4 -> I32
            | 8 -> I64
            | _ -> failwith "Not Implemented"
            |> TInt
        | Semantic.TFloat Semantic.F32 -> TFloat F32
        | Semantic.TFloat Semantic.F64 -> TFloat F64
        | Semantic.TChar -> TInt I128
        | Semantic.TRef t -> TRef(Type.FromSema semantic layout t)
        | Semantic.TFn f -> failwith "Not Implemented"
        | Semantic.TTuple t -> t |> Array.map (Type.FromSema semantic layout) |> TMany
        | Semantic.TStruct(s, p) ->
            let strukt = semantic.Struct[s]

            let trans (ty: Semantic.Type) =
                ty.Instantiate strukt.TVar p |> Type.FromSema semantic layout

            strukt.Field.Values |> Seq.map trans |> Array.ofSeq |> TMany
        | Semantic.TEnum(e, p) ->
            let enum = semantic.Enum[e]
            failwith "Not Implemented"
        | Semantic.TNever
        | Semantic.TVar _ -> failwith "unreachable"
