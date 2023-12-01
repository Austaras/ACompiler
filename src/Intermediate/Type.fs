module Intermediate.Type

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
    | TMany of Type[]

    member internal this.SizeAndAlign(arch: Arch) =
        match this with
        | TInt I1 -> 1, arch.I1Align
        | TInt I8 -> 1, arch.I8Align
        | TInt I32 -> 4, arch.I32Align
        | TFloat F32 -> 4, arch.F32Align
        | TInt I64 -> 8, arch.I64Align
        | TInt I128 -> 16, arch.I64Align
        | TFloat F64 -> 8, arch.F64Align
        | TFn _
        | TRef _ -> arch.PtrSize, arch.PtrAlign
        | TMany ty ->
            let sum (size, align) (ty: Type) =
                let s, a = ty.SizeAndAlign arch

                let padding = if size % a = 0 then 0 else s - size % s

                let align = if a > align then a else align

                size + padding + s, align

            Array.fold sum (0, 0) ty

    member this.Size(arch: Arch) =
        let size, align = this.SizeAndAlign arch

        if size % align = 0 then
            size
        else
            (size / align + 1) * align

    member this.Align(arch: Arch) = snd (this.SizeAndAlign arch)

    member this.OptLayout(arch: Arch) =
        match this with
        | TMany t ->
            let t = t |> Array.sortByDescending _.Size(arch)

            TMany t
        | t -> t

    static member FromTy (semantic: Semantic.SemanticInfo) (arch: Arch) (ty: Semantic.Type) =
        match ty with
        | Semantic.TBool -> TInt I1
        | Semantic.TInt(_, Semantic.I8) -> TInt I8
        | Semantic.TInt(_, Semantic.I32) -> TInt I32
        | Semantic.TInt(_, Semantic.I64) -> TInt I64
        | Semantic.TInt(_, Semantic.ISize) ->
            match arch.PtrSize with
            | 4 -> I32
            | 8 -> I64
            | _ -> failwith "Not Implemented"
            |> TInt
        | Semantic.TFloat Semantic.F32 -> TFloat F32
        | Semantic.TFloat Semantic.F64 -> TFloat F64
        | Semantic.TChar -> TInt I128
        | Semantic.TRef t -> TRef(Type.FromTy semantic arch t)
        | Semantic.TFn f -> failwith "Not Implemented"
        | Semantic.TTuple t -> t |> Array.map (Type.FromTy semantic arch) |> TMany
        | Semantic.TStruct(s, p) ->
            let strukt = semantic.Struct[s]
            failwith "Not Implemented"
        | Semantic.TEnum(e, p) ->
            let enum = semantic.Enum[e]
            failwith "Not Implemented"
        | Semantic.TNever
        | Semantic.TVar _ -> failwith "unreachable"
