module FLIR.Type

open Common.Target

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
    | TRef of Type
    | TMany of Type[]

    member internal this.SizeAndAlign(arch: Arch) =
        match this with
        | TInt I1 -> 1, arch.I1Align
        | TInt I8 -> 1, arch.I8Align
        | TInt I32 -> 4, arch.I32Align
        | TFloat F32 -> 4, arch.F32Align
        | TInt I64 -> 8, arch.I64Align
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

type MonoMode =
    | MSize of int
    | MType of Type

type Location =
    | Static
    | Unambiguous
    | Automatic
    | Irregular
