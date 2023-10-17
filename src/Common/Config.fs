module Common.Config

type Arch =
    | X86_64
    | AArch64
    | Wasm

    /// pointer width in byte
    member this.PtrSize =
        match this with
        | X86_64
        | AArch64 -> 8
        | Wasm -> 4

    member this.Align =
        match this with
        | X86_64 -> 8
        | AArch64 -> failwith "Not Implemented"
        | Wasm -> failwith "Not Implemented"

    member this.Endian =
        match this with
        | X86_64
        | AArch64
        | Wasm -> LittleEndian

and Endian =
    | LittleEndian
    | BigEndian

type OS =
    | Linux
    | MacOS
    | Unknown

type Optimization =
    { TailCall: bool }

    static member Debug = { TailCall = false }

    static member Releas = { TailCall = true }
