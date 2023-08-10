module Config.Config

type Arch =
    | X86_64
    | AArch64
    | Wasm

    /// pointer width in byte
    member this.ptrSize =
        match this with
        | X86_64
        | AArch64 -> 8
        | Wasm -> 4

    member this.endian =
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
    | Debug
    | Release
