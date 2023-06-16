module Config.Config

type Arch =
    | X64
    | AArch64
    | Wasm

    /// pointer width in byte
    member this.ptrSize =
        match this with
        | X64
        | AArch64 -> 8
        | Wasm -> 4

type OS =
    | Linux
    | MacOS
    | Unknown

type Optimization =
    | Debug
    | Release
