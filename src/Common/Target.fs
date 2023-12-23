module Common.Target

type Endian =
    | LittleEndian
    | BigEndian

type Layout =
    { PtrSize: int
      I1Align: int
      I8Align: int
      I32Align: int
      I64Align: int
      I128Align: int
      F32Align: int
      F64Align: int
      PtrAlign: int
      Endian: Endian }

type Arch =
    | X86_64
    | AArch64
    | RiscV64
    | Wasm

    member this.Layout =
        match this with
        | X86_64 ->
            { PtrSize = 8
              Endian = LittleEndian
              I1Align = 1
              I8Align = 1
              I32Align = 4
              I64Align = 8
              I128Align = 8
              F32Align = 4
              F64Align = 8
              PtrAlign = 8 }

        | AArch64 ->
            { PtrSize = 8
              Endian = LittleEndian
              I1Align = 1
              I8Align = 1
              I32Align = 4
              I64Align = 8
              I128Align = 8
              F32Align = 4
              F64Align = 8
              PtrAlign = 8 }

        | RiscV64 -> failwith "123"

        | Wasm ->
            { PtrSize = 4
              Endian = LittleEndian
              I1Align = 1
              I8Align = 1
              I32Align = 4
              I64Align = 8
              I128Align = 8
              F32Align = 4
              F64Align = 8
              PtrAlign = 4 }

type OS =
    | Linux
    | MacOS
    | Unknown
