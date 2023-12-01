module Common.Target

type Endian =
    | LittleEndian
    | BigEndian

type Arch =
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

    static member X86_64 =
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

    static member AArch64 =
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

    static member Wasm =
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
