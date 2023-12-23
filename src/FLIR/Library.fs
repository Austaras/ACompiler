module FLIR.FLIR

open Common.Span
open FLIR.Op
open FLIR.Type

type MonoMode =
    | MSize of int
    | MType of Type

type Location =
    | Static
    | Unambiguous
    | Automatic
    | Irregular

type Value =
    | Int of uint64
    | Binding

type Stm =
    | Load
    | Store
    | Bin
    | FNeg
    | Call
    | Alloc

    member this.Span = Span.dummy

type Transfer =
    | Jump
    | CJump
    | Ret

type Block =
    { Stm: Stm[]
      Trans: Transfer
      Link: int[]
      Span: Span }

type Func =
    { Block: Block[]
      Param: Type[]
      Var: Type[]
      Span: Span }

type Module = { Func: Func[]; Static: int[] }
