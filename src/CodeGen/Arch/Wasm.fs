module Codegen.Arch.Wasm

open System.Collections.Generic

open Optimize
open FLIR

type Type =
    | I32
    | I64
    | F32
    | F64

type Var = { Id: int; name: string }

type BinOp =
    | Add
    | Sub
    | Mul

type Instr =
    | LocalDecl of Var * Type
    | Const of uint64 * Type
    | LocalGet of Var
    | LocalSet of Var
    | Bin of BinOp
