module FLIR.FLIR

open Config
open AST
open Semantic.Semantic

open FLIR.Type

type BinOp =
    | Add
    | Sub
    | Mul
    | Div
    | Rem
    | BitXor
    | BitAnd
    | BitOr
    | Shl
    | Shr
    | Eq
    | Lt
    | LtEq
    | NotEq
    | GtEq
    | Gt

type Bin =
    { ty: Integer
      op: BinOp
      fst: AST.Id
      snd: AST.Id }

type FLIR = Bin of Bin

let transformAST (arch: Config.Arch) (ast: AST.Module) (ty: SemanticInfo) = failwith "Not Implemented"
