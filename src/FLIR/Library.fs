module FLIR.FLIR

open Config
open AST
open Semantic.Type

open FLIR.Type

type BinOp =
    { ty: Integer
      fst: AST.Id
      snd: AST.Id }

type FLIR = And of BinOp

let transformAST (arch: Config.Arch) (ast: AST.Module) (ty: Type.Symbol) = failwith "Not Implemented"
