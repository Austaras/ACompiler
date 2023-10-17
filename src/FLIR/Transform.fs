module FLIR.Transform

open Common
open AST
open Semantic.Semantic

type TransForm(arch: Config.Arch) =

    let ptrSize = arch.PtrSize

    member internal this.ProcessPat(p: AST.Pat) = 123

    member internal this.ProcessExpr(e: AST.Expr) = 123

    member this.TransForm (m: AST.Module) (sema: SemanticInfo) = failwith "Not Implemented"
