module FLIR.Transform

open Common
open AST
open Semantic
open FLIR.Type
open FLIR.FLIR

let transform (arch: Target.Arch) (m: AST.Module) (sema: Semantic.SemanticInfo) =
    let layout = arch.Layout

    let processPat (p: AST.Pat) = 123

    let processExpr (e: AST.Expr) = 123

    let processFn (f: AST.Fn) =
        let var = ResizeArray()

        let fnTy =
            match sema.Var[f.Name] with
            | Semantic.TFn f -> f
            | _ -> failwith "Unreachable"

        if fnTy.TVar.Length > 0 then
            failwith "Not Implemented"

        let param = fnTy.Param |> Array.map (Type.FromSema sema layout)

        { Block = [||]
          Var = Array.ofSeq var
          Param = param
          Span = f.Span }

    let func = ResizeArray()

    for item in m.Item do
        match item.Decl with
        | AST.Use _ -> ()
        | AST.Let l -> ()
        | AST.Const c -> ()
        | AST.FnDecl f -> func.Add(processFn f)
        | AST.StructDecl _
        | AST.EnumDecl _
        | AST.TypeDecl _ -> ()
        | AST.Impl impl -> ()
        | AST.Trait t -> ()

    { Func = Array.ofSeq func
      Static = [||] }
