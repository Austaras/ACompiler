module ATIR.Transform

open Common.Span
open Common.Target
open AST
open Semantic
open Intermediate.Op
open ATIR.ATIR

type internal IdGen() =
    let mutable tempId = 0
    let mutable labelId = 0

    member _.GenTemp =
        let id = tempId
        tempId <- tempId + 1

        { Id = id; Span = Span.dummy }

    member _.GenLabel =
        let id = labelId
        labelId <- labelId + 1

        { Name = None
          Id = id
          Span = Span.dummy }

type internal ExpRes =
    | Ex of Exp
    | Nx of Stm
    | Cx of (Label -> Label -> Stm)

    member this.ToEx(gen: IdGen) =
        match this with
        | Ex e -> e
        | Nx n ->
            ESeq
                { Stm = n
                  Exp = Const { Value = 0; Span = Span.dummy }
                  Span = n.Span }
        | Cx c ->
            let r = gen.GenTemp
            let t = gen.GenLabel
            let f = gen.GenLabel
            let c = c t f

            ESeq
                { Stm =
                    Seq
                        { Fst =
                            Move
                                { From = Const { Value = 1; Span = Span.dummy }
                                  To = Temp r
                                  Span = Span.dummy }
                          Snd =
                            Seq
                                { Fst = c
                                  Snd =
                                    Seq
                                        { Fst = Label f
                                          Snd =
                                            Seq
                                                { Fst =
                                                    Move
                                                        { From = Const { Value = 0; Span = Span.dummy }
                                                          To = Temp r
                                                          Span = Span.dummy }
                                                  Snd = Label t
                                                  Span = Span.dummy }
                                          Span = Span.dummy }
                                  Span = c.Span }
                          Span = c.Span }
                  Exp = Temp r
                  Span = c.Span }

    member this.ToNx(gen: IdGen) =
        match this with
        | Ex e -> Exp e
        | Nx n -> n
        | Cx c ->
            let t = gen.GenLabel
            let f = gen.GenLabel
            c t f

    member this.ToCx(gen: IdGen) =
        match this with
        | Ex(Const { Value = 0; Span = span }) ->
            fun t f ->
                Jump
                    { To = Name f
                      Label = [| f |]
                      Span = span }
        | Ex(Const { Value = 1; Span = span }) ->
            fun t f ->
                Jump
                    { To = Name t
                      Label = [| f |]
                      Span = span }
        | Ex e ->
            fun t f ->
                CJump
                    { Left = e
                      Op = Eq
                      Right = Const { Value = 1; Span = Span.dummy }
                      TLabel = t
                      FLabel = f
                      Span = e.Span }
        | Nx _ -> failwith "Unreachable"
        | Cx c -> c

let transform (arch: Arch) (sema: Semantic.SemanticInfo) (ast: AST.Module) =

    let transformExp (exp: AST.Expr) = 456

    123
