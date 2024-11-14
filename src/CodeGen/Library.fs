module CodeGen.CodeGen

open Common.Span
open Optimize.FLIR

let deSSA (f: Func) =
    let block = f.Block

    for idx in 0 .. block.Length - 1 do
        let phi = block[idx].Phi

        if phi.Count > 0 then
            for KeyValue(varId, value) in phi do
                for (pred, value) in Array.zip f.CFG[idx].Pred value do
                    block[pred] <-
                        { block[pred] with
                            Instr =
                                Array.append
                                    block[pred].Instr
                                    [| Assign
                                           { Target = varId
                                             Value = value
                                             Span = Span.dummy } |] }

    { f with Block = block }
