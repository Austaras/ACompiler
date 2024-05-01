/// Local Value Numbering
module Optimizer.LVN

open System.Collections.Generic

open FLIR.FLIR

let lvn (m: Module) =
    let mutable num = 0
    let varTable = Dictionary()
    let valueTable = Dictionary()

    m
