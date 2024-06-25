/// Local Value Numbering
module Optimize.Pass.LVN

open System.Collections.Generic

open Optimize.FLIR

let lvnImpl (b: Block) =
    let mutable num = 0
    let varTable = Dictionary()
    let valueTable = Dictionary()

    b

let lvn = transLocal lvnImpl
