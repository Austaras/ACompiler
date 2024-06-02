/// Local Value Numbering
module Optimize.Pass.LVN

open System.Collections.Generic

open Optimize.FLIR

let lvn (m: Module) =
    let mutable num = 0
    let varTable = Dictionary()
    let valueTable = Dictionary()

    m
