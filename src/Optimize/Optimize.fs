module Optimize.Optimize

open Common.Config
open Optimize.Pass

let optimize (config: Optimization) (m: FLIR.Module) =
    let m = if config.DCE then DCE.dce m else m
    let m = if config.LVN then LVN.lvn m else m
    let m = if config.SCCP then SCCP.sccp m else m

    m
