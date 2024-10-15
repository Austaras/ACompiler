module Optimize.Optimize

open Common.Config
open Optimize.Pass

let optimize (config: Optimization) (m: FLIR.Module) =
    let m = DCE.dce (config.DCE = DDebug) m
    let m = if config.LVN then LVN.lvn m else m
    let m = if config.SCCP then SCCP.sccp m else m
    let m = if config.DCE = DAgressive then ADCE.adce m else m

    m
