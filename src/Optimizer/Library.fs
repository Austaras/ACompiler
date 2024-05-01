module Optimizer.Optimizer

open Common
open FLIR

open LVN

let optimize (config: Config.Optimization) (arch: Target.Arch) (m: FLIR.Module) =
    let m = if config.LVN then lvn m else m

    m
