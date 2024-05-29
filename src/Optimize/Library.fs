module Optimize.Optimize

open Common
open Optimize.FLIR
open Optimize.Pass.LVN

let optimize (config: Config.Optimization) (arch: Target.Arch) (m: FLIR.Module) =
    let m = if config.LVN then lvn m else m

    m
