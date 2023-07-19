module Util.BiMap

open System.Collections.Generic

type BiMap<'V1, 'V2 when 'V1: equality and 'V2: equality>() =
    let l2r = Dictionary<'V1, 'V2>()
    let r2l = Dictionary<'V2, 'V1>()

    member this.GetByLeft(key: 'V1) = l2r[key]

    member this.GetByRight(key: 'V2) = r2l[key]

    member this.Add (key: 'V1) (value: 'V2) =
        l2r[key] <- value
        r2l[value] <- key
