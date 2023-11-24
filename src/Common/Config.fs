module Common.Config

type Optimization =
    { TailCall: bool }

    static member Debug = { TailCall = false }

    static member Releas = { TailCall = true }
