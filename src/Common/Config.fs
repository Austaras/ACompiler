module Common.Config

type Optimization =
    { TailCall: bool
      LVN: bool }

    static member Debug = { TailCall = false; LVN = false }

    static member Release = { TailCall = true; LVN = true }
