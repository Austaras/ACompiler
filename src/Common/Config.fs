module Common.Config

type Optimization =
    { TailCall: bool
      LVN: bool
      SCCP: bool }

    static member Debug =
        { TailCall = false
          LVN = false
          SCCP = false }

    static member Release =
        { TailCall = true
          LVN = true
          SCCP = false }
