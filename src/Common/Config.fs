module Common.Config

type Optimization =
    { TailCall: bool
      LVN: bool
      DCE: bool
      SCCP: bool }

    static member Debug =
        { TailCall = false
          LVN = false
          DCE = false
          SCCP = false }

    static member Release =
        { TailCall = true
          LVN = true
          DCE = true
          SCCP = true }
