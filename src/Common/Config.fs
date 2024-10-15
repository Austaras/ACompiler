module Common.Config

type DCE =
    | DDebug
    | DRelease
    | DAgressive

type Optimization =
    { TailCall: bool
      LVN: bool
      DCE: DCE
      SCCP: bool }

    static member Debug =
        { TailCall = false
          LVN = false
          DCE = DDebug
          SCCP = false }

    static member Release =
        { TailCall = true
          LVN = true
          DCE = DRelease
          SCCP = true }

    static member Aggressive =
        { TailCall = true
          LVN = true
          DCE = DAgressive
          SCCP = true }
