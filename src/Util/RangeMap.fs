module Util.RangeMap

open System.Linq

[<StructuralEquality; CustomComparison>]
type internal RangeMapNode<'value> =
    { first: int
      last: int
      value: 'value }

    interface System.IComparable<RangeMapNode<'value>> with
        member this.CompareTo other = compare this.first other.first

type RangeMap<'value>() =
    let set = System.Collections.Generic.SortedSet<RangeMapNode<'value>>()

    member internal this.SplitAt i toRight =
        let left =
            set.GetViewBetween(
                { first = -1
                  last = 0
                  value = Unchecked.defaultof<'value> },
                { first = i
                  last = 0
                  value = Unchecked.defaultof<'value> }
            )

        if left.Count > 0 then
            let left = left.Max

            if left.last >= i then
                if left.last > left.first then
                    set.Remove left |> ignore

                    if toRight then
                        set.Add { left with last = i - 1 } |> ignore
                        set.Add { left with first = i } |> ignore
                    else
                        set.Add { left with last = i } |> ignore
                        set.Add { left with first = i + 1 } |> ignore

    member this.Remove first last =
        this.SplitAt first true
        this.SplitAt last false

        let middle =
            set.GetViewBetween(
                { first = first
                  last = 0
                  value = Unchecked.defaultof<'value> },
                { first = last
                  last = 0
                  value = Unchecked.defaultof<'value> }
            )

        middle.Clear()

    member this.Add first last value =
        this.Remove first last

        set.Add
            { first = first
              last = last
              value = value }
        |> ignore

    member this.Change first last mapper =
        this.SplitAt first true
        this.SplitAt last false

        let middle =
            set.GetViewBetween(
                { first = first
                  last = 0
                  value = Unchecked.defaultof<'value> },
                { first = last
                  last = 0
                  value = Unchecked.defaultof<'value> }
            )

        if middle.Count = 0 then
            set.Add
                { first = first
                  last = last
                  value = mapper None }
            |> ignore
        else
            let arr = middle.ToArray()

            if first < arr[0].first then
                set.Add
                    { first = first
                      last = arr[0].first - 1
                      value = mapper None }
                |> ignore

            for (idx, range) in Array.indexed arr do
                set.Remove range |> ignore

                set.Add
                    { range with
                        value = mapper (Some range.value) }
                |> ignore

                if idx + 1 < arr.Length && range.last < arr[idx + 1].first then
                    set.Add
                        { first = range.last + 1
                          last = arr[idx + 1].first - 1
                          value = mapper None }
                    |> ignore

            if last > (Array.last arr).last then
                set.Add
                    { first = (Array.last arr).last + 1
                      last = last
                      value = mapper None }
                |> ignore

    member this.Get first last =
        let left =
            set.GetViewBetween(
                { first = -1
                  last = 0
                  value = Unchecked.defaultof<'value> },
                { first = first
                  last = 0
                  value = Unchecked.defaultof<'value> }
            )

        if left.Count > 0 then
            let left = left.Max

            if left.last >= last then Some left.value else None
        else
            None

    member this.AddPoint key value = this.Add key key value

    member this.GetPoint key = this.Get key key

    member this.ToSeq =
        seq {
            let mutable i = set.GetEnumerator()

            while i.MoveNext() do
                yield i.Current
        }
        |> Seq.map (fun s -> s.first, s.last, s.value)
