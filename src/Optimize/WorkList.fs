module Optimize.WorkList

open System.Collections.Generic

type WorkList<'T>(init: IEnumerable<'T>) =
    let list = ResizeArray<'T>(init)
    let mutable idx = 0
    let set = HashSet<'T>(init)

    member _.Add data =
        let inserted = set.Add data

        if inserted then
            list.Add data

        inserted

    member _.Contain data = set.Contains data

    member _.Next() =
        if idx < list.Count then
            let data = list[idx]
            set.Remove data |> ignore
            idx <- idx + 1
            Some data
        else
            None

    member _.ToSeq() =
        seq {
            while idx < list.Count do
                let data = list[idx]
                yield data
                set.Remove data |> ignore
                idx <- idx + 1
        }

    interface System.Collections.IEnumerable with

        member this.GetEnumerator() = this.ToSeq().GetEnumerator()

    interface IEnumerable<'T> with

        member this.GetEnumerator() = this.ToSeq().GetEnumerator()
