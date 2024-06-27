module Common.WorkList

open System.Collections.Generic

type WorkList<'T>(init: IEnumerable<'T>) =
    let list = ResizeArray<'T>(init)
    let set = HashSet<'T>(init)

    member _.Add data =
        if not (set.Contains data) then
            list.Add data
            set.Add data |> ignore

    member _.ToSeq() =
        seq {
            let mutable idx = 0

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
