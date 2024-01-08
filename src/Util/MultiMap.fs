module Util.MultiMap

open System.Collections.Generic
open System.Linq

type MultiMap<'K, 'V when 'K: equality>(?comparer: IEqualityComparer<'K>) =

    let map =
        match comparer with
        | Some c -> Dictionary<'K, ResizeArray<'V>>(c)
        | None -> Dictionary<'K, ResizeArray<'V>>()

    member _.Add key value =
        if map.ContainsKey key then
            map[key].Add value
        else
            let arr = ResizeArray()
            arr.Add value
            map[key] <- arr

    member _.Get key =
        if map.ContainsKey key then Some(map[key].Last()) else None

    member _.GetAll key =
        if map.ContainsKey key then
            Some(map[key].ToArray())
        else
            None

    member _.Remove key = map.Remove key |> ignore

    interface System.Collections.IEnumerable with

        member _.GetEnumerator() = map.GetEnumerator()

    interface IEnumerable<KeyValuePair<'K, ResizeArray<'V>>> with

        member _.GetEnumerator() =
            let elems = List<_>(map.Count)

            for kvp in map do
                elems.Add(kvp)

            elems.GetEnumerator()

    member _.Values = map.Values
