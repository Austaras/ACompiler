module Util.Util

let pick chooser (array: ResizeArray<_>) =
    let rec loop i =
        match chooser array[i] with
        | None -> if i = array.Count - 1 then None else loop (i + 1)
        | res -> res

    loop 0

let pickBack chooser (array: ResizeArray<_>) =
    let rec loop i =
        match chooser array[i] with
        | None -> if i = 0 then None else loop (i - 1)
        | res -> res

    loop (array.Count - 1)

type Either<'L, 'R> =
    | Left of 'L
    | Right of 'R

let dictToMap (dict: System.Collections.Generic.Dictionary<'a, 'b>) =
    dict |> Seq.map (|KeyValue|) |> Map.ofSeq
