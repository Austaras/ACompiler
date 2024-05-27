module Util.Util

let pick chooser (array: ResizeArray<_>) =
    let rec loop i =
        if i = array.Count then
            None
        else
            match chooser array[i] with
            | None -> loop (i + 1)
            | res -> res

    loop 0

let pickBack chooser (array: ResizeArray<_>) =
    let rec loop i =
        if i = 0 then
            None
        else
            match chooser array[i - 1] with
            | None -> loop (i - 1)
            | res -> res

    loop array.Count

type Either<'L, 'R> =
    | Left of 'L
    | Right of 'R

let dictToMap (dict: System.Collections.Generic.Dictionary<'a, 'b>) =
    dict |> Seq.map (|KeyValue|) |> Map.ofSeq
