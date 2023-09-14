module Util.Util

let tryPickBack chooser (array: _[]) =
    let rec loop i =
        match chooser array[i] with
        | None -> if i = 0 then None else loop (i - 1)
        | res -> res

    loop (array.Length - 1)

type Either<'L, 'R> =
    | Left of 'L
    | Right of 'R
