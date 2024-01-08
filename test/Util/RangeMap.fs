module Util.Tests

open Xunit

open RangeMap

[<Fact>]
let Overlap () =
    let map = RangeMap()

    map.Add 1 10 0
    map.Add 20 30 1
    map.Add 15 16 2
    map.Add 19 19 3
    map.Add 10 20 4

    Assert.Equal(Some 4, map.GetPoint 15)
    Assert.Equal(Some 4, map.GetPoint 19)
    Assert.Equal(Some 1, map.Get 21 30)

    map.Add 9 21 5

    Assert.Equal(Some 5, map.Get 9 21)

[<Fact>]
let Sum () =
    let map = RangeMap()

    let sum a b =
        match b with
        | Some b -> a + b
        | None -> a

    map.Add 1 10 -1
    map.Add 20 30 1
    map.Add 15 16 2
    map.Add 18 18 3
    map.Change 10 20 (sum 4)

    Assert.Equal(Some -1, map.Get 1 9)
    Assert.Equal(Some 3, map.GetPoint 10)
    Assert.Equal(Some 4, map.Get 11 14)
    Assert.Equal(Some 6, map.Get 15 16)
    Assert.Equal(Some 4, map.GetPoint 17)
    Assert.Equal(Some 7, map.GetPoint 18)
    Assert.Equal(Some 4, map.GetPoint 19)
    Assert.Equal(Some 5, map.GetPoint 20)
    Assert.Equal(Some 1, map.Get 21 30)
