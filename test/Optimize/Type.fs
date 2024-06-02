module FLIR.Tests.Type

open Xunit

open Common.Target
open Optimize.FLIR

let layout = X86_64.Layout

[<Fact>]
let Layout () =
    let ty = I1 |> TInt |> Array.replicate 9 |> TMany

    Assert.Equal(ty.Size layout, 9)

[<Fact>]
let ReLayout () =
    let ty = [| I1; I64; I32 |] |> Array.map TInt |> TMany

    Assert.Equal(ty.Size layout, 24)

    let ty = ty.OptLayout layout

    Assert.Equal(ty.Size layout, 16)
