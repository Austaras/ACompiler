module FLIR.Tests.Type

open Xunit

open IR.Type

let arch = Common.Target.Arch.X86_64

[<Fact>]
let Layout () =
    let ty = I1 |> TInt |> Array.replicate 9 |> TMany

    Assert.Equal(ty.Size arch, 9)

[<Fact>]
let ReLayout () =
    let ty = [| I1; I64; I32 |] |> Array.map TInt |> TMany

    Assert.Equal(ty.Size arch, 24)

    let ty = ty.OptLayout arch

    Assert.Equal(ty.Size arch, 16)

// [<Fact>]
// let Niche () =
//     let ty = TMany [| TInt I1; TRef(TInt I64); |]

//     Assert.Equal(ty.Size arch, 8)
