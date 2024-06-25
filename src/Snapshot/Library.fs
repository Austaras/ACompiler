module Snapshot

open System.IO
open System.Text

open Xunit
open DiffPlex
open Pastel

let shouldUpdate = System.Environment.GetEnvironmentVariable "UPDATE" = "1"

let shouldMatch (actual: TextWriter -> unit) snap =
    let snapExist = File.Exists snap

    if shouldUpdate || not snapExist then
        use sw = new StreamWriter(snap, false)
        actual (sw)
        Assert.True(true)
    else
        use tw = new StringWriter()
        actual tw
        let actual = tw.ToString()

        let expected = File.ReadAllText snap

        if actual <> expected then
            let diff = DiffBuilder.InlineDiffBuilder.Diff(expected, actual, false)
            let msg = StringBuilder().AppendLine("Failed to match snapshot:")
            let mutable offset = 0

            for (idx, line) in diff.Lines |> Seq.indexed do
                let sign, color =
                    match line.Type with
                    | DiffBuilder.Model.ChangeType.Deleted -> "-", System.ConsoleColor.Red
                    | DiffBuilder.Model.ChangeType.Inserted ->
                        offset <- offset + 1
                        "+", System.ConsoleColor.Green
                    | _ -> " ", System.ConsoleColor.White

                let idx = idx + 1 - offset
                let lineNumber = string idx
                let lineNumber = String.replicate (5 - lineNumber.Length) " " + lineNumber + "| "

                let text = sign + lineNumber + line.Text
                let text = text.Pastel color

                msg.AppendLine(text) |> ignore

            Assert.Fail(msg.ToString())

type Snapshot(name: string) =

    member _.ShouldMatch (text: TextWriter -> unit) (path: string) =

        let snap = Path.GetDirectoryName(path) + "/" + name

        shouldMatch text snap

type TextSnapshot(suffix: string, basePath: string) =

    member _.ShouldMatch (text: TextWriter -> unit) path =
        let path = basePath + path
        let snap = Path.ChangeExtension(path, suffix)

        shouldMatch text snap
