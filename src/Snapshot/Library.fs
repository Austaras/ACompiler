module Snapshot

open System.IO
open System.Text

open Xunit
open DiffPlex
open Pastel

let shouldUpdate = System.Environment.GetEnvironmentVariable "UPDATE" = "1"

type Snapshot(suffix: string) =

    member _.ShouldMatch (transform: string -> string) path =
        let path = Path.GetFullPath path
        let content = File.ReadAllText(path)
        let actual = transform content

        let snap = Path.ChangeExtension(path, suffix)
        let snapExist = File.Exists snap

        if shouldUpdate || not snapExist then
            File.WriteAllText(snap, actual)

            Assert.True(true)
        else
            let expected = File.ReadAllText snap

            if actual <> expected then
                let diff = DiffBuilder.InlineDiffBuilder.Diff(expected, actual)
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

type SnapshotText(suffix: string, basePath: string) =

    member _.ShouldMatch text name = if shouldUpdate then true else false
