module Common.Span

type Span =
    { First: int
      Last: int }

    static member dummy = { First = 0; Last = 0 }
    static member Make first last = { First = first; Last = last }

    member this.WithFirst first = { this with First = first.First }

    member this.WithLast last = { this with Last = last.Last }

    member this.ShrinkFirst i = { this with First = this.First + i }
    member this.ShrinkLast i = { this with Last = this.Last - i }

    member this.ExpandLast i = { this with Last = this.Last + i }

type Pos =
    { Line: int
      Column: int }

    static member FromSpan lines span =
        let rec fromSpan lines line column =
            if Array.length lines = 0 then
                failwith "not in lines"
            else if column < lines[0] then
                { Line = line; Column = column }
            else
                let newColumn = column - lines[0]

                if newColumn = 0 then
                    { Line = line + 1; Column = 0 }
                else
                    fromSpan lines[1..] (line + 1) newColumn

        fromSpan lines 0 span
