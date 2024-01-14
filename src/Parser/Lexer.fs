module Parser.Lexer

open System.Globalization

open Common.Span
open AST
open Parser.Common

let internal classify input =
    match input with
    | "if" -> Reserved IF
    | "else" -> Reserved ELSE
    | "match" -> Reserved MATCH
    | "for" -> Reserved FOR
    | "in" -> Reserved IN
    | "while" -> Reserved WHILE
    | "continue" -> Reserved CONTINUE
    | "break" -> Reserved BREAK
    | "fn" -> Reserved FUNCTION
    | "return" -> Reserved RETURN
    | "let" -> Reserved LET
    | "mut" -> Reserved MUTABLE
    | "const" -> Reserved CONST
    | "type" -> Reserved TYPE
    | "struct" -> Reserved STRUCT
    | "enum" -> Reserved ENUM
    | "trait" -> Reserved TRAIT
    | "impl" -> Reserved IMPL
    | "use" -> Reserved USE
    | "pub" -> Reserved PUBLIC
    | "intl" -> Reserved INTERNAL
    | "Self" -> Reserved SELF
    | "self" -> Reserved LOWSELF
    | "pak" -> Reserved PACKAGE
    | "as" -> Reserved AS
    | "true" -> Lit(AST.Bool true)
    | "false" -> Lit(AST.Bool false)
    | "NaN" -> Lit(AST.Float nan)
    | "Infinity" -> Lit(AST.Float infinity)
    | "_" -> Underline
    | str -> Identifier str

let internal unescapeStr = System.Text.RegularExpressions.Regex.Unescape

let internal letter c =
    match System.Char.GetUnicodeCategory c with
    | UnicodeCategory.UppercaseLetter
    | UnicodeCategory.LowercaseLetter
    | UnicodeCategory.TitlecaseLetter
    | UnicodeCategory.ModifierLetter
    | UnicodeCategory.OtherLetter
    | UnicodeCategory.LetterNumber -> true
    | _ -> false

let internal isIdStart c = c = '_' || letter c

let internal isIdContinue c =
    isIdStart c
    || match System.Char.GetUnicodeCategory c with
       | UnicodeCategory.DecimalDigitNumber
       | UnicodeCategory.ConnectorPunctuation
       | UnicodeCategory.NonSpacingMark
       | UnicodeCategory.SpacingCombiningMark
       | UnicodeCategory.Format -> true
       | _ -> false

type internal Lexer(input: string, error: ResizeArray<Error>) =
    let len = input.Length

    let mutable pos = 0

    let mutable prevToken = None

    member _.Len = len

    member _.Token data j =
        let span = Span.Make pos j
        pos <- j + 1
        { Data = data; Span = span }

    member this.Single p = this.Token p pos

    // TODO: use table
    // TODO: parse int and float
    member this.Int alphabet i =
        let mutable j = i

        while j < len && (Array.contains input[j] alphabet || input[j] = '_') do
            j <- j + 1

        if alphabet.Length <> 10 || j = len then
            j - 1
        else if input[j] = '.' then
            this.Dec(j + 1)
        else if input[j] = 'e' || input[j] = 'E' then
            this.Exp(j + 1)
        else
            j - 1

    member this.Dec start =
        let mutable j = start

        while j < len && (System.Char.IsAsciiDigit input[j] || (j <> pos && input[j] = '_')) do
            j <- j + 1

        if j = len || (input[j] <> 'e' && input[j] <> 'E') then
            j - 1
        else
            this.Exp(j + 1)

    member _.Exp start =
        if start = len then
            raise (ParserExp(MissingExpContent(Span.Make pos (start - 1))))
        else
            let start =
                if input[start] = '+' || input[start] = '-' then
                    start + 1
                else
                    start

            let rec takeWhen j =
                if j = len then
                    j
                else if System.Char.IsAsciiDigit input[j] then
                    takeWhen (j + 1)
                else if j <> pos && input[j] = '_' then
                    takeWhen (j + 1)
                else
                    j

            if start = len then
                raise (ParserExp(MissingExpContent(Span.Make pos (start - 1))))
            else
                takeWhen start

    member this.MayAssign op =
        let token, j =
            if pos + 1 < len && input[pos + 1] = '=' then
                AssignOp op, pos + 1
            else
                Operator(AST.Arith op), pos

        this.Token token j

    member this.NextInner needOp =
        match input[pos] with
        | ';' -> this.Single(Delimiter Semi)
        | '\n' -> this.Single(Delimiter CR)
        | '\r' -> this.Single(Delimiter LF)

        | '(' -> this.Single(Open Paren)
        | ')' -> this.Single(Close Paren)
        | '[' -> this.Single(Open Bracket)
        | ']' -> this.Single(Close Bracket)
        | '{' -> this.Single(Open Curly)
        | '}' -> this.Single(Close Curly)
        | '~' -> this.Single Tilde
        | ',' -> this.Single Comma
        | '?' -> this.Single Question
        | ':' ->
            let token, j =
                if pos + 1 < len && input[pos + 1] = ':' then
                    ColonColon, pos + 1
                else
                    Colon, pos

            this.Token token j

        | '.' ->
            let token, j =
                if pos + 1 < len && input[pos + 1] = '.' then
                    if pos + 2 < len && input[pos + 2] = '^' then
                        DotDotCaret, pos + 2
                    else
                        DotDot, pos + 1
                else if pos + 1 < len && System.Char.IsAsciiDigit input[pos + 1] then
                    let j = this.Dec(pos + 1)

                    let str = input[pos..j]

                    Lit(AST.Float(float str)), j
                else
                    Dot, pos

            this.Token token j

        | '=' ->
            let token, j =
                if pos + 1 < len then
                    match input[pos + 1] with
                    | '>' -> FatArrow, pos + 1
                    | '=' -> Operator(AST.Cmp AST.EqEq), pos + 1
                    | _ -> Eq, pos
                else
                    Eq, pos

            this.Token token j

        | '!' ->
            let token, j =
                if pos + 1 < len && input[pos + 1] = '=' then
                    Operator(AST.Cmp AST.NotEq), pos + 1
                else
                    Not, pos

            this.Token token j

        | '+' -> this.MayAssign AST.Add
        | '%' -> this.MayAssign AST.Rem
        | '^' -> this.MayAssign AST.BitXor

        | '*' -> this.MayAssign AST.Mul

        | '-' ->
            if pos + 1 < len && input[pos + 1] = '>' then
                this.Token Arrow (pos + 1)
            else
                this.MayAssign AST.Sub

        | '&' ->
            if not needOp then
                this.Single(Operator(AST.Arith AST.BitAnd))
            else if pos + 1 < len && input[pos + 1] = '&' then
                this.Token (Operator(AST.Logic AST.And)) (pos + 1)
            else
                this.MayAssign AST.BitAnd

        | '|' ->
            if not needOp then
                this.Single(Operator(AST.Arith AST.BitOr))
            else if pos + 1 < len && input[pos + 1] = '>' then
                this.Token (Operator AST.Pipe) (pos + 1)
            else if pos + 1 < len && input[pos + 1] = '|' then
                this.Token (Operator(AST.Logic AST.Or)) (pos + 1)
            else
                this.MayAssign AST.BitOr

        | '>' ->
            let token, j =
                if not needOp then
                    Operator(AST.Cmp AST.Gt), pos
                else if pos + 2 < len && input[pos + 1] = '>' && input[pos + 2] = '=' then
                    AssignOp AST.Shr, pos + 2
                else if pos + 1 < len && input[pos + 1] = '>' then
                    Operator(AST.Arith AST.Shr), pos + 1
                else if pos + 1 < len && input[pos + 1] = '=' then
                    Operator(AST.Cmp AST.GtEq), pos + 1
                else
                    Operator(AST.Cmp AST.Gt), pos

            this.Token token j

        | '<' ->
            let token, j =
                if pos + 2 < len && input[pos + 1] = '<' && input[pos + 2] = '=' then
                    AssignOp AST.Shl, pos + 2
                else if pos + 1 < len && input[pos + 1] = '<' then
                    Operator(AST.Arith AST.Shl), pos + 1
                else if pos + 1 < len && input[pos + 1] = '=' then
                    Operator(AST.Cmp AST.LtEq), pos + 1
                else
                    Operator(AST.Cmp AST.Lt), pos

            this.Token token j

        | '/' ->
            let data, j =
                if pos + 1 < len then
                    match input[pos + 1] with
                    | '/' ->
                        let rec takeWhen i =
                            if i = len || input[i] = '\n' || input[i] = '\r' then
                                i
                            else
                                takeWhen (i + 1)

                        let j = takeWhen (pos + 1)
                        let token = Comment(SingleLine, input[(pos + 2) .. (j - 1)])

                        token, j - 1
                    | '*' ->
                        let rec takeWhen j =
                            if j = len then
                                raise (ParserExp(IncompleteMultilineComment(Span.Make pos (j - 1))))
                            else if j + 1 < len && input[j] = '*' && input[j + 1] = '/' then
                                let token = Comment(MultiLine, input[pos .. (j + 1)])
                                token, j + 1
                            else
                                takeWhen (j + 1)

                        takeWhen (pos + 1)
                    | '=' -> AssignOp(AST.Div), pos + 1
                    | _ -> Operator(AST.Arith AST.Div), pos
                else
                    Operator(AST.Arith AST.Div), pos

            this.Token data j
        | '"' ->
            let rec takeWhen j =
                if j = len then
                    raise (ParserExp(Unmatched(Span.Make pos (j - 1), '"')))
                else if input[j] = '\\' then
                    if j = len - 1 then
                        raise (ParserExp(IncompleteEscapeSeq(Span.Make pos j)))
                    else
                        takeWhen (j + 2)
                else if input[j] = '"' then
                    j
                else
                    takeWhen (j + 1)

            let j = takeWhen (pos + 1)

            let token = unescapeStr input[(pos + 1) .. (j - 1)] |> AST.String |> Lit
            this.Token token j

        | ''' ->
            let rec takeWhen i =
                if i = len then
                    raise (ParserExp(Unmatched(Span.Make i i, ''')))
                else if input[i] = '\\' then
                    if i = len - 1 then
                        raise (ParserExp(IncompleteEscapeSeq(Span.Make i i)))
                    else
                        takeWhen (i + 2)
                else if input[i] = ''' then
                    i
                else
                    takeWhen (i + 1)

            let j = takeWhen (pos + 1)
            let str = unescapeStr input[(pos + 1) .. (j - 1)]

            match str.Length with
            | 0 ->
                error.Add(CharEmpty(Span.Make pos j))

                this.Token (Lit(AST.Char ' ')) j
            | 1 ->
                let token = Lit(AST.Char str[0])

                this.Token token j

            | _ ->
                error.Add(CharTooMany(Span.Make pos j))

                let token = Lit(AST.Char str[0])

                this.Token token j

        | c when isIdStart c ->
            let rec takeWhen i =
                if i = len then i - 1
                else if isIdContinue input[i] then takeWhen (i + 1)
                else i - 1

            let j = takeWhen (pos + 1)
            let token = classify input[pos..j]
            this.Token token j

        | c when System.Char.IsAsciiDigit c ->
            let alphabet, newI =
                if c = '0' && pos + 1 < len then
                    match input[pos + 1] with
                    | 'b'
                    | 'B' -> seq { '0' .. '1' }, pos + 2
                    | 'o'
                    | 'O' -> seq { '0' .. '8' }, pos + 2
                    | 'x'
                    | 'X' -> Seq.concat [ seq { '0' .. '9' }; seq { 'a' .. 'f' }; seq { 'A' .. 'F' } ], pos + 2
                    | _ -> seq { '0' .. '9' }, pos

                else
                    seq { '0' .. '9' }, pos

            let alphabet = Seq.toArray alphabet

            let j =
                if newI = len then
                    if alphabet.Length <> 10 then
                        raise (ParserExp(MissingIntContent(Span.Make pos (newI - 1))))

                    newI
                else
                    this.Int alphabet newI

            let str = input[pos..j]

            let token, j =
                if str.EndsWith '.' && j < len - 1 && (isIdStart input[j] || input[j] = '.') then
                    let token = Lit(AST.Int(uint64 str[.. (str.Length - 2)]))

                    token, j - 1
                else
                    let token =
                        if
                            str.Contains '.'
                            || (not (str.StartsWith "0x") && str.Contains "e" || str.Contains "E")
                        then
                            Lit(AST.Float(float str))
                        else
                            Lit(AST.Int(uint64 str))

                    token, j

            this.Token token j

        | c -> raise (ParserExp(UnrecognizablePattern(Span.Make pos pos, c)))

    member _.WhiteSpace() =
        while pos < len && (input[pos] = ' ' || input[pos] = '\t') do
            pos <- pos + 1

    member this.Next() =
        match prevToken with
        | Some t ->
            prevToken <- None
            Some t
        | None ->
            this.WhiteSpace()

            if pos = len then None else this.NextInner false |> Some

    member this.Read error =
        match prevToken with
        | Some t ->
            prevToken <- None
            t
        | None ->
            let rec read () =
                this.WhiteSpace()

                if pos = len then
                    raise (ParserExp(IncompleteAtEnd error))
                else
                    match this.NextInner false with
                    | { Data = Comment _ | Delimiter(CR | LF) } -> read ()
                    | token -> token

            read ()

    member this.Expect token error =
        match this.Read error with
        | { Data = data; Span = span } when data = token -> span
        | token -> raise (ParserExp(UnexpectedToken(token, error)))

    member this.ReadId error : AST.Id =
        match this.Read error with
        | { Data = Identifier sym; Span = span } -> { Sym = sym; Span = span }
        | token -> raise (ParserExp(UnexpectedToken(token, error)))

    member _.Consume() = prevToken <- None

    // the 1 of LL(1)
    member this.Peek() =
        match prevToken with
        | Some t -> Some t
        | None ->
            let rec peek () =
                match this.Next() with
                | None -> None
                | Some({ Data = Comment _ | Delimiter(CR | LF) }) -> peek ()
                | Some t -> Some t

            let last = peek ()

            prevToken <- last

            last

    member this.PeekInline() =
        match prevToken with
        | Some t -> Some t
        | None ->
            let rec peek () =
                match this.Next() with
                | None -> None
                | Some({ Data = Comment _ }) -> peek ()
                | Some t -> Some t

            let last = peek ()

            prevToken <- last

            last

    member this.PeekOp() =
        match prevToken with
        | Some t ->
            match t.Data with
            | Operator(AST.Cmp AST.Gt) when pos < len ->
                match input[pos] with
                | '=' ->
                    let token =
                        { Data = Operator(AST.Cmp AST.GtEq)
                          Span = t.Span.ExpandLast 1 }

                    pos <- pos + 1
                    prevToken <- Some token
                    Some token

                | '>' ->
                    let token =
                        if pos + 1 < len && input[pos + 1] = '=' then
                            pos <- pos + 2

                            { Data = AssignOp AST.Shr
                              Span = t.Span.ExpandLast 2 }
                        else
                            pos <- pos + 1

                            { Data = Operator(AST.Arith AST.Shr)
                              Span = t.Span.ExpandLast 1 }

                    prevToken <- Some token
                    Some token
                | _ -> Some t

            | Operator(AST.Arith AST.BitAnd) when pos < len ->
                match input[pos] with
                | '=' ->
                    let token =
                        { Data = AssignOp AST.BitAnd
                          Span = t.Span.ExpandLast 1 }

                    pos <- pos + 1
                    prevToken <- Some token
                    Some token

                | '&' ->
                    let token =
                        { Data = Operator(AST.Logic AST.And)
                          Span = t.Span.ExpandLast 1 }

                    pos <- pos + 1
                    prevToken <- Some token
                    Some token
                | _ -> Some t

            | Operator(AST.Arith AST.BitOr) when pos < len ->
                match input[pos] with
                | '=' ->
                    let token =
                        { Data = AssignOp AST.BitOr
                          Span = t.Span.ExpandLast 1 }

                    pos <- pos + 1
                    prevToken <- Some token
                    Some token

                | '|' ->
                    let token =
                        { Data = Operator(AST.Logic AST.Or)
                          Span = t.Span.ExpandLast 1 }

                    pos <- pos + 1
                    prevToken <- Some token
                    Some token
                | _ -> Some t
            | _ -> Some t
        | None ->
            let rec peek () =

                this.WhiteSpace()

                if pos = len then
                    None
                else
                    match this.NextInner true with
                    | { Data = Comment _ } -> peek ()
                    | t -> Some t

            let last = peek ()

            prevToken <- last

            last

    member this.PeekPost() =
        match prevToken with
        | Some t -> Some t
        | None ->
            let rec peek () =
                this.WhiteSpace()

                if pos = len then
                    None
                else
                    match input[pos] with
                    | '.' when pos = len - 1 || input[pos + 1] <> '.' -> this.Single Dot |> Some
                    | _ ->
                        match this.NextInner false with
                        | { Data = Comment _ } -> peek ()
                        | token -> Some token

            let last = peek ()

            prevToken <- last

            last

    /// only for tests
    member this.AllToken() =
        let res = ResizeArray()
        this.WhiteSpace()

        while pos < len do
            let token = this.NextInner true
            res.Add token
            this.WhiteSpace()

        res.ToArray(), error.ToArray()
