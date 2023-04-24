// TODO: table driven lexer
module Lexer.Lexer

open AST

type Pair =
    | Open
    | Close

type Delimiter =
    | CR
    | LF
    | Semi

type Reserved =
    | IF
    | ELSE
    | MATCH
    | FOR
    | WHILE
    | CONTINUE
    | BREAK
    | RETURN
    | FN
    | LET
    | MUT
    | TYPE
    | TRAIT
    | IMPL
    | USE
    | PUB

type CommentKind =
    | SingleLine
    | MultiLine

type TokenData =
    | Paren of Pair
    | Curly of Pair
    | Colon
    | ColonColon
    | Tilde
    | Comma
    | Arrow
    | FatArrow
    | Dot
    | DotDot
    | DotDotEq
    | Delimiter of Delimiter
    | Lit of AST.Lit
    | Operator of string
    | Identifier of string
    | Reserved of Reserved
    | Comment of CommentKind * string

type Token =
    { data: TokenData
      span: AST.Span }

    static member make data span = { data = data; span = span }

let internal parseIdentifier input =
    match input with
    | "if" -> Reserved IF
    | "else" -> Reserved ELSE
    | "match" -> Reserved MATCH
    | "for" -> Reserved FOR
    | "while" -> Reserved WHILE
    | "continue" -> Reserved CONTINUE
    | "break" -> Reserved BREAK
    | "fn" -> Reserved FN
    | "return" -> Reserved RETURN
    | "let" -> Reserved LET
    | "mut" -> Reserved MUT
    | "type" -> Reserved TYPE
    | "trait" -> Reserved TRAIT
    | "impl" -> Reserved IMPL
    | "use" -> Reserved USE
    | "pub" -> Reserved PUB
    | "true" -> Lit(AST.Bool true)
    | "false" -> Lit(AST.Bool false)
    | str -> Identifier str

let unescapeStr = System.Text.RegularExpressions.Regex.Unescape

let internal operator_arr =
    [| '<'; '='; '>'; '&'; '|'; '+'; '-'; '*'; '/'; '%'; '!' |]

let internal is_operator c = Array.contains c operator_arr

let is_id_start c = c = '_' || System.Char.IsAsciiLetter c

let is_id_continue c =
    is_id_start c || System.Char.IsAsciiDigit c

type internal State =
    { i: int
      data: Token[]
      error: (AST.Span * string)[] }

let lex (input: string) =
    let len = input.Length

    let rec lex state =
        let i = state.i

        let punc p =
            let token = Token.make p (AST.Span.make state.i state.i)

            let new_state =
                { state with
                    i = i + 1
                    data = Array.append state.data [| token |] }

            lex new_state

        let delimiter kind =
            let token = Token.make (Delimiter kind) (AST.Span.make state.i state.i)

            let state =
                { state with
                    i = i + 1
                    data = Array.append state.data [| token |] }

            lex state

        let rec parse_int alphabet i =
            let rec skip_when i =
                if i = len then
                    i
                else if Array.contains input[i] alphabet || input[i] = '_' then
                    skip_when (i + 1)
                else
                    i

            let j = skip_when i

            if alphabet.Length <> 10 || j = len then
                j
            else if input[j] = '.' then
                parse_dec (j + 1)
            else if input[j] = 'e' || input[j] = 'E' then
                parse_exp (j + 1)
            else
                j

        and parse_dec i =
            let rec skip_when j =
                if j = len then
                    j
                else if System.Char.IsAsciiDigit input[j] then
                    skip_when (j + 1)
                else if j <> i && input[j] = '_' then
                    skip_when (j + 1)
                else
                    j

            let j = skip_when i

            if j = len || (input[j] <> 'e' && input[j] <> 'E') then
                j
            else
                parse_exp (j + 1)

        and parse_exp i =
            if i = len then
                i
            else
                let i = if input[i] = '+' || input[i] = '-' then i + 1 else i

                let rec skip_when j =
                    if j = len then
                        j
                    else if System.Char.IsAsciiDigit input[j] then
                        skip_when (j + 1)
                    else if j <> i && input[j] = '_' then
                        skip_when (j + 1)
                    else
                        j

                skip_when i

        if i = input.Length then
            if state.error.Length = 0 then
                Ok state.data
            else
                Error state.error

        else
            match input[i] with
            | '(' -> punc (Paren Open)
            | ')' -> punc (Paren Close)
            | '{' -> punc (Curly Open)
            | '}' -> punc (Curly Close)
            | '~' -> punc Tilde
            | ',' -> punc Comma
            | ';' -> delimiter Semi
            | '\n' -> delimiter CR
            | '\r' -> delimiter LF
            | ':' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = ':' then
                        ColonColon, i + 2
                    else
                        Colon, i + 1

                let span = AST.Span.make i (j - 1)

                let state =
                    { state with
                        i = j
                        data = Array.append state.data [| Token.make token span |] }

                lex state

            | '.' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = '.' then
                        if i + 2 < len && input[i + 2] = '=' then
                            DotDotEq, i + 3
                        else
                            DotDot, i + 2
                    else if i + 1 < len && System.Char.IsAsciiDigit input[i + 1] then
                        let j = parse_dec (i + 1)
                        let str = input[i .. (j - 1)]

                        Lit(AST.Float(float str)), j
                    else
                        Dot, i + 1

                let span = AST.Span.make i (j - 1)

                let state =
                    { state with
                        i = j
                        data = Array.append state.data [| Token.make token span |] }

                lex state

            | ' '
            | '\t' ->
                let rec skip_when i =
                    if i = len then
                        i
                    else if input[i] = ' ' || input[i] = '\t' then
                        skip_when (i + 1)
                    else
                        i

                lex { state with i = skip_when (i + 1) }

            | '/' when i < len && input[i + 1] = '/' ->
                let rec skip_when i =
                    if i = len || input[i] = '\n' || input[i] = '\r' then
                        i
                    else
                        skip_when (i + 1)

                let j = skip_when (i + 1)
                let token = Comment(SingleLine, input[i .. (j - 1)])
                let span = AST.Span.make i (j - 1)

                let state =
                    { state with
                        i = j
                        data = Array.append state.data [| Token.make token span |] }

                lex state

            | '/' when i < len && input[i + 1] = '*' ->
                let rec skip_when i =
                    if i = len then
                        Error i
                    else if i < len - 1 && input[i] = '*' && input[i + 1] = '/' then
                        Ok(i + 2)
                    else
                        skip_when (i + 1)

                let j = skip_when (i + 1)

                match j with
                | Ok j ->
                    let token = Comment(SingleLine, input[i .. (j - 1)])
                    let span = AST.Span.make i (j - 1)

                    let state =
                        { state with
                            i = j
                            data = Array.append state.data [| Token.make token span |] }

                    lex state
                | Error j ->
                    let error =
                        Array.append
                            state.error
                            [| AST.Span.make i (j - 1), "incomplete mulitline comment at the end of file" |]

                    Error error

            | '"' ->
                let rec take_when i =
                    if i = len then
                        Error i
                    else if input[i] = '\\' then
                        if i = len - 1 then Error i else take_when (i + 2)
                    else if input[i] = '"' then
                        Ok(i + 1)
                    else
                        take_when (i + 1)

                let j = take_when (i + 1)

                match j with
                | Error j ->
                    let error =
                        Array.append
                            state.error
                            [| AST.Span.make j j, "incomplete escape sequence at the end of file" |]

                    Error error
                | Ok j ->
                    let token = unescapeStr input[(i + 1) .. (j - 2)] |> AST.String |> Lit
                    let span = AST.Span.make i (j - 1)

                    let state =
                        { state with
                            i = j
                            data = Array.append state.data [| Token.make token span |] }

                    lex state
            | ''' ->
                let rec take_when i =
                    if i = len then
                        Error i
                    else if input[i] = '\\' then
                        if i = len - 1 then Error i else take_when (i + 2)
                    else if input[i] = ''' then
                        Ok(i + 1)
                    else
                        take_when (i + 1)

                let j = take_when (i + 1)

                match j with
                | Error j ->
                    let error =
                        Array.append
                            state.error
                            [| AST.Span.make j j, "incomplete escape sequence at the end of file" |]

                    Error error
                | Ok j ->
                    let str = unescapeStr input[(i + 1) .. (j - 2)]
                    let span = AST.Span.make i (j - 1)

                    let state =
                        match str.Length with
                        | 0 ->
                            { state with
                                i = j
                                error = Array.append state.error [| span, "char can not be empty" |] }
                        | 1 ->
                            let token = Lit(AST.Char str[0])

                            { state with
                                i = j
                                data = Array.append state.data [| Token.make token span |] }

                        | _ ->
                            { state with
                                i = j
                                error = Array.append state.error [| span, "char can only contain one character" |] }

                    lex state

            | c when is_operator c ->
                let rec take_when i =
                    if i = len then i
                    else if is_operator input[i] then take_when (i + 1)
                    else i

                let token, j =
                    if i + 1 < len then
                        let two = input[i .. (i + 1)]

                        match two with
                        | "->" -> Arrow, i + 2
                        | "=>" -> FatArrow, i + 2
                        | _ ->
                            let j = take_when (i + 1)
                            Operator input[i .. (j - 1)], j
                    else
                        let j = take_when (i + 1)
                        Operator input[i .. (j - 1)], j

                let span = AST.Span.make i (j - 1)

                let state =
                    { state with
                        i = j
                        data = Array.append state.data [| Token.make token span |] }

                lex state

            | c when is_id_start c ->
                let rec take_when i =
                    if i = len then i
                    else if is_id_continue input[i] then take_when (i + 1)
                    else i

                let i = state.i
                let j = take_when (i + 1)
                let token = parseIdentifier input[i .. (j - 1)]
                let span = AST.Span.make i (j - 1)

                let state =
                    { state with
                        i = j
                        data = Array.append state.data [| Token.make token span |] }

                lex state

            | c when System.Char.IsAsciiDigit c ->
                let alphabet, new_i =
                    if c = '0' && i + 1 < len then
                        match input[i + 1] with
                        | 'b'
                        | 'B' -> Ok(seq { '0' .. '1' }), i + 2
                        | 'o'
                        | 'O' -> Ok(seq { '0' .. '8' }), i + 2
                        | 'x'
                        | 'X' -> Ok(Seq.concat [ seq { '0' .. '9' }; seq { 'a' .. 'f' }; seq { 'A' .. 'F' } ]), i + 2
                        | c when System.Char.IsAsciiDigit c || c = '_' || c = '.' -> Ok(seq { '0' .. '9' }), i + 1
                        | c -> Error c, i + 2

                    else
                        Ok(seq { '0' .. '9' }), i + 1

                match alphabet with
                | Ok a ->
                    let alphabet = Seq.toArray a

                    let j = if new_i = len then new_i else parse_int alphabet new_i
                    let str = input[i .. (j - 1)]

                    if str.EndsWith 'e' || str.EndsWith 'E' then
                        let state =
                            { state with
                                i = j
                                error = Array.append state.error [| AST.Span.make i (j - 1), "missing exponent" |] }

                        lex state
                    else
                        let token, j =
                            if str.EndsWith '.' && j < len && (is_id_start input[j] || input[j] = '.') then
                                let token = Lit(AST.Int(uint str[.. (str.Length - 2)]))

                                token, j - 1
                            else
                                let token =
                                    if
                                        str.Contains '.'
                                        || (not (str.StartsWith "0x") && str.Contains "e" || str.Contains "E")
                                    then
                                        Lit(AST.Float(float str))
                                    else
                                        Lit(AST.Int(uint str))


                                token, j

                        let span = AST.Span.make i (j - 1)

                        let state =
                            { state with
                                i = j
                                data = Array.append state.data [| Token.make token span |] }

                        lex state
                | Error c ->
                    let state =
                        { state with
                            i = i + 2
                            error =
                                Array.append
                                    state.error
                                    [| AST.Span.make i (i + 1), $"unknown number literal prefix {c}" |] }

                    lex state

            | _ ->
                let i = state.i

                let error =
                    Array.append state.error [| AST.Span.make i i, "unrecognizable pattern" |]

                Error error

    lex { i = 0; data = [||]; error = [||] }
