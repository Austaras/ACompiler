// TODO: table driven lexer
module Lexer.Lexer

open System.Globalization
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
    | IN
    | WHILE
    | CONTINUE
    | BREAK
    | RETURN
    | FN
    | LET
    | MUT
    | CONST
    | TYPE
    | TRAIT
    | IMPL
    | USE
    | PUB
    | DYN
    | WITH

type CommentKind =
    | SingleLine
    | MultiLine

type TokenData =
    | Paren of Pair
    | Bracket of Pair
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
    | Not
    | Eq
    | Binary of AST.BinaryOp
    | Assign of AST.ArithmeticOp
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
    | "in" -> Reserved IN
    | "while" -> Reserved WHILE
    | "continue" -> Reserved CONTINUE
    | "break" -> Reserved BREAK
    | "fn" -> Reserved FN
    | "return" -> Reserved RETURN
    | "let" -> Reserved LET
    | "mut" -> Reserved MUT
    | "const" -> Reserved CONST
    | "type" -> Reserved TYPE
    | "trait" -> Reserved TRAIT
    | "impl" -> Reserved IMPL
    | "use" -> Reserved USE
    | "pub" -> Reserved PUB
    | "dyn" -> Reserved DYN
    | "with" -> Reserved WITH
    | "true" -> Lit(AST.Bool true)
    | "false" -> Lit(AST.Bool false)
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

let internal is_id_start c = c = '_' || letter c

let internal is_id_continue c =
    is_id_start c
    || match System.Char.GetUnicodeCategory c with
       | UnicodeCategory.DecimalDigitNumber
       | UnicodeCategory.ConnectorPunctuation
       | UnicodeCategory.NonSpacingMark
       | UnicodeCategory.SpacingCombiningMark
       | UnicodeCategory.Format -> true
       | _ -> false

type internal State =
    { i: int
      data: Token[]
      error: (AST.Span * string)[] }

let lex (input: string) =
    let len = input.Length

    let rec lex state =
        let i = state.i

        let with_new_token token j =
            let span = AST.Span.make i (j - 1)

            let new_state =
                { state with
                    i = j
                    data = Array.append state.data [| Token.make token span |] }

            lex new_state

        let with_new_error error j =
            let span = AST.Span.make i (j - 1)

            let new_state =
                { state with
                    i = j
                    error = Array.append state.error [| span, error |] }

            lex new_state

        let punc p = with_new_token p (i + 1)

        let delimiter kind = with_new_token (Delimiter kind) (i + 1)

        let maybe_assign op =
            let token, j =
                if i + 1 < len && input[i + 1] = '=' then
                    Assign op, i + 2
                else
                    Binary(AST.Arithmetic op), i + 1

            with_new_token token j

        let maybe_assign_or_double char op double =
            let token, j =
                if i + 2 < len && input[i + 1] = char && input[i + 2] = '=' then
                    Assign double, i + 3
                else if i + 1 < len && input[i + 1] = char then
                    Binary(AST.Arithmetic double), i + 2
                else if i + 1 < len && input[i + 1] = '=' then
                    Assign op, i + 2
                else
                    Binary(AST.Arithmetic op), i + 1

            with_new_token token j

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
                Ok j
            else if input[j] = '.' then
                parse_dec (j + 1)
            else if input[j] = 'e' || input[j] = 'E' then
                parse_exp (j + 1)
            else
                Ok j

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
                Ok j
            else
                parse_exp (j + 1)

        and parse_exp i =
            if i = len then
                Error(i, "missing exponent")
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

                if i = len then
                    Error(i, "missing exponent")
                else
                    Ok(skip_when i)

        if i = input.Length then
            if state.error.Length = 0 then
                Ok state.data
            else
                Error state.error

        else
            match input[i] with
            | '(' -> punc (Paren Open)
            | ')' -> punc (Paren Close)
            | '[' -> punc (Bracket Open)
            | ']' -> punc (Bracket Close)
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

                with_new_token token j

            | '.' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = '.' then
                        if i + 2 < len && input[i + 2] = '=' then
                            Ok DotDotEq, i + 3
                        else
                            Ok DotDot, i + 2
                    else if i + 1 < len && System.Char.IsAsciiDigit input[i + 1] then
                        let j = parse_dec (i + 1)

                        match j with
                        | Ok j ->
                            let str = input[i .. (j - 1)]

                            Ok(Lit(AST.Float(float str))), j
                        | Error(j, msg) -> Error msg, j
                    else
                        Ok Dot, i + 1

                match token with
                | Ok token -> with_new_token token j
                | Error msg -> with_new_error msg j

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

            | '=' ->
                let token, j =
                    if i + 1 < len then
                        match input[i + 1] with
                        | '>' -> FatArrow, i + 2
                        | '=' -> Binary(AST.EqEq), i + 2
                        | _ -> Eq, i + 1
                    else
                        Eq, i + 1

                with_new_token token j

            | '!' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = '=' then
                        Binary(AST.NotEq), i + 2
                    else
                        Not, i + 1

                with_new_token token j

            | '+' -> maybe_assign AST.Add
            | '%' -> maybe_assign AST.Mod
            | '^' -> maybe_assign AST.BitXor

            | '*' -> maybe_assign_or_double '*' AST.Mul AST.Pow

            | '-' ->
                if i + 1 < len && input[i + 1] = '>' then
                    with_new_token Arrow (i + 2)
                else
                    maybe_assign AST.Sub

            | '&' -> maybe_assign_or_double '&' AST.BitAnd AST.LogicalAnd

            | '|' ->
                if i + 1 < len && input[i + 1] = '>' then
                    with_new_token (Binary AST.Pipe) (i + 2)
                else
                    maybe_assign_or_double '|' AST.BitOr AST.LogicalOr

            | '>' ->
                let token, j =
                    if i + 2 < len && input[i + 1] = '>' && input[i + 2] = '=' then
                        Assign AST.Shr, i + 3
                    else if i + 1 < len && input[i + 1] = '>' then
                        Binary(AST.Arithmetic AST.Shr), i + 2
                    else if i + 1 < len && input[i + 1] = '=' then
                        Binary(AST.GtEq), i + 2
                    else
                        Binary(AST.Gt), i + 1

                with_new_token token j

            | '<' ->
                let token, j =
                    if i + 2 < len && input[i + 1] = '<' && input[i + 2] = '=' then
                        Assign AST.Shl, i + 3
                    else if i + 1 < len && input[i + 1] = '<' then
                        Binary(AST.Arithmetic AST.Shl), i + 1
                    else if i + 1 < len && input[i + 1] = '=' then
                        Binary(AST.LtEq), i + 2
                    else
                        Binary(AST.Lt), i + 1

                with_new_token token j

            | '/' ->
                let data, j =
                    if i + 1 < len then
                        match input[i + 1] with
                        | '/' ->
                            let rec take_when i =
                                if i = len || input[i] = '\n' || input[i] = '\r' then
                                    i
                                else
                                    take_when (i + 1)

                            let j = take_when (i + 1)
                            let token = Comment(SingleLine, input[(i + 2) .. (j - 1)])

                            Ok token, j
                        | '*' ->
                            let rec take_when j =
                                if j = len then
                                    Error "incomplete mulitline comment at the end of file", j
                                else if j + 1 < len && input[j] = '*' && input[j + 1] = '/' then
                                    let token = Comment(MultiLine, input[(i + 2) .. (j - 1)])
                                    Ok token, j + 2
                                else
                                    take_when (j + 1)

                            take_when (i + 1)
                        | '=' -> Ok(Assign(AST.Div)), i + 2
                        | _ -> Ok(Binary(AST.Arithmetic AST.Div)), i + 1
                    else
                        Ok(Binary(AST.Arithmetic AST.Div)), i + 1

                match data with
                | Ok token -> with_new_token token j
                | Error msg -> with_new_error msg j

            | '"' ->
                let rec take_when i =
                    if i = len then
                        Error(i, "unmatched double quote")
                    else if input[i] = '\\' then
                        if i = len - 1 then
                            Error(i, "incomplete escape sequence at the end of file")
                        else
                            take_when (i + 2)
                    else if input[i] = '"' then
                        Ok(i + 1)
                    else
                        take_when (i + 1)

                let j = take_when (i + 1)

                match j with
                | Error(j, msg) ->
                    let error = Array.append state.error [| AST.Span.make j j, msg |]

                    Error error
                | Ok j ->
                    let token = unescapeStr input[(i + 1) .. (j - 2)] |> AST.String |> Lit
                    with_new_token token j
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

                    match str.Length with
                    | 0 -> with_new_error "char can not be empty" j
                    | 1 ->
                        let token = Lit(AST.Char str[0])

                        with_new_token token j

                    | _ -> with_new_error "char can only contain one character" j

            | c when is_id_start c ->
                let rec take_when i =
                    if i = len then i
                    else if is_id_continue input[i] then take_when (i + 1)
                    else i

                let j = take_when (i + 1)
                let token = parseIdentifier input[i .. (j - 1)]
                with_new_token token j

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
                        | c when System.Char.IsAsciiDigit c || c = '_' || c = '.' || c = 'e' || c = 'E' ->
                            Ok(seq { '0' .. '9' }), i + 1
                        | c -> Error c, i + 2

                    else
                        Ok(seq { '0' .. '9' }), i + 1

                match alphabet with
                | Ok a ->
                    let alphabet = Seq.toArray a

                    let j =
                        if new_i = len then
                            if alphabet.Length <> 10 then
                                Error(new_i, "missing number content")
                            else
                                Ok new_i
                        else
                            parse_int alphabet new_i

                    match j with
                    | Ok j ->
                        let str = input[i .. (j - 1)]

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

                        with_new_token token j
                    | Error(j, msg) -> with_new_error msg j

                | Error c -> with_new_error $"unknown number literal prefix {c}" (i + 2)

            | _ ->
                let error =
                    Array.append state.error [| AST.Span.make i i, "unrecognizable pattern" |]

                Error error

    lex { i = 0; data = [||]; error = [||] }
