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
    | FUNCTION
    | LET
    | MUTABLE
    | CONST
    | TYPE
    | TRAIT
    | IMPL
    | USE
    | PUBLIC
    | INTERNAL
    | WITH
    | STRUCT
    | ENUM
    | SELF
    | LOWSELF
    | PACKAGE

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
    | DotDotCaret
    | Delimiter of Delimiter
    | Lit of AST.Lit
    | Not
    | Eq
    | Question
    | Operator of AST.BinaryOp
    | AssignOp of AST.ArithmeticOp
    | Identifier of string
    | Reserved of Reserved
    | Comment of CommentKind * string

type Token =
    { data: TokenData
      span: AST.Span }

    static member Make data span = { data = data; span = span }

type Error =
    | IncompleteExp of AST.Span
    | IncompleteEscapeSeq of AST.Span
    | IncompleteMultilineComment of AST.Span
    | UnrecognizablePattern of AST.Span * char
    | Unmatched of AST.Span * char
    | MissingIntContent of AST.Span
    | MissingExpContent of AST.Span
    | CharEmpty of AST.Span
    | CharTooMany of AST.Span
    | UnknownNumberPrefix of AST.Span * char

let internal parseIdentifier input =
    match input with
    | "if" -> Reserved IF
    | "else" -> Reserved ELSE
    | "match" -> Reserved MATCH
    | "for" -> Reserved FOR
    | "in" -> Reserved IN
    | "while" -> Reserved WHILE
    | "cnt" -> Reserved CONTINUE
    | "break" -> Reserved BREAK
    | "fn" -> Reserved FUNCTION
    | "ret" -> Reserved RETURN
    | "let" -> Reserved LET
    | "mut" -> Reserved MUTABLE
    | "const" -> Reserved CONST
    | "type" -> Reserved TYPE
    | "trait" -> Reserved TRAIT
    | "impl" -> Reserved IMPL
    | "use" -> Reserved USE
    | "pub" -> Reserved PUBLIC
    | "intl" -> Reserved INTERNAL
    | "with" -> Reserved WITH
    | "Self" -> Reserved SELF
    | "self" -> Reserved LOWSELF
    | "pak" -> Reserved PACKAGE
    | "as" -> Operator AST.As
    | "true" -> Lit(AST.Bool true)
    | "false" -> Lit(AST.Bool false)
    | "NaN" -> Lit(AST.Float nan)
    | "Infinity" -> Lit(AST.Float infinity)
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

type internal State =
    { i: int
      data: Token[]
      error: Error[] }

let lex (input: string) =
    let len = input.Length

    let rec lex state =
        let i = state.i

        let withNewToken token j =
            let span = AST.Span.Make i (j - 1)

            let newState =
                { state with
                    i = j
                    data = Array.append state.data [| Token.Make token span |] }

            lex newState

        let withNewError error j =
            let span = AST.Span.Make i (j - 1)

            let newState =
                { state with
                    i = j
                    error = Array.append state.error [| error span |] }

            lex newState

        let punc p = withNewToken p (i + 1)

        let delimiter kind = withNewToken (Delimiter kind) (i + 1)

        let maybeAssign op =
            let token, j =
                if i + 1 < len && input[i + 1] = '=' then
                    AssignOp op, i + 2
                else
                    Operator(AST.Arithmetic op), i + 1

            withNewToken token j

        let maybeAssignOrDouble char op double =
            let token, j =
                if i + 2 < len && input[i + 1] = char && input[i + 2] = '=' then
                    AssignOp double, i + 3
                else if i + 1 < len && input[i + 1] = char then
                    Operator(AST.Arithmetic double), i + 2
                else if i + 1 < len && input[i + 1] = '=' then
                    AssignOp op, i + 2
                else
                    Operator(AST.Arithmetic op), i + 1

            withNewToken token j

        let rec parseInt alphabet i =
            let rec takeWhen i =
                if i = len then
                    i
                else if Array.contains input[i] alphabet || input[i] = '_' then
                    takeWhen (i + 1)
                else
                    i

            let j = takeWhen i

            if alphabet.Length <> 10 || j = len then
                Ok j
            else if input[j] = '.' then
                parseDec (j + 1)
            else if input[j] = 'e' || input[j] = 'E' then
                parseExp (j + 1)
            else
                Ok j

        and parseDec i =
            let rec takeWhen j =
                if j = len then
                    j
                else if System.Char.IsAsciiDigit input[j] then
                    takeWhen (j + 1)
                else if j <> i && input[j] = '_' then
                    takeWhen (j + 1)
                else
                    j

            let j = takeWhen i

            if j = len || (input[j] <> 'e' && input[j] <> 'E') then
                Ok j
            else
                parseExp (j + 1)

        and parseExp i =
            if i = len then
                Error(MissingExpContent, i)
            else
                let i = if input[i] = '+' || input[i] = '-' then i + 1 else i

                let rec takeWhen j =
                    if j = len then
                        j
                    else if System.Char.IsAsciiDigit input[j] then
                        takeWhen (j + 1)
                    else if j <> i && input[j] = '_' then
                        takeWhen (j + 1)
                    else
                        j

                if i = len then
                    Error(MissingExpContent, i)
                else
                    Ok(takeWhen i)

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
            | '?' -> punc Question
            | ';' -> delimiter Semi
            | '\n' -> delimiter CR
            | '\r' -> delimiter LF
            | ':' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = ':' then
                        ColonColon, i + 2
                    else
                        Colon, i + 1

                withNewToken token j

            | '.' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = '.' then
                        if i + 2 < len && input[i + 2] = '^' then
                            Ok DotDotCaret, i + 3
                        else
                            Ok DotDot, i + 2
                    else if i + 1 < len && System.Char.IsAsciiDigit input[i + 1] then
                        let j = parseDec (i + 1)

                        match j with
                        | Ok j ->
                            let str = input[i .. (j - 1)]

                            Ok(Lit(AST.Float(float str))), j
                        | Error(e, j) -> Error e, j
                    else
                        Ok Dot, i + 1

                match token with
                | Ok token -> withNewToken token j
                | Error msg -> withNewError msg j

            | ' '
            | '\t' ->
                let rec skipWhen i =
                    if i = len then
                        i
                    else if input[i] = ' ' || input[i] = '\t' then
                        skipWhen (i + 1)
                    else
                        i

                lex { state with i = skipWhen (i + 1) }

            | '=' ->
                let token, j =
                    if i + 1 < len then
                        match input[i + 1] with
                        | '>' -> FatArrow, i + 2
                        | '=' -> Operator(AST.EqEq), i + 2
                        | _ -> Eq, i + 1
                    else
                        Eq, i + 1

                withNewToken token j

            | '!' ->
                let token, j =
                    if i + 1 < len && input[i + 1] = '=' then
                        Operator(AST.NotEq), i + 2
                    else
                        Not, i + 1

                withNewToken token j

            | '+' -> maybeAssign AST.Add
            | '%' -> maybeAssign AST.Mod
            | '^' -> maybeAssign AST.BitXor

            | '*' -> maybeAssign AST.Mul

            | '-' ->
                if i + 1 < len && input[i + 1] = '>' then
                    withNewToken Arrow (i + 2)
                else
                    maybeAssign AST.Sub

            | '&' -> maybeAssignOrDouble '&' AST.BitAnd AST.LogicalAnd

            | '|' ->
                if i + 1 < len && input[i + 1] = '>' then
                    withNewToken (Operator AST.Pipe) (i + 2)
                else
                    maybeAssignOrDouble '|' AST.BitOr AST.LogicalOr

            | '>' ->
                let token, j =
                    if i + 2 < len && input[i + 1] = '>' && input[i + 2] = '=' then
                        AssignOp AST.Shr, i + 3
                    else if i + 1 < len && input[i + 1] = '>' then
                        Operator(AST.Arithmetic AST.Shr), i + 2
                    else if i + 1 < len && input[i + 1] = '=' then
                        Operator(AST.GtEq), i + 2
                    else
                        Operator(AST.Gt), i + 1

                withNewToken token j

            | '<' ->
                let token, j =
                    if i + 2 < len && input[i + 1] = '<' && input[i + 2] = '=' then
                        AssignOp AST.Shl, i + 3
                    else if i + 1 < len && input[i + 1] = '<' then
                        Operator(AST.Arithmetic AST.Shl), i + 2
                    else if i + 1 < len && input[i + 1] = '=' then
                        Operator(AST.LtEq), i + 2
                    else
                        Operator(AST.Lt), i + 1

                withNewToken token j

            | '/' ->
                let data, j =
                    if i + 1 < len then
                        match input[i + 1] with
                        | '/' ->
                            let rec takeWhen i =
                                if i = len || input[i] = '\n' || input[i] = '\r' then
                                    i
                                else
                                    takeWhen (i + 1)

                            let j = takeWhen (i + 1)
                            let token = Comment(SingleLine, input[(i + 2) .. (j - 1)])

                            Ok token, j
                        | '*' ->
                            let rec takeWhen j =
                                if j = len then
                                    Error IncompleteMultilineComment, j
                                else if j + 1 < len && input[j] = '*' && input[j + 1] = '/' then
                                    let token = Comment(MultiLine, input[(i + 2) .. (j - 1)])
                                    Ok token, j + 2
                                else
                                    takeWhen (j + 1)

                            takeWhen (i + 1)
                        | '=' -> Ok(AssignOp(AST.Div)), i + 2
                        | _ -> Ok(Operator(AST.Arithmetic AST.Div)), i + 1
                    else
                        Ok(Operator(AST.Arithmetic AST.Div)), i + 1

                match data with
                | Ok token -> withNewToken token j
                | Error msg -> withNewError msg j

            | '"' ->
                let rec takeWhen j =
                    if j = len then
                        Error(Unmatched(AST.Span.Make i (j - 1), '"'))
                    else if input[j] = '\\' then
                        if j = len - 1 then
                            Error(IncompleteEscapeSeq(AST.Span.Make i j))
                        else
                            takeWhen (j + 2)
                    else if input[j] = '"' then
                        Ok(j + 1)
                    else
                        takeWhen (j + 1)

                let res = takeWhen (i + 1)

                match res with
                | Error e ->
                    let error = Array.append state.error [| e |]

                    Error error
                | Ok j ->
                    let token = unescapeStr input[(i + 1) .. (j - 2)] |> AST.String |> Lit
                    withNewToken token j
            | ''' ->
                let rec takeWhen i =
                    if i = len then
                        Error i
                    else if input[i] = '\\' then
                        if i = len - 1 then Error i else takeWhen (i + 2)
                    else if input[i] = ''' then
                        Ok(i + 1)
                    else
                        takeWhen (i + 1)

                let j = takeWhen (i + 1)

                match j with
                | Error j ->
                    let error = Array.append state.error [| IncompleteEscapeSeq(AST.Span.Make j j) |]

                    Error error
                | Ok j ->
                    let str = unescapeStr input[(i + 1) .. (j - 2)]

                    match str.Length with
                    | 0 -> withNewError CharEmpty j
                    | 1 ->
                        let token = Lit(AST.Char str[0])

                        withNewToken token j

                    | _ -> withNewError CharTooMany j

            | c when isIdStart c ->
                let rec takeWhen i =
                    if i = len then i
                    else if isIdContinue input[i] then takeWhen (i + 1)
                    else i

                let j = takeWhen (i + 1)
                let token = parseIdentifier input[i .. (j - 1)]
                withNewToken token j

            | c when System.Char.IsAsciiDigit c ->
                let alphabet, newI =
                    if c = '0' && i + 1 < len then
                        match input[i + 1] with
                        | 'b'
                        | 'B' -> Ok(seq { '0' .. '1' }), i + 2
                        | 'o'
                        | 'O' -> Ok(seq { '0' .. '8' }), i + 2
                        | 'x'
                        | 'X' -> Ok(Seq.concat [ seq { '0' .. '9' }; seq { 'a' .. 'f' }; seq { 'A' .. 'F' } ]), i + 2
                        | _ -> Ok(seq { '0' .. '9' }), i + 1

                    else
                        Ok(seq { '0' .. '9' }), i + 1

                match alphabet with
                | Ok a ->
                    let alphabet = Seq.toArray a

                    let j =
                        if newI = len then
                            if alphabet.Length <> 10 then
                                Error(MissingIntContent, newI)
                            else
                                Ok newI
                        else
                            parseInt alphabet newI

                    match j with
                    | Ok j ->
                        let str = input[i .. (j - 1)]

                        let token, j =
                            if str.EndsWith '.' && j < len && (isIdStart input[j] || input[j] = '.') then
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

                        withNewToken token j
                    | Error(msg, j) -> withNewError msg j

                | Error c -> withNewError (fun span -> UnknownNumberPrefix(span, c)) (i + 2)

            | c ->
                let error =
                    Array.append state.error [| UnrecognizablePattern(AST.Span.Make i i, c) |]

                Error error

    lex { i = 0; data = [||]; error = [||] }
