module Lexer.Lexer

type Reserved =
    | IF
    | ELSE

    static member tryInto input =
        match input with
        | "if" -> Some IF
        | "else" -> Some ELSE
        | _ -> None

type Pair =
    | Open
    | Close

type Token =
    | Paren of Pair
    | Curly of Pair
    | Colon
    | Arrow
    | String of string
    | Number of string
    | Bool of bool
    | Identifier of string
    | Reserved of Reserved

type State = { in_comment: bool }

let lex (input: string) =
    let rec lex i state =
        if i = input.Length then
            [||]
        else
            match input[i] with
            | '(' -> Array.append [| Paren Open |] (lex (i + 1) state)
            | ')' -> Array.append [| Paren Close |] (lex (i + 1) state)
            | '{' -> Array.append [| Curly Open |] (lex (i + 1) state)
            | '}' -> Array.append [| Curly Close |] (lex (i + 1) state)
            | ' '
            | '\t'
            | '\n'
            | '\r' -> lex (i + 1) state
            | _ -> [||]

    lex 0 { in_comment = false }
