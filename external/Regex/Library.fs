module Regex.Regex

type internal RegexUnit =
    | Empty
    // | All
    // | Range of (char * char)[]
    // | NotRange of (char * char)[]
    | Normal of char
    | Star of RegexUnit
    | Concat of RegexUnit[]
    | Or of RegexUnit[]

let internal parseRegex (str: string) =
    let arrToUnit r =
        match Array.length r with
        | 0 -> Empty
        | 1 -> r[0]
        | _ -> Concat r

    let findOther (str: string) =
        let rec findOther i cnt =
            if cnt = 0 then
                i - 1
            else if i = str.Length then
                failwith "cannot find correspond bracket"
            else
                match str[i] with
                | '(' -> findOther (i + 1) (cnt + 1)
                | ')' -> findOther (i + 1) (cnt - 1)
                | _ -> findOther (i + 1) cnt

        findOther 0 1

    let rec parseRegex (str: string) prev =
        if str.Length = 0 then
            prev
        else
            match str[0] with
            | '*' ->
                let last = Star(Array.last prev)
                Array.set prev (prev.Length - 1) last
                parseRegex str[1..] prev

            | '+' ->
                let last = Array.last prev
                let last = Concat [| last; Star last |]
                Array.set prev (prev.Length - 1) last
                parseRegex str[1..] prev

            | '?' ->
                let last = Array.last prev
                let last = Or [| last; Empty |]
                Array.set prev (prev.Length - 1) last
                parseRegex str[1..] prev

            | '|' ->
                let other = parseRegex str[1..] [||]

                let r =
                    match arrToUnit prev, arrToUnit other with
                    | Or l, Or r -> Or(Array.append l r)
                    | Or l, r -> Or(Array.append l [| r |])
                    | l, Or r -> Or(Array.append [| l |] r)
                    | l, r -> Or [| l; r |]

                [| r |]

            | '(' ->
                let endId = findOther str[1..]
                let child = parseRegex str[1..endId] [||] |> arrToUnit
                let prev = Array.append prev [| child |]

                parseRegex str[(endId + 2) ..] prev

            | ')' -> failwith "unreachable"

            | '\\' ->
                if str.Length = 1 then
                    failwith "incomplete escape sequence"

                let prev = Array.append prev [| (Normal str[1]) |]

                parseRegex str[2..] prev

            | c ->
                let prev = Array.append prev [| (Normal c) |]

                parseRegex str[1..] prev

    parseRegex str [||] |> arrToUnit

type internal NFAUnit = { next: Option<char>; maybe: int[] }

let internal regexToNFA regex =
    let empty = { next = None; maybe = [||] }

    let rec regexToNFA cnt regex =
        match regex with
        | Empty -> [| { next = None; maybe = [| cnt + 1 |] }; empty |], cnt + 2
        | Normal c -> [| { next = Some c; maybe = [||] }; empty |], cnt + 2

        | Concat r ->
            let folder (arr: NFAUnit[], cnt) r =
                let nu, cnt = regexToNFA cnt r

                Array.concat [ arr[.. (arr.Length - 2)]; nu ], cnt - 1

            let nfa, cnt = Array.fold folder ([| empty |], cnt) r
            nfa, cnt + 1

        | Or r ->
            let calcMiddle (arr, len, cnt) r =
                let nu, newCnt = regexToNFA cnt r

                Array.append arr nu, Array.append len [| newCnt - cnt |], newCnt

            let middle, len, newCnt = Array.fold calcMiddle ([||], [||], cnt + 1) r

            let mutable idx = 0

            for cnt in len do
                idx <- idx + cnt

                let newEnd = { next = None; maybe = [| newCnt |] }

                Array.set middle (idx - 1) newEnd

            let firstId = Array.scan (+) (cnt + 1) len

            let first =
                { next = None
                  maybe = firstId[0 .. firstId.Length - 2] }

            Array.concat [ [| first |]; middle; [| empty |] ], newCnt + 1

        | Star r ->
            let middle, newCnt = regexToNFA (cnt + 1) r

            Array.set
                middle
                (middle.Length - 1)
                { next = None
                  maybe = [| cnt + 1; newCnt |] }

            let first =
                { next = None
                  maybe = [| cnt + 1; newCnt |] }

            Array.concat [ [| first |]; middle; [| empty |] ], newCnt + 1

    regexToNFA 0 regex |> fst

type internal DFAUnit =
    { next: Map<char, int>; terminal: bool }

let internal nfaToDFA (nfa: NFAUnit[]) =
    let rec eclosure i : Set<int> =
        Array.map eclosure nfa[i].maybe |> Set.unionMany |> Set.add i

    let closureNext e =
        let reachable state key i =
            let add prev =
                Some(
                    match prev with
                    | Some p -> if Set.contains i p then p else Set.union (eclosure i) p
                    | None -> eclosure i
                )

            Map.change key add state

        let setReachable state i =
            let init =
                match nfa[i].next with
                | Some c -> Map [ c, i + 1 ]
                | None -> Map.empty

            Map.fold reachable state init

        Set.fold setReachable Map.empty e

    let rec transform curr map =
        let reachable = closureNext curr

        let getTodo (map, todo) _ set =
            match Map.tryFind set map with
            | Some _ -> map, todo
            | None -> Map.add set (Map.count map) map, Array.append todo [| set |]

        let map, todo = Map.fold getTodo (map, [||]) reachable

        let idx = map[curr]

        let curr =
            { next = Map.map (fun _ v -> map[v]) reachable
              terminal = Set.contains (nfa.Length - 1) curr }

        let calcTodo (state, map) todo =
            let rest, map = transform todo map

            let state = Map.fold (fun map k v -> Map.add k v map) state rest

            state, map

        Array.fold calcTodo (Map [| idx, curr |], map) todo

    let init = eclosure 0

    let dfa, _ = transform init (Map [| init, 0 |])

    dfa |> Map.values |> Seq.toArray

let internal minifyDFA (dfa: DFAUnit[]) =
    let dfaId = seq { 0 .. (dfa.Length - 1) }

    let partTerminal (t, nt) i =
        if dfa[i].terminal then Set.add i t, nt else t, Set.add i nt

    let t, nt = Seq.fold partTerminal (Set.empty, Set.empty) dfaId

    let trySplit (ctx: Map<int, int>) s =
        let mapToSeq m = m |> Map.keys |> Set.ofSeq

        let unionOfNext state i =
            let node = dfa[i]

            Set.union state (mapToSeq node.next)

        let possibleNext = Set.fold unionOfNext Set.empty s

        let nextOfSet s next =
            let nextOfUnit i =
                let node = dfa[i]

                let next =
                    match Map.tryFind next node.next with
                    | Some next -> Some ctx[next]
                    | None -> None

                i, next

            s |> Set.toArray |> Array.map nextOfUnit

        let findSplit next =
            let nextMap = nextOfSet s next
            let nextGroup = Array.groupBy (fun (_, next) -> next) nextMap

            if nextGroup.Length = 1 then
                None
            else
                let getNodeSet (_, nodeToNext) = Array.map fst nodeToNext |> Set.ofArray

                Some(Array.map getNodeSet nextGroup)

        Seq.tryPick findSplit possibleNext

    let rec split ctx arr =
        let updateCtx value state i = Map.add i value state
        let last = Map.count ctx

        let updateCtxMulti state (idx, set) =
            Set.fold (updateCtx (last + idx)) state set

        let ctx = Array.fold updateCtxMulti ctx (Array.indexed arr)

        let splitSet ctx set =
            match Set.count set with
            | 0 -> [||], ctx
            | 1 -> [| set |], ctx
            | _ ->
                match trySplit ctx set with
                | Some child ->
                    let union = Set.unionMany child
                    let rest = Set.difference set union

                    let res =
                        if Set.count rest = 0 then
                            child
                        else
                            Array.append [| rest |] child

                    split ctx res
                | None -> [| set |], ctx

        Array.foldBack
            (fun set (state, ctx) ->
                let child, ctx = splitSet ctx set

                Array.append state child, ctx)
            arr
            ([||], ctx)

    let newDfa, _ = split Map.empty [| nt; t |]

    if newDfa.Length = dfa.Length then
        dfa
    else
        let newDfa = Array.sortBy Set.minElement newDfa

        let mapToNewId state (newId, set) =
            Set.fold (fun state id -> Map.add id newId state) state set

        let idMap = Array.fold mapToNewId Map.empty (Array.indexed newDfa)

        let mapToNewDfa (state, seen) idx =
            if Set.contains idx seen then
                state, seen
            else
                let merge = newDfa[Array.length state]
                let seen = Set.union seen merge

                let mergeNext prev curr =
                    Map.fold (fun prev key value -> Map.add key idMap[value] prev) prev curr

                let calcNewDfa state id =
                    let dfa = dfa[id]

                    { next = mergeNext state.next dfa.next
                      terminal = state.terminal || dfa.terminal }

                let newDfa = Set.fold calcNewDfa { next = Map []; terminal = false } merge

                Array.append state [| newDfa |], seen

        Array.fold mapToNewDfa ([||], Set.empty) (Array.ofSeq dfaId) |> fst

type Regex(text) =
    let regex = text |> parseRegex |> regexToNFA |> nfaToDFA |> minifyDFA

    member this.MatchStr str =
        let rec matchStr i (str: string) =
            if str.Length = 0 then
                regex[i].terminal
            else
                let next = regex[i].next

                match Map.tryFind str[0] next with
                | Some next -> matchStr next str[1..]
                | None -> false

        matchStr 0 str
