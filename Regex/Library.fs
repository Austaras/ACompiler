module Regex.Regex

type internal RegexUnit =
    | Empty
    // | All
    // | Range of char * char
    | Normal of char
    | Star of RegexUnit
    | Concat of RegexUnit[]
    | Or of RegexUnit[]

let internal parseRegex (str: string) =
    let arr_to_unit r =
        match Array.length r with
        | 0 -> Empty
        | 1 -> r[0]
        | _ -> Concat r

    let find_other (str: string) =
        let rec find_other i cnt =
            if cnt = 0 then
                i - 1
            else if i = str.Length then
                failwith "cannot find correspond bracket"
            else
                match str[i] with
                | '(' -> find_other (i + 1) (cnt + 1)
                | ')' -> find_other (i + 1) (cnt - 1)
                | _ -> find_other (i + 1) cnt

        find_other 0 1

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
                    match arr_to_unit prev, arr_to_unit other with
                    | Or l, Or r -> Or(Array.append l r)
                    | Or l, r -> Or(Array.append l [| r |])
                    | l, Or r -> Or(Array.append [| l |] r)
                    | l, r -> Or [| l; r |]

                [| r |]

            | '(' ->
                let end_id = find_other str[1..]
                let child = parseRegex str[1..end_id] [||] |> arr_to_unit
                let prev = Array.append prev [| child |]

                parseRegex str[(end_id + 2) ..] prev

            | ')' -> failwith "unreachable"

            | c ->
                let prev = Array.append prev [| (Normal c) |]

                parseRegex str[1..] prev

    parseRegex str [||] |> arr_to_unit

type internal NFAUnit = { next: Map<char, int>; maybe: int[] }

let internal regexToNFA regex =
    let empty = { next = Map [||]; maybe = [||] }

    let rec regexToNFA cnt regex =
        match regex with
        | Empty ->
            [| { next = Map [||]
                 maybe = [| cnt + 1 |] }
               empty |],
            cnt + 2
        | Normal c ->
            [| { next = Map [| c, cnt + 1 |]
                 maybe = [||] }
               empty |],
            cnt + 2

        | Concat r ->
            let folder (arr: NFAUnit[], cnt) r =
                let nu, cnt = regexToNFA cnt r

                Array.concat [ arr[.. (arr.Length - 2)]; nu ], cnt - 1

            let nfa, cnt = Array.fold folder ([| empty |], cnt) r
            nfa, cnt + 1

        | Or r ->
            let calc_middle (arr, len, cnt) r =
                let nu, new_cnt = regexToNFA cnt r

                Array.append arr nu, Array.append len [| new_cnt - cnt |], new_cnt

            let middle, len, new_cnt = Array.fold calc_middle ([||], [||], cnt + 1) r

            let mutable idx = 0

            for cnt in len do
                idx <- idx + cnt

                let new_end =
                    { next = Map.empty
                      maybe = [| new_cnt |] }

                Array.set middle (idx - 1) new_end

            let first_id = Array.scan (+) (cnt + 1) len

            let first =
                { next = Map.empty
                  maybe = first_id[0 .. first_id.Length - 2] }

            Array.concat [ [| first |]; middle; [| empty |] ], new_cnt + 1

        | Star r ->
            let middle, new_cnt = regexToNFA (cnt + 1) r

            Array.set
                middle
                (middle.Length - 1)
                { next = Map.empty
                  maybe = [| cnt + 1; new_cnt |] }

            let first =
                { next = Map.empty
                  maybe = [| cnt + 1; new_cnt |] }

            Array.concat [ [| first |]; middle; [| empty |] ], new_cnt + 1

    regexToNFA 0 regex |> fst

type internal DFAUnit =
    { next: Map<char, int>; terminal: bool }

let internal nfaToDFA (nfa: NFAUnit[]) =
    let rec eclosure i : Set<int> =
        Array.map eclosure nfa[i].maybe |> Set.unionMany |> Set.add i

    let closure_next e =
        let reachable state key i =
            let add prev =
                Some(
                    match prev with
                    | Some p -> Set.add i p
                    | None -> Set [| i |]
                )

            Map.change key add state

        let set_reachable state i = Map.fold reachable state nfa[i].next

        let set_eclosure _ s =
            s |> Set.toArray |> Array.map eclosure |> Set.unionMany

        Set.fold set_reachable Map.empty e |> Map.map set_eclosure

    let rec transform curr map =
        let reachable = closure_next curr

        let get_todo (map, todo) _ set =
            match Map.tryFind set map with
            | Some _ -> map, todo
            | None -> Map.add set (Map.count map) map, Array.append todo [| set |]

        let map, todo = Map.fold get_todo (map, [||]) reachable

        let idx = map[curr]

        let curr =
            { next = Map.map (fun _ v -> map[v]) reachable
              terminal = Set.contains (nfa.Length - 1) curr }

        let calc_todo (state, map) todo =
            let rest, map = transform todo map

            let state = Map.fold (fun map k v -> Map.add k v map) state rest

            state, map

        Array.fold calc_todo (Map [| idx, curr |], map) todo

    let init = eclosure 0

    let dfa, _ = transform init (Map [| init, 0 |])

    dfa |> Map.values |> Seq.toArray

let internal minifyDFA (dfa: DFAUnit[]) =
    let dfa_id = seq { 0 .. (dfa.Length - 1) }

    let part_terminal (t, nt) i =
        if dfa[i].terminal then Set.add i t, nt else t, Set.add i nt

    let t, nt = Seq.fold part_terminal (Set.empty, Set.empty) dfa_id

    let try_split (ctx: Map<int, int>) s =
        let map_to_seq m = m |> Map.keys |> Set.ofSeq

        let union_of_next state i =
            let node = dfa[i]

            Set.union state (map_to_seq node.next)

        let possible_next = Set.fold union_of_next Set.empty s

        let next_of_set s next =
            let next_of_unit i =
                let node = dfa[i]

                let next =
                    match Map.tryFind next node.next with
                    | Some next -> Some ctx[next]
                    | None -> None

                i, next

            s |> Set.toArray |> Array.map next_of_unit

        let find_split next =
            let next_map = next_of_set s next
            let next_group = Array.groupBy (fun (_, next) -> next) next_map

            if next_group.Length = 1 then
                None
            else
                let get_node_set (_, node_to_next) =
                    Array.map (fun (node, _) -> node) node_to_next |> Set.ofArray

                Some(Array.map get_node_set next_group)

        Seq.tryPick find_split possible_next

    let rec split ctx arr =
        let update_ctx value state i = Map.add i value state
        let last = Map.count ctx

        let update_ctx_multi state (idx, set) =
            Set.fold (update_ctx (last + idx)) state set

        let ctx = Array.fold update_ctx_multi ctx (Array.indexed arr)

        let split_set ctx set =
            match Set.count set with
            | 0 -> [||], ctx
            | 1 -> [| set |], ctx
            | _ ->
                match try_split ctx set with
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
                let child, ctx = split_set ctx set

                Array.append state child, ctx)
            arr
            ([||], ctx)

    let new_dfa = [| nt; t |]
    let new_dfa, _ = split Map.empty new_dfa

    if new_dfa.Length = dfa.Length then
        dfa
    else
        let new_dfa = Array.sortBy Set.minElement new_dfa

        let map_to_new_id state (new_id, set) =
            Set.fold (fun state id -> Map.add id new_id state) state set

        let id_map = Array.fold map_to_new_id Map.empty (Array.indexed new_dfa)

        let map_to_new_dfa (state, seen) idx =
            if Set.contains idx seen then
                state, seen
            else
                let merge = new_dfa[Array.length state]
                let seen = Set.union seen merge

                let merge_next prev curr =
                    Map.fold (fun prev key value -> Map.add key id_map[value] prev) prev curr

                let calc_new_dfa state id =
                    let dfa = dfa[id]

                    { next = merge_next state.next dfa.next
                      terminal = state.terminal || dfa.terminal }

                let new_dfa = Set.fold calc_new_dfa { next = Map []; terminal = false } merge

                Array.append state [| new_dfa |], seen

        Array.fold map_to_new_dfa ([||], Set.empty) (Array.ofSeq dfa_id) |> fst

type Regex(text) =
    let regex = text |> parseRegex |> regexToNFA |> nfaToDFA |> minifyDFA

    member this.match_str str =
        let rec match_str i (str: string) =
            if str.Length = 0 then
                regex[i].terminal
            else
                let next = regex[i].next

                match Map.tryFind str[0] next with
                | Some next -> match_str next str[1..]
                | None -> false

        match_str 0 str
