module H = Hashtbl

module Key = struct
    type t = int

    let compare = Int.compare
    let equal = Int.equal
    let hash = H.hash
end

module Hashtbl = H.Make(Key)
module HashMap = CCHashTrie.Make(Key)
module HashSet = CCHashSet.Make(Key)
module Map = Map.Make(Key)

include Key

let fresh =
    let counter = ref 0 in
    fun () ->
        let i = !counter in
        counter := i + 1;
        i

let names = Hashtbl.create 0

let of_string =
    let module Cache = H.Make(struct
        type t = string
        let equal = String.equal
        let hash = H.hash
    end) in
    let cache = Cache.create 0 in
    fun s ->
        match Cache.find_opt cache s with
        | Some n -> n
        | None ->
            let n = fresh () in
            Hashtbl.add names n s;
            Cache.add cache s n;
            n

let basename n = Hashtbl.find_opt names n

let freshen n =
    let n' = fresh () in
    (match basename n with
    | Some s -> Hashtbl.add names n' s
    | None -> ());
    n'

let to_string n = 
    let prefix = match basename n with
        | Some s -> s ^ "$"
        | None -> "$" in
    prefix ^ Int.to_string n

let to_doc n = PPrint.string (to_string n)

