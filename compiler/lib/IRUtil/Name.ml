type t
    = String of string
    | Fresh of int

let counter = ref 0

let fresh () = 
    let i = !counter in
    counter := i + 1;
    Fresh i

let of_string str = String str

let compare = compare

let to_string = function
    | String s -> s
    | Fresh n ->"__" ^ Int.to_string n

let to_doc name = PPrint.string (to_string name)

type name = t

module Map = Map.Make(struct
    type t = name
    let compare = compare
end)

module Hashtbl = Hashtbl.Make(struct
    type t = name
    let equal = (=)
    let hash = Hashtbl.hash
end)

