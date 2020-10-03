type t
    = String of string
    | Fresh of int
    | Fring of string * int

let counter = ref 0

let fresh () = 
    let i = !counter in
    counter := i + 1;
    Fresh i

let freshen name =
    let i = !counter in
    counter := i + 1;
    match name with
    | String s -> Fring (s, i)
    | Fresh _ -> Fresh i
    | Fring (s, _) -> Fring (s, i)

let is_gensym = function String _ -> false | Fresh _ | Fring _ -> true

let of_string str = String str

let compare = compare

let to_string = function
    | String s -> s
    | Fresh n ->"__" ^ Int.to_string n
    | Fring (s, n) -> s ^ "__" ^ Int.to_string n

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

