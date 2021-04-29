module Map = Name.Hashtbl

type t = Value.t Map.t

let create () = Map.create 0
let add = Map.add
let find = Map.find_opt
let clone = Map.copy

