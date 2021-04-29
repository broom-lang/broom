module Type = Fc.Type

module Map = Name.HashMap
module T = Fc.Type

type t = (T.t * Value.t option ref) Map.t

let empty = Map.empty

let add ns name typ = Map.add name (typ, ref None) ns

let find_typ ns name = Option.map fst (Map.get name ns)

let find ns name = Option.map snd (Map.get name ns)

