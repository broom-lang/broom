type typ = Fc.Type.t
type var = Fc.Term.Expr.var

module Map = Name.HashMap
module T = Fc.Type

type t = (typ * Value.t option ref) Map.t

let empty = Map.empty

let add ns (var : var) = Map.add var.name (var.vtyp, ref None) ns

let find_typ ns name = Option.map fst (Map.get name ns)

let find ns name = Option.map snd (Map.get name ns)

