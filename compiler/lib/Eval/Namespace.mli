type typ = Fc.Type.t
type var = Fc.Term.Expr.var

type t

val empty : t

val add : t -> var -> t
val find_typ : t -> Name.t -> typ option
val find : t -> Name.t -> Value.t option ref option

