module Type = Fc.Type

type t

val empty : t

val add : t -> Name.t -> Type.t -> t
val find_typ : t -> Name.t -> Type.t option
val find : t -> Name.t -> Value.t option ref option

