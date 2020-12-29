type t

val id : t
val coercer : (Fc.Term.Expr.t -> Fc.Term.Expr.t) -> t
val apply : t -> Fc.Term.Expr.t -> Fc.Term.Expr.t

