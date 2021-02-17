type expr = ComplexFc.Term.Expr.t

type t

val id : t
val coercer : (expr -> expr) -> t
val apply : t -> expr -> expr
val apply_opt : t option -> expr -> expr

