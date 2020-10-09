module T = Fc.Type
module E = Fc.Term.Expr

val expand_clauses : Util.span -> T.t -> E.t -> E.clause Vector.t -> E.t

