module T = Fc.Type
module E = Fc.Term.Expr

val expand_clauses : Util.span -> T.t -> E.t -> E.clause Vector.t -> E.t

val expand_stmt : Fc.Term.Stmt.t -> Fc.Term.Stmt.t

