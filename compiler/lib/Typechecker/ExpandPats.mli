module T = Fc.Type
module E = Fc.Term.Expr

type ctx = Inline | Shared of E.var | Redirect of E.var
type final_naming = {tmp_var : E.var; src_var : E.var}
type final_emitter = ctx -> final_naming Vector.t -> E.t
type clause' = {pat : E.pat; emit : final_emitter}

val expand_clauses : Util.span -> T.t -> E.t -> clause' Vector.t -> E.t

