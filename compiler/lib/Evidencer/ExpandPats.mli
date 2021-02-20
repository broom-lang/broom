module Fc = ComplexFc
module T = Fc.Type
module E = ComplexFc.Term.Expr

module type S = sig
    type env

    type ctx = Inline | Shared of Fc.Term.Expr.var | Redirect of Fc.Term.Expr.var
    type final_naming = {tmp_var : Fc.Term.Expr.var; src_var : Fc.Term.Expr.var}
    type final_emitter = ctx -> final_naming Vector.t -> Fc.Term.Expr.t
    type clause' = {pat : Fc.Term.Expr.pat; emit : final_emitter}

    val expand_clauses : Util.span -> env -> T.t -> Fc.Term.Expr.t -> clause' Vector.t
        -> Fc.Term.Expr.t
end

module Make
    (Env : TyperSigs.ENV)
    (K : TyperSigs.KINDING with type env = Env.t)
: S with type env = Env.t

