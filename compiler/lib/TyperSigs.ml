(* Predeclare types and signatures for typer internal modules so that they can be separated: *)

type span = Util.span
type 'a with_pos = 'a Ast.with_pos

type typ = Fc.Type.t
type abs = Fc.Type.abs

type 'a typing = {term : 'a; typ : typ; eff : typ}
type 'a kinding = {typ : 'a; kind : Fc.Type.kind}

(* Newtype to allow ignoring subtyping coercions without partial application warning: *)
(* TODO: triv_expr with_pos -> expr with_pos to avoid bugs that would delay side effects
         or that duplicate large/nontrivial terms: *)
type coercer = Cf of (Fc.Term.Expr.t with_pos -> Fc.Term.Expr.t with_pos)

module type KINDING = sig
    val kindof_F : Env.t -> Fc.Type.t -> Fc.Type.kind
    val kindof : Env.t -> Ast.Type.t with_pos -> abs kinding
    val check : Env.t -> Fc.Type.kind -> Ast.Type.t with_pos -> abs
    val eval : Env.t -> typ -> (typ * Fc.Type.coercion option) option
end

module type TYPING = sig
    val typeof : Env.t -> Ast.Term.Expr.t with_pos -> Fc.Term.Expr.t with_pos typing
    val deftype : Env.t -> Ast.Term.Stmt.def -> Fc.Term.Expr.def typing
    val check_stmt : Env.t -> Ast.Term.Stmt.t -> Fc.Term.Stmt.t typing * Env.t
    (* HACK: (?): *)
    val elaborate_pat : Env.t -> Ast.Term.Expr.pat with_pos ->
        Fc.Term.Expr.pat with_pos * (Fc.Type.ov Vector.t * Fc.Type.t) * Fc.Term.Expr.lvalue Vector.t
    val lookup : span -> Env.t -> Name.t -> Fc.Term.Expr.lvalue
end

module type MATCHING = sig
    val focalize : span -> Env.t -> typ -> Fc.Type.template -> coercer * typ
    val solving_subtype : span -> Env.t -> typ -> typ -> coercer
    val solving_unify : span -> Env.t -> typ -> typ -> Fc.Type.coercion option
end

