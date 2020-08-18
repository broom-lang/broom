(* Predeclare types and signatures for typer internal modules so that they can be separated: *)

open FcType

type span = Util.span
type 'a with_pos = 'a Ast.with_pos
type 'a typing = {term : 'a; typ : typ; eff : typ}

(* Newtype to allow ignoring subtyping coercions without partial application warning: *)
(* TODO: triv_expr with_pos -> expr with_pos to avoid bugs that would delay side effects
         or that duplicate large/nontrivial terms: *)
type coercer = Cf of (FcTerm.Expr.t with_pos -> FcTerm.Expr.t with_pos)

module type ELABORATION = sig
    val elaborate : Env.t -> Ast.Type.t with_pos -> abs
    val eval : Env.t -> typ -> (typ * coercion option) option
end

module type CHECKING = sig
    val typeof : Env.t -> Ast.Term.Expr.t with_pos -> FcTerm.Expr.t with_pos typing
    val deftype : Env.t -> Ast.Term.Stmt.def -> FcTerm.Expr.def typing
    val lookup : span -> Env.t -> Name.t -> locator * FcTerm.Expr.lvalue
end

module type MATCHING = sig
    val focalize : span -> Env.t -> typ -> locator -> coercer * typ
    val solving_coercion : span -> Env.t -> typ -> ov Vector.t * locator * typ -> coercer
    val solving_subtype : span -> Env.t -> typ -> locator -> typ -> coercer
    val solving_unify : span -> Env.t -> typ -> typ -> coercion option
end

