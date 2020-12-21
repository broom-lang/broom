(* Macroexpansion, infix operator "reparsing" and partial application handling.
 * Hygienic macroexpansion also causes alphatization. *)

type 'a with_pos = 'a Util.with_pos
type def = Ast.Term.Stmt.def
type stmt = Ast.Term.Stmt.t
type expr = Ast.Term.Expr.t

module Env : sig
    type t

    val empty : t
end

val expand : Env.t -> expr with_pos -> expr with_pos
val expand_interactive_stmt : Env.t -> stmt -> Env.t * stmt

