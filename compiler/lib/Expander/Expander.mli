(* Macroexpansion, infix operator "reparsing" and partial application handling.
 * Hygienic macroexpansion also causes alphatization. *)

type 'a with_pos = 'a Util.with_pos
type def = Ast.Term.Stmt.def
type expr = Ast.Term.Expr.t

module Env : sig
    type t

    val empty : t
end

val expand_defs : Env.t -> def Vector.t -> def Vector.t
val expand_program : def Vector.t -> expr with_pos -> expr with_pos

