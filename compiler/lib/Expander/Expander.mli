(* Macroexpansion, infix operator "reparsing" and partial application handling.
 * Hygienic macroexpansion also causes alphatization. *)

module Env : sig
    type t

    val empty : t
end

val expand_defs : Env.t -> Ast.Term.Stmt.def Vector.t -> Ast.Term.Stmt.def Vector.t

