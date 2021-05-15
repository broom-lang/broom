(* Macroexpansion, infix operator "reparsing" and partial application handling.
 * Hygienic macroexpansion also causes alphatization. *)

type 'a with_pos = 'a Util.with_pos
type def = Ast.Term.Stmt.def
type stmt = Ast.Term.Stmt.t
type expr = Ast.Term.Expr.t
type broompath = string list

module Make (StringHashtbl : Hashtbl.S with type key = string) : sig
    module Bindings : sig
        type t

        val empty : broompath -> t
    end

    val expand_program : Bindings.t -> Ast.Program.t -> Ast.Program.t
    val expand_interactive_stmt : Bindings.t -> stmt -> Bindings.t * stmt Vector1.t
end

