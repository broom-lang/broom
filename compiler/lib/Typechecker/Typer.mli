module Sigs = TyperSigs

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a Sigs.typing

module Error = TypeError

module Kinding : Sigs.KINDING

module Typing : Sigs.TYPING

val check_program : Ast.Program.t -> (Fc.Program.t typing, TypeError.t list) result

val check_interactive_stmts : Namespace.t -> Ast.Term.Stmt.t Vector1.t
    -> (Fc.Program.t typing * Namespace.t, TypeError.t list) result

