module Sigs = TyperSigs
module Env = TypeEnv

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a Sigs.typing

module Error = TypeError

module Kinding : Sigs.KINDING

module Typing : Sigs.TYPING

val check_interactive_stmts : Env.t -> Ast.Term.Stmt.t Vector1.t
    -> (Fc.Program.t typing * Env.t, TypeError.t list) result

