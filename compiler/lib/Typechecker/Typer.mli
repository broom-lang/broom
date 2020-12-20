module TypeError = TypeError

module Env : TyperSigs.ENV

type 'a typing = 'a TyperSigs.typing

val check_program : Env.t -> Ast.Term.Stmt.def Vector.t -> Ast.Term.Expr.t Util.with_pos
    -> (Fc.Program.t, Util.span * TypeError.t) result

val check_interactive_stmt : Env.t -> Ast.Term.Stmt.t
    -> (Fc.Program.t typing * Env.t, Util.span * TypeError.t) result

