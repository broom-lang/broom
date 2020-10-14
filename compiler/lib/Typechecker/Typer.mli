module TypeError = TypeError

module Env : TyperSigs.ENV

type 'a typing = 'a TyperSigs.typing

val typeof : Env.t -> Ast.Term.Expr.t Util.with_pos -> Fc.Term.Expr.t typing
val check_program : Env.t -> Ast.Term.Stmt.def Vector.t -> Ast.Term.Expr.t Util.with_pos
    -> Fc.Program.t
val check_stmt : Env.t -> Ast.Term.Stmt.t -> Fc.Term.Stmt.t Vector.t typing * Fc.Type.t * Env.t

