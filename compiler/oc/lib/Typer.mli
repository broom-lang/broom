module Env = Env

type 'a typing = 'a TyperSigs.typing

val check_stmt : Env.t -> Ast.Term.Stmt.t -> FcTerm.Stmt.t typing

