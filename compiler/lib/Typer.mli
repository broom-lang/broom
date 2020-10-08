module TypeError = TypeError

module Env : TyperSigs.ENV

type 'a typing = 'a TyperSigs.typing

val check_stmt : Env.t -> Ast.Term.Stmt.t -> Fc.Term.Stmt.t Vector.t typing * Fc.Type.t * Env.t

