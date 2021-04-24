module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module FExpr = Fc.Term.Expr
module AType = Ast.Type
module Type = FcType.Type
module Env = TypeEnv

type 'a with_pos = 'a Util.with_pos

type 'a typing = {term : 'a; eff : Type.t}

module type TYPING = sig
    val typeof : Constraint.queue -> Env.t -> AExpr.t with_pos -> FExpr.t typing
    val check_interactive_stmts : Constraint.queue -> Env.t -> AStmt.t Vector1.t
        -> Fc.Program.t typing * Env.t
end

module type KINDING = sig
    val elaborate : Env.t -> AType.t with_pos -> Type.t
end

