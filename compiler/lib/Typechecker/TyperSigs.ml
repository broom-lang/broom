type 'a with_pos = 'a Util.with_pos
type span = Util.span

module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module FExpr = Fc.Term.Expr
module AType = Ast.Type
module T = FcType.Type
module Env = TypeEnv
module Tx = Transactional

type 'a typing = {term : 'a; eff : T.t}

module type TYPING = sig
    val typeof : Constraint.queue -> Env.t -> AExpr.t with_pos -> FExpr.t typing
    val check_interactive_stmts : Constraint.queue -> Env.t -> AStmt.t Vector1.t
        -> Fc.Program.t typing * Env.t
end

module type KINDING = sig
    val elaborate : Env.t -> AType.t with_pos -> T.t
    val eval : span -> Env.t -> T.t -> (T.t * T.coercion option) option
end

module type CONSTRAINTS = sig
    type queue = Constraint.queue

    val unify : queue -> span -> Env.t -> T.t -> T.t -> T.coercion option
    val subtype : queue -> span -> Env.t -> T.t -> T.t -> Fc.Term.Coercer.t option

    val solve : queue -> unit
end

