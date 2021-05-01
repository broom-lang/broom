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
    val check_program : TypeError.t list Tx.Ref.t -> Constraint.queue
        -> AStmt.def Vector.t -> AExpr.t with_pos -> Fc.Program.t typing
    val check_interactive_stmts : Namespace.t -> TypeError.t list Tx.Ref.t
        -> Constraint.queue -> AStmt.t Vector1.t -> Fc.Program.t typing * Namespace.t
end

module type KINDING = sig
    val elaborate : Env.t -> AType.t with_pos -> T.t
    val check : Env.t -> T.kind -> AType.t with_pos -> T.t
    val kindof_F : Constraint.queue -> span -> Env.t -> T.t -> T.kind
    val eval : span -> Env.t -> T.t -> (T.t * T.t T.coercion option) option
end

module type CONSTRAINTS = sig
    type queue = Constraint.queue

    val unify : queue -> span -> Env.t -> T.t -> T.t -> T.t T.coercion option
    val subtype : queue -> span -> Env.t -> T.t -> T.t -> Fc.Term.Coercer.t option

    val solve : queue -> unit
end

