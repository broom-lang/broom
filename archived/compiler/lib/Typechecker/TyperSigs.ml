type span = Util.span
type plicity = Util.plicity

module AExpr = Ast.Expr
module AStmt = Ast.Stmt
module FExpr = Fc.Term.Expr
module AType = Ast.Expr
module T = FcType.Type
module Tx = Transactional
type ctrs = Constraint.queue
type env = TypeEnv.t

type 'a typing = {term : 'a; eff : T.t}
type 'a kinding = {typ : 'a; kind : T.kind}

module type TYPING = sig
    val typeof : ctrs -> env -> AExpr.t -> FExpr.t typing
    val check : ctrs -> env -> T.t -> AExpr.t -> FExpr.t typing

    val bind_pat : env -> plicity -> AExpr.t
        -> (plicity -> span -> Name.t -> unit)
        -> unit
    val typeof_bound_pat : ctrs -> env -> Util.plicity -> AExpr.t -> FExpr.pat
    val typeof_pat : ctrs -> env -> TypeEnv.NonRecScope.Builder.t
        -> (span -> Name.t -> FExpr.var -> unit)
        -> Util.plicity -> AExpr.t -> FExpr.pat

    val check_program : TypeError.t list Tx.Ref.t -> ctrs -> Ast.Program.t
        -> Fc.Program.t typing
    val check_interactive_stmts : Namespace.t -> TypeError.t list Tx.Ref.t
        -> ctrs -> AStmt.t Vector1.t -> Fc.Program.t typing * Namespace.t
end

module type KINDING = sig
    val elaborate : ctrs -> env -> AType.t -> T.t kinding
    val check : ctrs -> env -> T.kind -> AType.t -> T.t
    val kindof_F : ctrs -> span -> env -> T.t -> T.kind
    val eval : span -> env -> T.t -> (T.t * T.t T.coercion option) option
end

module type CONSTRAINTS = sig
    val unify : ctrs -> span -> env -> T.t -> T.t -> T.t T.coercion option
    val subtype : ctrs -> span -> env -> T.t -> T.t -> Fc.Term.Coercer.t option

    val solve : ctrs -> unit
end

