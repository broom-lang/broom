type 'a with_pos = 'a Util.with_pos
type span = Util.span

module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module FExpr = Fc.Term.Expr
module AType = Ast.Type
module T = FcType.Type
module Tx = Transactional
type ctrs = Constraint.queue
type env = TypeEnv.t

type 'a typing = {term : 'a; eff : T.t}
type 'a kinding = {typ : 'a; kind : T.kind}

module type TYPING = sig
    val typeof : ctrs -> env -> AExpr.t with_pos -> FExpr.t typing
    val check : ctrs -> env -> T.t -> AExpr.t with_pos -> FExpr.t typing

    (* HACK: *)
    val typeof_pat : ctrs -> bool -> bool -> env -> Util.plicity -> AExpr.t with_pos
        -> FExpr.pat * env * FExpr.var Vector.t

    val check_program : TypeError.t list Tx.Ref.t -> ctrs
        -> AStmt.def Vector.t -> AExpr.t with_pos -> Fc.Program.t typing
    val check_interactive_stmts : Namespace.t -> TypeError.t list Tx.Ref.t
        -> ctrs -> AStmt.t Vector1.t -> Fc.Program.t typing * Namespace.t
end

module type KINDING = sig
    val elaborate : ctrs -> env -> AType.t with_pos -> T.t kinding
    val check : ctrs -> env -> T.kind -> AType.t with_pos -> T.t
    val kindof_F : ctrs -> span -> env -> T.t -> T.kind
    val eval : span -> env -> T.t -> (T.t * T.t T.coercion option) option
end

module type CONSTRAINTS = sig
    val unify : ctrs -> span -> env -> T.t -> T.t -> T.t T.coercion option
    val subtype : ctrs -> span -> env -> T.t -> T.t -> Fc.Term.Coercer.t option

    val solve : ctrs -> unit
end

