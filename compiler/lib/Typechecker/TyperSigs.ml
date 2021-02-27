module AExpr = Ast.Term.Expr
module FExpr = Fc.Term.Expr
module AType = Ast.Type
module Type = FcType.Type
module Env = TypeEnv

type 'a with_pos = 'a Util.with_pos

type 'a typing = {term : 'a; eff : Type.t}

module type TYPING = sig
    val typeof : Env.t -> AExpr.t with_pos -> FExpr.t typing
end

module type KINDING = sig
    val elaborate : Env.t -> AType.t with_pos -> Type.t
end

