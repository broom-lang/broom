module Type = Cps.Type

module Expr : CfgSigs.EXPR

module Stmt : CfgSigs.STMT
    with module Type = Type

module Transfer : CfgSigs.TRANSFER
    with module Type = Type
    with type expr_id = Expr.Id.t
    with type cont_id = Cps.Cont.Id.t

module Cont : CfgSigs.CONT
    with module Type = Type
    with module Stmt = Stmt
    with module Id = Cps.Cont.Id

module Program : CfgSigs.PROGRAM
    with module Stmt = Stmt
    with module Transfer = Transfer
    with module Cont = Cont

