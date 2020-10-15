module S = CpsSigs

module Type : S.TYPE

module Expr : S.EXPR
    with module Type = Type

module Pattern : S.PATTERN

module Transfer : S.TRANSFER
    with type expr_id = Expr.Id.t
    with type cont_id = Expr.cont_id
    with module Type = Type

module Cont : S.CONT
    with module Type = Type
    with module Transfer = Transfer
    with type Id.t = Expr.cont_id

module Program : S.PROGRAM
    with module Type = Type
    with module Expr = Expr
    with module Cont = Cont

