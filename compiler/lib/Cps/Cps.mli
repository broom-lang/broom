module S = CpsSigs

module Type : S.TYPE

module ContId : Id.S

module Expr : S.EXPR
    with type cont_id = ContId.t
    with module Type = Type

module Pattern : S.PATTERN

module Transfer : S.TRANSFER
    with type expr_id = Expr.Id.t
    with type cont_id = ContId.t
    with module Pattern = Pattern
    with module Type = Type

module Cont : S.CONT
    with module Type = Type
    with module Transfer = Transfer
    with module Id = ContId

module Program : S.PROGRAM
    with module Type = Type
    with module Expr = Expr
    with module Cont = Cont

