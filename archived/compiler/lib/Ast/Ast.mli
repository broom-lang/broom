type 'a with_pos = 'a Util.with_pos

module Primop : AstSigs.PRIMOP

module rec Expr : (AstSigs.EXPR
    with type primop = Primop.t
    with type stmt = Stmt.t
    with type decl = Decl.t)

and Stmt : (AstSigs.STMT
    with type expr = Expr.t)

and Decl : (AstSigs.DECL
    with type expr = Expr.t)

module Program : AstSigs.PROGRAM
    with module Stmt = Stmt
    with module Expr = Expr

