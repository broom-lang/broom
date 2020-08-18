module rec Expr : (FcSigs.EXPR
    with type def = Stmt.def
    with type stmt = Stmt.t)

and Stmt : (FcSigs.STMT
    with type expr = Expr.t
    with type lvalue = Expr.lvalue)

