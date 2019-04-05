signature EXPR = sig
    type expr
end

functor ExprFn(Expr: EXPR) :> EXPR = struct
    datatype expr = Fn of string * Expr.expr
                  | App of Expr.expr * Expr.expr
                  | Var of string
end

structure Expr = ExprFn(Expr)

structure TypedExpr = ExprFn(struct
    type expr = { expr: TypedExpr.expr
                , typ: Type.typ }
end)

