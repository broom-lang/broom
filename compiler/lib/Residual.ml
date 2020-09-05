module T = Fc.Type

type t =
    | Sub of bool * T.t * T.locator * T.t * Fc.Term.Expr.t Ast.with_pos TxRef.rref
    | Unify of T.t * T.t * T.coercion TxRef.rref
    | Residuals of t * t
    | Skolems of T.kind Vector1.t * t
    | Axioms of (Name.t * T.ov * T.uv) Vector1.t * t

let combine r r' = Residuals (r, r')

