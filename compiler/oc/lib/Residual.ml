module T = Fc.Type

type t =
    | Sub of T.t * T.locator * T.t * Fc.Term.Expr.t Ast.with_pos ref
    | Unify of T.t * T.t * T.coercion ref
    | Residuals of t * t
    | Skolems of T.binding Vector1.t * t
    | Axioms of (Name.t * T.ov * T.uv) Vector1.t * t

let combine r r' = Residuals (r, r')

