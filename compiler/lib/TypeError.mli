type typ = Fc.Type.t
type abs = Fc.Type.abs

type error =
    | NonPattern of Ast.Term.Expr.t
    | InvalidDecl of Ast.Term.Stmt.t
    | InvalidField of Ast.Term.Stmt.t
    | Unbound of Name.t
    | Unusable of Fc.Type.template * typ
    | MissingField of typ * string
    | SubType of typ * typ
    | Unify of typ * typ
    | Unresolvable of Fc.Type.t * typ
    | Unsolvable of Residual.t
    | IncompleteImpl of Fc.Type.uv * Fc.Type.uv
    | ImpureType of Ast.Term.Expr.t
    | Escape of Fc.Type.ov
    | Occurs of Fc.Type.uv * typ
    | Polytype of abs
    | PolytypeInference of abs

exception TypeError of Util.span * error

val to_doc : Util.span -> Fc.Uv.subst -> error -> PPrint.document

