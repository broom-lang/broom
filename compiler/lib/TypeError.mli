type typ = Fc.Type.t
type abs = Fc.Type.abs

type error =
    | Unbound of Name.t
    | Unusable of Fc.Type.locator * typ
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
    | RecordArticulation of typ
    | RecordArticulationL of Fc.Type.locator

exception TypeError of Util.span * error

val to_doc : Fc.Uv.subst -> Util.span -> error -> PPrint.document

