type typ = ComplexFc.Type.t

type t =
    | NonPattern of Ast.Term.Expr.t
    | InvalidDecl of Ast.Term.Stmt.t
    | InvalidField of Ast.Term.Stmt.t
    | Unbound of Name.t
    (*| Unusable of Fc.Type.template * typ*)
    | TupleWidth of typ * int * Ast.Term.Expr.t * int
    | MissingField of typ * string
    | SubType of typ * typ
    | Unify of typ * typ
    | Unresolvable of typ * typ
    | IncompleteImpl of typ * typ
    | ImpureType of Ast.Term.Expr.t
    | Escape of typ
    | Occurs of typ * typ
    | Causes of t * t list

exception TypeError of Util.span * t

val to_doc : Util.span -> t -> PPrint.document

