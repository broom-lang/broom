type typ = Fc.Type.t

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
    | Unresolvable of Fc.Type.t * typ
    | IncompleteImpl of Fc.Type.t * Fc.Type.t
    | ImpureType of Ast.Term.Expr.t
    | Escape of Fc.Type.t
    | Occurs of Fc.Type.t * typ
    | Causes of t * t list

exception TypeError of Util.span * t

val to_doc : Util.span -> t -> PPrint.document

