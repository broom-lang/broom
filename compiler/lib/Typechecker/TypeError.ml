type typ = Fc.Type.t

type t =
    | NonPattern of Ast.Term.Expr.t
    | InvalidDecl of Ast.Term.Stmt.t
    | InvalidField of Ast.Term.Stmt.t
    | Unbound of Name.t
    | Unusable of Fc.Type.template * typ
    | TupleWidth of typ * int * Ast.Term.Expr.t * int
    | MissingField of typ * string
    | SubType of typ * typ
    | Unify of typ * typ
    | Unresolvable of Fc.Type.t * typ
    | Unsolvable of Residual.t
    | IncompleteImpl of Fc.Type.uv * Fc.Type.uv
    | ImpureType of Ast.Term.Expr.t
    | Escape of Fc.Type.ov
    | Occurs of Fc.Type.uv * typ

exception TypeError of Util.span * t

let rec cause_to_doc s pos err =
    let open PPrint in
    match err with
    | NonPattern expr -> string "invalid pattern" ^/^ Ast.Term.Expr.to_doc {v = expr; pos}
    | InvalidDecl decl -> string "invalid declaration" ^/^ Ast.Term.Stmt.to_doc decl
    | InvalidField decl -> string "invalid record field" ^/^ Ast.Term.Stmt.to_doc decl
    | Unbound name -> string "unbound name" ^/^ Name.to_doc name
    | Unusable (template, typ) ->
        Fc.Type.to_doc s typ ^/^
        (match template with
        | TupleL min_length ->
            string "is not a tuple of at least" ^/^ string (Int.to_string min_length)
                ^/^ string "values")

    | TupleWidth (typ, typ_width, expr, expr_width) ->
        Ast.Term.Expr.to_doc {v = expr; pos} ^/^ string "has" ^/^ string (Int.to_string expr_width)
        ^/^ string "elements but expected type" ^/^ Fc.Type.to_doc s typ ^/^ string "has"
        ^/^ string (Int.to_string typ_width)

    | MissingField (typ, label) -> Fc.Type.to_doc s typ ^/^ string "is missing field" ^/^ string label
    | SubType (typ, super) -> Fc.Type.to_doc s typ ^/^ string "is not a subtype of" ^/^ Fc.Type.to_doc s super
    | Unify (typ, typ') -> Fc.Type.to_doc s typ ^/^ string "does not unify with" ^/^ Fc.Type.to_doc s typ'
    | Unresolvable (path, impl) ->
        Fc.Type.to_doc s path ^/^ string "cannot be resolved with the unresolved" ^/^ Fc.Type.to_doc s impl
    | Unsolvable residual ->
        let rec to_doc : Residual.t -> document = function
            | Axioms (_, residual) | Skolems (_, residual) -> to_doc residual
            | Residuals (residual, residual') ->
                to_doc residual ^/^ string "and" ^/^ to_doc residual'
            | Sub (typ, super, _) -> cause_to_doc s pos (SubType (typ, super))
            | Unify (typ, typ', _) -> cause_to_doc s pos (Unify (typ, typ'))
        in to_doc residual

    | IncompleteImpl (uv, uv') ->
        Fc.Type.to_doc s (Uv uv) ^/^ string "cannot be resolved with the underresolved"
            ^/^ Fc.Type.to_doc s (Uv uv')

    | ImpureType expr -> string "impure type expression" ^/^ Ast.Term.Expr.to_doc {v = expr; pos}
    | Escape ((name, _), _) -> Name.to_doc name ^/^ string "would escape"
    | Occurs (uv, typ) -> Fc.Type.to_doc s (Uv uv) ^/^ string "occurs in" ^/^ Fc.Type.to_doc s typ

let to_doc (({pos_fname; _}, _) as span : Util.span) s err =
    PPrint.(prefix 4 1 (string "Type error in" ^/^ string pos_fname ^/^ string "at"
        ^/^ string (Util.span_to_string span) ^/^ colon)
        (cause_to_doc s span err))

