type typ = Fc.Type.t

type t =
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

exception TypeError of Util.span * t

let (^/^) = PPrint.(^/^)

let rec cause_to_doc s pos = function
    | NonPattern expr -> PPrint.string "invalid pattern" ^/^ Ast.Term.Expr.to_doc {v = expr; pos}
    | InvalidDecl decl -> PPrint.string "invalid declaration" ^/^ Ast.Term.Stmt.to_doc decl
    | InvalidField decl -> PPrint.string "invalid record field" ^/^ Ast.Term.Stmt.to_doc decl
    | Unbound name -> PPrint.string "unbound name" ^/^ Name.to_doc name
    | Unusable (template, typ) ->
        Fc.Type.to_doc s typ ^/^
        (match template with
        | ValuesL min_length ->
            PPrint.string "is not a tuple of at least" ^/^ PPrint.string (Int.to_string min_length)
                ^/^ PPrint.string "values"
        | PiL _ -> PPrint.string "is uncallable"
        | WithL {base = _; label; field = _} -> PPrint.string "lacks the field" ^/^ Name.to_doc label
        | ProxyL _ -> PPrint.string "is not a type"
        | Hole -> failwith "unreachable: Unusable as Hole")
    | MissingField (typ, label) -> Fc.Type.to_doc s typ ^/^ PPrint.string "is missing field" ^/^ PPrint.string label
    | SubType (typ, super) -> Fc.Type.to_doc s typ ^/^ PPrint.string "is not a subtype of" ^/^ Fc.Type.to_doc s super
    | Unify (typ, typ') -> Fc.Type.to_doc s typ ^/^ PPrint.string "does not unify with" ^/^ Fc.Type.to_doc s typ'
    | Unresolvable (path, impl) ->
        Fc.Type.to_doc s path ^/^ PPrint.string "cannot be resolved with the unresolved"
            ^/^ Fc.Type.to_doc s impl
    | Unsolvable residual ->
        let rec to_doc : Residual.t -> PPrint.document = function
            | Axioms (_, residual) | Skolems (_, residual) -> to_doc residual
            | Residuals (residual, residual') ->
                to_doc residual ^/^ PPrint.string "and" ^/^ to_doc residual'
            | Sub (_, typ, super, _) -> cause_to_doc s pos (SubType (typ, super))
            | Unify (typ, typ', _) -> cause_to_doc s pos (Unify (typ, typ'))
        in to_doc residual
    | IncompleteImpl (uv, uv') ->
        Fc.Type.to_doc s (Uv uv) ^/^ PPrint.string "cannot be resolved with the underresolved"
            ^/^ Fc.Type.to_doc s (Uv uv')
    | ImpureType expr -> PPrint.string "impure type expression" ^/^ Ast.Term.Expr.to_doc {v = expr; pos}
    | Escape ((name, _), _) -> Name.to_doc name ^/^ PPrint.string "would escape"
    | Occurs (uv, typ) -> Fc.Type.to_doc s (Uv uv) ^/^ PPrint.string "occurs in" ^/^ Fc.Type.to_doc s typ

let to_doc (({pos_fname; _}, _) as span : Util.span) s err =
    PPrint.prefix 4 1 (PPrint.string "Type error in" ^/^ PPrint.string pos_fname ^/^ PPrint.string "at"
        ^/^ PPrint.string (Util.span_to_string span) ^/^ PPrint.colon)
        (cause_to_doc s span err)

