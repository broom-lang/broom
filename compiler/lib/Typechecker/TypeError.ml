module Type = GraphType.Type

type typ = Type.t

type t =
    | NonPattern of Ast.Term.Expr.t
    | InvalidDecl of Ast.Term.Stmt.t
    | InvalidField of Ast.Term.Stmt.t
    | Unbound of Name.t
    (*| Unusable of Type.template * typ*)
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

let rec cause_to_doc pos err =
    let open PPrint in
    match err with
    | NonPattern expr -> string "invalid pattern" ^/^ Ast.Term.Expr.to_doc {v = expr; pos}
    | InvalidDecl decl -> string "invalid declaration" ^/^ Ast.Term.Stmt.to_doc decl
    | InvalidField decl -> string "invalid record field" ^/^ Ast.Term.Stmt.to_doc decl
    | Unbound name -> string "unbound name" ^/^ Name.to_doc name
    (*| Unusable (template, typ) ->
        Type.to_doc s typ ^/^
        (match template with
        | TupleL min_length ->
            string "is not a tuple of at least" ^/^ string (Int.to_string min_length)
                ^/^ string "values")*)

    | TupleWidth (typ, typ_width, expr, expr_width) ->
        Ast.Term.Expr.to_doc {v = expr; pos} ^/^ string "has" ^/^ string (Int.to_string expr_width)
        ^/^ string "elements but expected type" ^/^ Type.to_doc typ ^/^ string "has"
        ^/^ string (Int.to_string typ_width)

    | MissingField (typ, label) -> Type.to_doc typ ^/^ string "is missing field" ^/^ string label
    | SubType (typ, super) -> Type.to_doc typ ^/^ string "is not a subtype of" ^/^ Type.to_doc super
    | Unify (typ, typ') -> Type.to_doc typ ^/^ string "does not unify with" ^/^ Type.to_doc typ'
    | Unresolvable (path, impl) ->
        Type.to_doc path ^/^ string "cannot be resolved with the unresolved" ^/^ Type.to_doc impl
    | IncompleteImpl (uv, uv') ->
        Type.to_doc uv ^/^ string "cannot be resolved with the underresolved" ^/^ Type.to_doc uv'

    | ImpureType expr -> string "impure type expression" ^/^ Ast.Term.Expr.to_doc {v = expr; pos}
    | Escape t -> Type.to_doc t ^/^ string "would escape"
    | Occurs (uv, typ) -> Type.to_doc uv ^/^ string "occurs in" ^/^ Type.to_doc typ
    | Causes (err, causes) ->
        cause_to_doc pos err
        ^/^ separate_map (twice hardline) (cause_to_doc pos) causes

let to_doc (({pos_fname; _}, _) as span : Util.span) err =
    PPrint.(prefix 4 1 (group @@ string "Type error in" ^/^ string pos_fname ^/^ string "at"
        ^/^ string (Util.span_to_string span) ^^ colon)
        (group @@ cause_to_doc span err))

