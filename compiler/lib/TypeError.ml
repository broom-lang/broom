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

let (^/^) = PPrint.(^/^)

let rec cause_to_doc s = function
    | Unbound name -> PPrint.string "unbound name" ^/^ Name.to_doc name
    | Unusable (template, typ) ->
        Fc.Type.to_doc s typ ^/^
        (match template with
        | PiL _ -> PPrint.string "is uncallable"
        | RecordL _ -> PPrint.string "is not a record"
        | TypeL _ -> PPrint.string "is not a type"
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
            | Sub (_, typ, _, super, _) -> cause_to_doc s (SubType (typ, super))
            | Unify (typ, typ', _) -> cause_to_doc s (Unify (typ, typ'))
        in to_doc residual
    | IncompleteImpl (uv, uv') ->
        Fc.Type.to_doc s (Uv uv) ^/^ PPrint.string "cannot be resolved with the underresolved"
            ^/^ Fc.Type.to_doc s (Uv uv')
    | ImpureType expr -> PPrint.string "impure type expression" ^/^ Ast.Term.Expr.to_doc expr
    | Escape ((name, _), _) -> Name.to_doc name ^/^ PPrint.string "would escape"
    | Occurs (uv, typ) -> Fc.Type.to_doc s (Uv uv) ^/^ PPrint.string "occurs in" ^/^ Fc.Type.to_doc s typ
    | Polytype typ -> Fc.Type.abs_to_doc s typ ^/^ PPrint.string "is not a monotype"
    | PolytypeInference typ -> PPrint.string "tried to infer polytype" ^/^ Fc.Type.abs_to_doc s typ
    | RecordArticulation typ ->
        PPrint.string "tried to articulate record type" ^/^ Fc.Type.to_doc s typ
    | RecordArticulationL typ ->
        PPrint.string "tried to articulate record type" ^/^ Fc.Type.locator_to_doc s typ

let to_doc s (({pos_fname; _}, _) as span : Util.span) err =
    PPrint.prefix 4 1 (PPrint.string "Type error in" ^/^ PPrint.string pos_fname ^/^ PPrint.string "at"
        ^/^ PPrint.string (Util.span_to_string span) ^/^ PPrint.colon)
        (cause_to_doc s err)

