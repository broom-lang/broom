let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

type 'a with_pos = 'a Util.with_pos

module rec Term : AstSigs.TERM with type typ = Type.t and type pat = Pattern.t = struct
    type typ = Type.t
    type pat = Pattern.t

    type expr =
        | Fn of clause Vector.t
        | App of expr with_pos * expr with_pos
        | Begin of def Vector1.t * expr with_pos
        | Do of stmt Vector.t
        | Ann of expr with_pos * typ with_pos
        | With of expr with_pos * Name.t * expr with_pos
        | Where of expr with_pos * Name.t * expr with_pos
        | Without of expr with_pos * Name.t
        | EmptyRecord
        | Select of expr with_pos * Name.t
        | Proxy of typ with_pos
        | Use of Name.t
        | Const of Const.t

    and clause = {pats : pat with_pos Vector.t; body : expr with_pos}

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = Util.span * pat with_pos * expr with_pos

    let rec expr_to_doc = function
        | Fn clauses ->
            PPrint.surround_separate_map 4 1 (PPrint.brackets PPrint.empty)
                PPrint.lbracket (PPrint.break 1 ^^ PPrint.bar ^^ PPrint.blank 1) PPrint.rbracket
                clause_to_doc (Vector.to_list clauses)
        | App ({v = callee; _}, {v = arg; _}) -> callee_to_doc callee ^/^ arg_to_doc arg
        | Begin (defs, body) ->
            PPrint.surround 4 1 (PPrint.string "begin")
                ((PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) def_to_doc
                    (Vector1.to_list defs))
                    ^^ PPrint.semi ^^ PPrint.break 1 ^^ expr_to_doc body.v)
                (PPrint.string "end")
        | Do stmts ->
            PPrint.surround_separate_map 4 1
                (PPrint.string "do" ^/^ PPrint.string "end")
                (PPrint.string "do") (PPrint.semi ^^ PPrint.break 1) (PPrint.string "end")
                stmt_to_doc (Vector.to_list stmts)
        | Ann (expr, typ) ->
            PPrint.infix 4 1 PPrint.colon (sealee_to_doc expr.v) (Type.to_doc typ.v)
        | With (super, label, expr) ->
            PPrint.braces (PPrint.infix 4 1 (PPrint.string "with") (expr_to_doc super.v)
                (PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (expr_to_doc expr.v)))
        | Where (super, label, expr) ->
            PPrint.braces (PPrint.infix 4 1 (PPrint.string "where") (expr_to_doc super.v)
                (PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (expr_to_doc expr.v)))
        | Without (super, label) ->
            PPrint.braces (PPrint.infix 4 1 (PPrint.string "without") (expr_to_doc super.v)
                (Name.to_doc label))
        | EmptyRecord -> PPrint.braces PPrint.empty
        | Select ({v = record; _}, label) ->
            selectee_to_doc record ^^ PPrint.dot ^^ Name.to_doc label
        | Proxy {v = typ; _} -> PPrint.string "type" ^^ PPrint.blank 1 ^^ Type.to_doc typ
        | Use name -> Name.to_doc name
        | Const v -> Const.to_doc v

    and clause_to_doc {pats; body} =
        if Vector.length pats > 0
        then PPrint.separate_map (PPrint.break 1) (fun {Util.v; pos = _} -> Pattern.to_doc v)
            (Vector.to_list pats) ^/^ PPrint.string "->" ^/^ expr_to_doc body.v
        else expr_to_doc body.v

    and callee_to_doc = function
        | Fn _ as callee -> PPrint.parens (expr_to_doc callee)
        | callee -> expr_to_doc callee

    and arg_to_doc = function
        | (Fn _ | App _) as callee -> PPrint.parens (expr_to_doc callee)
        | callee -> expr_to_doc callee

    and sealee_to_doc = function
        | Fn _ as sealee -> PPrint.parens (expr_to_doc sealee)
        | sealee -> expr_to_doc sealee

    and selectee_to_doc = function
        | (Fn _ | App _) as callee -> PPrint.parens (expr_to_doc callee)
        | callee -> expr_to_doc callee

    and def_to_doc ((_, pat, expr) : def) =
        PPrint.string "val" ^^ PPrint.blank 1
            ^^ PPrint.infix 4 1 PPrint.equals (Pattern.to_doc pat.v) (expr_to_doc expr.v)

    and stmt_to_doc = function
        | Def def -> def_to_doc def
        | Expr expr -> expr_to_doc expr.v
end

and Pattern : AstSigs.PATTERN with type typ = Type.t = struct
    type typ = Type.t

    type t =
        | Ann of t with_pos * typ with_pos
        | Binder of Name.t
        | Ignore
        | Const of Const.t

    let rec to_doc = function
        | Ann (inner, typ) -> PPrint.infix 4 1 PPrint.colon (to_doc inner.v) (Type.to_doc typ.v)
        | Binder name -> Name.to_doc name
        | Ignore -> PPrint.string "_"
        | Const c -> Const.to_doc c
end

and Type : AstSigs.TYPE
    with type expr = Term.expr
    with type pat = Pattern.t
    with type eff = Effect.t
= struct
    type expr = Term.expr
    type pat = Pattern.t
    type eff = Effect.t

    type t =
        | Pi of pat with_pos Vector.t * eff * t with_pos
        | Sig of Name.t decl Vector.t
        | Path of expr
        | Singleton of expr with_pos
        | Type
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    let rec to_doc = function
        | Pi (domain, eff, codomain) ->
            PPrint.infix 4 1 (Effect.arrow eff)
                (PPrint.string "pi" ^^ PPrint.blank 1
                    ^^ PPrint.separate_map (PPrint.break 1) (fun {Util.v; pos = _} -> Pattern.to_doc v)
                        (Vector.to_list domain))
                (to_doc codomain.v)
        | Sig decls ->
            PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
                decl_to_doc (Vector.to_list decls)
        | Path expr -> Term.expr_to_doc expr
        | Singleton {v = expr; _} -> PPrint.parens (PPrint.equals ^/^ Term.expr_to_doc expr)
        | Type -> PPrint.string "type"
        | Prim pt -> Prim.to_doc pt

    and decl_to_doc {name; typ = {v = typ; _}} =
        PPrint.string "val" ^/^ Name.to_doc name ^/^ PPrint.colon ^/^ to_doc typ
end

and Effect : sig
    type t = Pure | Impure

    val to_doc : t -> PPrint.document
    val arrow : t -> PPrint.document
end = struct
    type t = Pure | Impure

    let to_doc = function
        | Pure -> PPrint.string "pure"
        | Impure -> PPrint.string "impure"

    let arrow = function
        | Pure -> PPrint.string "=>"
        | Impure -> PPrint.string "->"
end
