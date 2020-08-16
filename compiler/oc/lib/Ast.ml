let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

(* FIXME: Printing syntax differs from parsed syntax: *)

type 'a with_pos = 'a Util.with_pos

module rec Term : AstSigs.TERM with type typ = Type.t = struct
    type typ = Type.t

    type expr =
        | Values of expr with_pos Vector.t
        | Fn of clause Vector.t
        | Thunk of stmt Vector.t
        | App of expr with_pos * expr with_pos Vector.t
        | AppSequence of expr with_pos Vector1.t
        | PrimApp of Primop.t * expr with_pos Vector.t
        | Let of def Vector1.t * expr with_pos
        | Begin of stmt Vector1.t * expr with_pos
        | Module of (pat with_pos * expr with_pos) option * def Vector.t
        | Ann of expr with_pos * typ with_pos
        | With of expr with_pos * Name.t * expr with_pos
        | Where of expr with_pos * Name.t * expr with_pos
        | Without of expr with_pos * Name.t
        | Record of stmt Vector.t
        | EmptyRecord
        | Select of expr with_pos * Name.t
        | Proxy of typ
        | Use of Name.t
        | Const of Const.t

    and clause = {pats : pat with_pos Vector.t; body : expr with_pos}

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = Util.span * pat with_pos * expr with_pos

    and pat = expr

    let rec expr_to_doc = function
        | Fn clauses ->
            PPrint.surround_separate_map 4 1 (PPrint.brackets PPrint.empty)
                PPrint.lbracket (PPrint.break 1 ^^ PPrint.bar ^^ PPrint.blank 1) PPrint.rbracket
                clause_to_doc (Vector.to_list clauses)
        (*| App ({v = callee; _}, {v = arg; _}) -> callee_to_doc callee ^/^ arg_to_doc arg*)
        | Let (defs, body) ->
            PPrint.surround 4 1 (PPrint.string "let")
                ((PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) def_to_doc
                    (Vector1.to_list defs)) ^^ PPrint.semi ^/^ PPrint.string "do" ^/^ expr_to_doc body.v)
                (PPrint.string "end")
        | Begin (stmts, expr) ->
            PPrint.surround_separate_map 4 1
                (PPrint.string "begin" ^/^ PPrint.string "end")
                (PPrint.string "begin") (PPrint.semi ^^ PPrint.break 1) (PPrint.string "end")
                stmt_to_doc (Vector1.to_list stmts @ [Expr expr])
        | Module (None, fields) when Vector.length fields = 0 ->
            PPrint.string "module" ^/^ PPrint.string "end"
        | Module (super, fields) ->
            let super_doc = match super with
                | Some (pat, expr) ->
                    (PPrint.string "extends") ^^ PPrint.blank 1 ^^
                        PPrint.infix 4 1 PPrint.equals (expr_to_doc pat.v)
                            (expr_to_doc expr.v ^^ PPrint.semi) ^^ PPrint.break 1
                | None -> PPrint.empty in
            PPrint.surround 4 1 (PPrint.string "module")
                (super_doc ^^ PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) def_to_doc
                    (Vector.to_list fields))
                (PPrint.string "end")
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
        | Proxy typ -> Type.to_doc typ
        | Use name -> Name.to_doc name
        | Const v -> Const.to_doc v

    and clause_to_doc {pats; body} =
        if Vector.length pats > 0
        then PPrint.separate_map (PPrint.break 1) (fun {Util.v; pos = _} -> expr_to_doc v)
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
        PPrint.infix 4 1 PPrint.equals (expr_to_doc pat.v) (expr_to_doc expr.v)

    and stmt_to_doc = function
        | Def def -> def_to_doc def
        | Expr expr -> PPrint.prefix 4 1 (PPrint.string "do") (expr_to_doc expr.v)
end

and Type : AstSigs.TYPE
    with type expr = Term.expr
    with type pat = Term.pat
= struct
    type expr = Term.expr
    type pat = Term.pat

    type t =
        | Pi of pat with_pos Vector.t * t with_pos * t with_pos
        | Interface of (Name.t * t with_pos) option * Name.t decl Vector.t
        | Record of t with_pos
        | With of t with_pos * Name.t * t with_pos
        | Where of t with_pos * Name.t * t with_pos
        | Without of t with_pos * Name.t
        | EmptyRow
        | Path of expr
        | Typeof of expr with_pos
        | Type
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    let rec to_doc = function
        (*| Pi (domain, eff, codomain) ->
            PPrint.infix 4 1 (Effect.arrow eff)
                (PPrint.string "pi" ^^ PPrint.blank 1
                    ^^ PPrint.separate_map (PPrint.break 1) (fun {Util.v; pos = _} -> Pattern.to_doc v)
                        (Vector.to_list domain))
                (to_doc codomain.v)*)
        | Interface (None, decls) when Vector.length decls = 0 ->
            PPrint.string "interface" ^/^ PPrint.string "end"
        | Interface (super, decls) ->
            let super_doc = match super with
                | Some (name, typ) ->
                    PPrint.infix 4 1 PPrint.equals (Name.to_doc name) (to_doc typ.v) ^^ PPrint.break 1
                | None -> PPrint.empty in
            PPrint.surround 4 1 (PPrint.string "interface")
                (super_doc ^^ PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) decl_to_doc
                    (Vector.to_list decls))
                (PPrint.string "end")
        | Record row -> row_to_doc (PPrint.lbrace ^^ PPrint.bar) row.v (PPrint.bar ^^ PPrint.rbrace)
        | (With _ | Where _ | Without _ | EmptyRow) as row ->
            row_to_doc (PPrint.lparen ^^ PPrint.bar) row (PPrint.bar ^^ PPrint.rparen)
        | Path expr -> Term.expr_to_doc expr
        | Typeof {v = expr; _} -> PPrint.parens (PPrint.equals ^/^ Term.expr_to_doc expr)
        | Type -> PPrint.string "type"
        | Prim pt -> Prim.to_doc pt

    and decl_to_doc {name; typ = {v = typ; _}} = Name.to_doc name ^/^ PPrint.colon ^/^ to_doc typ

    and row_to_doc l row r =
        let contents = match row with
            | With (super, label, typ) ->
                PPrint.infix 4 1 (PPrint.string "with")
                    (PPrint.prefix 4 1 (PPrint.string "...") (to_doc super.v))
                    (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (to_doc typ.v))
            | Where (super, label, typ) ->
                PPrint.infix 4 1 (PPrint.string "where")
                    (PPrint.prefix 4 1 (PPrint.string "...") (to_doc super.v))
                    (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (to_doc typ.v))
            | Without (super, label) ->
                PPrint.infix 4 1 (PPrint.string "without")
                    (PPrint.prefix 4 1 (PPrint.string "...") (to_doc super.v))
                    (Name.to_doc label)
            | EmptyRow -> PPrint.empty
            | typ -> to_doc typ in
        PPrint.surround 4 0 l contents r
end

