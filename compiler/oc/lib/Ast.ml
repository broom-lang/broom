let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

(* FIXME: Printing syntax differs from parsed syntax: *)

type 'a with_pos = 'a Util.with_pos

module rec Term : AstSigs.TERM with type typ = Type.t = struct
    type typ = Type.t

    type expr =
        | Values of expr with_pos Vector.t
        | Ann of expr with_pos * typ with_pos
        | Fn of clause Vector.t
        | Thunk of stmt Vector.t
        | App of expr with_pos * expr with_pos Vector.t
        | AppSequence of expr with_pos Vector1.t
        | PrimApp of Primop.t * expr with_pos Vector.t
        | Record of stmt Vector.t
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
        | Values val_exprs ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (fun {Util.v = expr; _} -> expr_to_doc expr) (Vector.to_list val_exprs)
        | Fn clauses ->
            PPrint.surround_separate_map 4 0 (PPrint.brackets PPrint.empty)
                PPrint.lbracket (PPrint.break 1 ^^ PPrint.bar ^^ PPrint.blank 1) PPrint.rbracket
                clause_to_doc (Vector.to_list clauses)
        | Thunk stmts ->
            PPrint.surround_separate_map 4 0 (PPrint.brackets PPrint.empty)
                PPrint.lbracket (PPrint.semi ^^ PPrint.break 1) PPrint.rbracket
                stmt_to_doc (Vector.to_list stmts)
        | App (callee, args) -> expr_to_doc callee.v
            ^/^ PPrint.separate_map (PPrint.break 1) (fun {Util.v = expr; _} -> expr_to_doc expr)
                (Vector.to_list args)
        | AppSequence exprs ->
            PPrint.separate_map (PPrint.break 1) (fun {Util.v = expr; _} -> expr_to_doc expr)
                (Vector1.to_list exprs)
        | PrimApp (callee, args) -> Primop.to_doc callee
            ^/^ PPrint.separate_map (PPrint.break 1) (fun {Util.v = expr; _} -> expr_to_doc expr)
                (Vector.to_list args)
        | Ann (expr, typ) ->
            PPrint.infix 4 1 PPrint.colon (expr_to_doc expr.v) (Type.to_doc typ.v)
        | Record stmts ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
                stmt_to_doc (Vector.to_list stmts)
        | Select ({v = record; _}, label) -> expr_to_doc record ^^ PPrint.dot ^^ Name.to_doc label
        | Proxy typ -> Type.to_doc typ
        | Use name -> Name.to_doc name
        | Const v -> Const.to_doc v

    and clause_to_doc {pats; body} =
        if Vector.length pats > 0
        then PPrint.separate_map (PPrint.break 1) (fun {Util.v; pos = _} -> expr_to_doc v)
            (Vector.to_list pats) ^/^ PPrint.string "->" ^/^ expr_to_doc body.v
        else expr_to_doc body.v

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
        | Pi of pat with_pos * t with_pos * t with_pos
        | Record of t with_pos
        | EmptyRow
        | Path of expr
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    let rec to_doc = function
        | Pi (domain, eff, codomain) ->
            PPrint.infix 4 1 (PPrint.string "->") (Term.expr_to_doc domain.v)
                (PPrint.infix 4 1 PPrint.bang (to_doc eff.v) (to_doc codomain.v))
        | Record row -> PPrint.braces (to_doc row.v)
        | EmptyRow -> PPrint.parens (PPrint.string "||")
        | Path expr -> Term.expr_to_doc expr
        | Prim pt -> Prim.to_doc pt
end

