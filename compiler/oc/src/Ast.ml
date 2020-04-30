type span = Lexing.position * Lexing.position

type 'a with_pos = {v : 'a; pos: span}

type domain = {name : Name.t option; typ : typ with_pos}

and lvalue = {pat : Name.t; ann: typ with_pos option}

and effect = Pure | Impure

and typ
    = Pi of domain * effect * typ with_pos
    | Sig of decl list
    | Path of expr
    | Singleton of expr with_pos
    | Type
    | Int
    | Bool

and decl = {name : Name.t; typ : typ with_pos}

and expr
    = Fn of lvalue * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | App of expr with_pos * expr with_pos
    | Seal of expr with_pos * typ with_pos
    | Struct of def list
    | Select of expr with_pos * Name.t
    | Proxy of typ
    | Use of Name.t
    | Const of int

and def = span * lvalue * expr with_pos

and stmt
    = Def of def
    | Expr of expr with_pos

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

let rec typ_to_doc = function
    | Pi (domain, eff, codomain) ->
        domain_to_doc domain ^/^ effect_arrow eff ^/^ typ_to_doc codomain.v
    | Sig decls ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
            decl_to_doc decls
    | Path expr -> expr_to_doc expr
    | Singleton {v = expr; _} -> PPrint.parens (PPrint.equals ^/^ expr_to_doc expr)
    | Type -> PPrint.string "type"
    | Int -> PPrint.string "__int"
    | Bool -> PPrint.string "__bool"

and domain_to_doc = function
    | {name = Some name; typ} ->
        PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ typ_to_doc typ.v)
    | {name = None; typ = {v = Pi _ as typ; _}} -> PPrint.parens (typ_to_doc typ)
    | {name = None; typ} -> typ_to_doc typ.v

and effect_to_doc = function
    | Pure -> PPrint.string "pure"
    | Impure -> PPrint.string "impure"

and effect_arrow = function
    | Pure -> PPrint.string "=>"
    | Impure -> PPrint.string "->"

and decl_to_doc {name; typ = {v = typ; _}} =
    PPrint.string "val" ^/^ Name.to_doc name ^/^ PPrint.colon ^/^ typ_to_doc typ

and lvalue_to_doc = function
    | {pat; ann = Some {v = ann; _}} -> Name.to_doc pat ^/^ PPrint.colon ^/^ typ_to_doc ann
    | {pat; ann = None} -> Name.to_doc pat

and expr_to_doc = function
    | Fn (param, body) ->
        PPrint.string "fun" ^/^ lvalue_to_doc param ^/^ PPrint.string "=>" ^/^ expr_to_doc body.v
    | If (cond, conseq, alt) ->
        PPrint.string "if" ^/^ expr_to_doc cond.v
            ^/^ PPrint.string "then" ^/^ expr_to_doc conseq.v
            ^/^ PPrint.string "else" ^/^ expr_to_doc alt.v
    | App ({v = callee; _}, {v = arg; _}) -> callee_to_doc callee ^/^ arg_to_doc arg
    | Struct defs ->
        PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
            def_to_doc defs
    | Select ({v = record; _}, label) ->
        selectee_to_doc record ^^ PPrint.dot ^^ Name.to_doc label
    | Proxy typ -> PPrint.brackets (typ_to_doc typ)
    | Use name -> Name.to_doc name
    | Const v -> PPrint.string (Int.to_string v)

and callee_to_doc = function
    | (Fn _ | If _) as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and arg_to_doc = function
    | (Fn _ | If _ | App _) as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and selectee_to_doc = function
    | (Fn _ | If _ | App _) as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and def_to_doc (_, def, {v = expr; _}) =
    lvalue_to_doc def ^/^ PPrint.equals ^/^ expr_to_doc expr

let stmt_to_doc = function
    | Def def -> def_to_doc def
    | Expr {v = expr; _} -> expr_to_doc expr

