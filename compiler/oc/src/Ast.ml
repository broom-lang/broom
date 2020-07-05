let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

type span = Lexing.position * Lexing.position

let pos_to_string ({pos_lnum = line; pos_bol = bol; pos_cnum = offset; pos_fname = _} : Lexing.position) =
    Int.to_string line ^ ":" ^ Int.to_string (offset - bol)
let span_to_string (pos, pos') = pos_to_string pos ^ "-" ^ pos_to_string pos'

type 'a with_pos = {v : 'a; pos: span}

module rec Term : sig
    type expr =
        | Fn of lvalue * expr with_pos
        | If of expr with_pos * expr with_pos * expr with_pos
        | App of expr with_pos * expr with_pos
        | Seal of expr with_pos * Type.t with_pos
        | Struct of def Vector.t
        | Select of expr with_pos * Name.t
        | Proxy of Type.t with_pos
        | Use of Name.t
        | Const of Const.t

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = span * lvalue * expr with_pos

    and lvalue = {pat : Name.t; ann: Type.t with_pos option}

    val expr_to_doc : expr -> PPrint.document
    val stmt_to_doc : stmt -> PPrint.document
end = struct
    type expr =
        | Fn of lvalue * expr with_pos
        | If of expr with_pos * expr with_pos * expr with_pos
        | App of expr with_pos * expr with_pos
        | Seal of expr with_pos * Type.t with_pos
        | Struct of def Vector.t
        | Select of expr with_pos * Name.t
        | Proxy of Type.t with_pos
        | Use of Name.t
        | Const of Const.t

    and stmt =
        | Def of def
        | Expr of expr with_pos

    and def = span * lvalue * expr with_pos

    and lvalue = {pat : Name.t; ann: Type.t with_pos option}

    let rec expr_to_doc = function
        | Fn (param, body) ->
            PPrint.string "fun" ^/^ lvalue_to_doc param ^/^ PPrint.string "=>" ^/^ expr_to_doc body.v
        | If (cond, conseq, alt) ->
            PPrint.string "if" ^/^ expr_to_doc cond.v
                ^/^ PPrint.string "then" ^/^ expr_to_doc conseq.v
                ^/^ PPrint.string "else" ^/^ expr_to_doc alt.v
        | App ({v = callee; _}, {v = arg; _}) -> callee_to_doc callee ^/^ arg_to_doc arg
        | Seal (expr, typ) ->
            PPrint.infix 4 1 (PPrint.string ":>") (sealee_to_doc expr.v) (Type.to_doc typ.v)
        | Struct defs ->
            PPrint.surround_separate_map 4 1 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
                def_to_doc (Vector.to_list defs)
        | Select ({v = record; _}, label) ->
            selectee_to_doc record ^^ PPrint.dot ^^ Name.to_doc label
        | Proxy {v = typ; _} -> PPrint.brackets (Type.to_doc typ)
        | Use name -> Name.to_doc name
        | Const v -> Const.to_doc v

    and callee_to_doc = function
        | (Fn _ | If _) as callee -> PPrint.parens (expr_to_doc callee)
        | callee -> expr_to_doc callee

    and arg_to_doc = function
        | (Fn _ | If _ | App _) as callee -> PPrint.parens (expr_to_doc callee)
        | callee -> expr_to_doc callee

    and sealee_to_doc = function
        | Fn _ as sealee -> PPrint.parens (expr_to_doc sealee)
        | sealee -> expr_to_doc sealee

    and selectee_to_doc = function
        | (Fn _ | If _ | App _) as callee -> PPrint.parens (expr_to_doc callee)
        | callee -> expr_to_doc callee

    and def_to_doc (_, def, {v = expr; _}) =
        lvalue_to_doc def ^/^ PPrint.equals ^/^ expr_to_doc expr

    and lvalue_to_doc = function
        | {pat; ann = Some {v = ann; _}} -> Name.to_doc pat ^/^ PPrint.colon ^/^ Type.to_doc ann
        | {pat; ann = None} -> Name.to_doc pat

    let stmt_to_doc = function
        | Def def -> def_to_doc def
        | Expr {v = expr; _} -> expr_to_doc expr
end

and Type : sig
    type t =
        | Pi of Name.t option decl * Effect.t * t with_pos
        | Sig of Name.t decl Vector.t
        | Path of Term.expr
        | Singleton of Term.expr with_pos
        | Type
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    val to_doc : t -> PPrint.document
end = struct
    type t =
        | Pi of Name.t option decl * Effect.t * t with_pos
        | Sig of Name.t decl Vector.t
        | Path of Term.expr
        | Singleton of Term.expr with_pos
        | Type
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    let rec to_doc = function
        | Pi (domain, eff, codomain) ->
            domain_to_doc domain ^/^ Effect.arrow eff ^/^ to_doc codomain.v
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

    and domain_to_doc = function
        | {name = Some name; typ} ->
            PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ to_doc typ.v)
        | {name = None; typ = {v = Pi _ as typ; _}} -> PPrint.parens (to_doc typ)
        | {name = None; typ} -> to_doc typ.v
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