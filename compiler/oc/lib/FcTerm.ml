module Type = FcType

type 'a with_pos = 'a Ast.with_pos
type abs = Type.abs
type typ = Type.typ
type ov = Type.ov
type coercion = Type.coercion

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module rec Expr : FcSigs.EXPR
    with type def = Stmt.def
    with type stmt = Stmt.t
= struct
    type def = Stmt.def
    type stmt = Stmt.t

    type lvalue = {name : Name.t; typ : typ}

    type t
        = Fn of FcType.binding Vector.t * lvalue Vector.t * t with_pos
        | App of t with_pos * typ Vector.t * t with_pos Vector.t
        | Let of def * t with_pos
        | Letrec of def Vector1.t * t with_pos
        | LetType of FcType.binding Vector1.t * t with_pos
        | Axiom of (Name.t * FcType.kind Vector.t * typ * typ) Vector1.t * t with_pos
        | Cast of t with_pos * coercion
        | Pack of typ Vector1.t * t with_pos
        | Unpack of FcType.binding Vector1.t * lvalue * t with_pos * t with_pos
        | Record of field Vector.t
        | Select of t with_pos * string
        | Proxy of abs 
        | Use of Name.t
        | Const of Const.t
        | Patchable of t with_pos ref

    and field = {label : string; expr : t with_pos}

    let coercion_to_doc = Type.coercion_to_doc

    let lvalue_to_doc {name; typ} =
        PPrint.infix 4 1 PPrint.colon (Name.to_doc name) (Type.to_doc typ)

    let rec to_doc {Util.v = expr; pos = _} = match expr with
        | Fn (universals, params, body) ->
            PPrint.prefix 4 1
                (PPrint.string "fun"
                     ^^ (PPrint.surround_separate_map 4 0 PPrint.empty
                             (PPrint.blank 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                             FcType.binding_to_doc (Vector.to_list universals)
                         ^^ PPrint.blank 1
                         ^^ PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                            PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                            lvalue_to_doc (Vector.to_list params))
                     ^^ PPrint.blank 1 ^^ PPrint.string "=>")
                (to_doc body)
        | Let (def, body) ->
            PPrint.surround 4 1 (PPrint.string "let") (Stmt.def_to_doc def) (PPrint.string "in")
                ^/^ to_doc body
        | Letrec (defs, body) ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "letrec")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                        Stmt.def_to_doc (Vector1.to_list defs)))
                    (PPrint.string "in")
                ^/^ to_doc body)
        | LetType (bindings, body) ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "let type")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                        Type.binding_to_doc (Vector1.to_list bindings)))
                    (PPrint.string "in")
                ^/^ to_doc body)
        | App (callee, targs, args) ->
            PPrint.align (to_doc callee
                          ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                                (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                                FcType.to_doc (Vector.to_list targs)
                          ^/^ PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                                to_doc (Vector.to_list args))
        | Axiom (axioms, body) ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "axiom")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) axiom_to_doc (Vector1.to_list axioms)))
                    (PPrint.string "in")
                ^/^ to_doc body)
        | Cast (castee, coercion) ->
            PPrint.infix 4 1 (PPrint.string "|>") (castee_to_doc castee) (coercion_to_doc coercion)
        | Pack (existentials, impl) ->
            PPrint.string "pack" ^^ PPrint.blank 1
                ^^ PPrint.surround_separate 4 0 PPrint.empty
                    PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                    (Vector1.to_list (Vector1.map FcType.to_doc existentials) @ [to_doc impl])
        | Unpack (existentials, lvalue, expr, body) ->
            PPrint.group(
                PPrint.surround 4 1
                    (PPrint.string "unpack" ^^ PPrint.blank 1
                        ^^ PPrint.surround_separate 4 0 PPrint.empty
                            PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                            (Vector1.to_list (Vector1.map FcType.binding_to_doc existentials) @ [lvalue_to_doc lvalue])
                        ^^ PPrint.blank 1 ^^ PPrint.equals)
                    (to_doc expr)
                    (PPrint.string "in")
                ^/^ to_doc body)
        | Record defs ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                field_to_doc (Vector.to_list defs)
        | Select (record, label) ->
            PPrint.prefix 4 0 (selectee_to_doc record) (PPrint.dot ^^ PPrint.string label)
        | Proxy typ -> PPrint.brackets (Type.abs_to_doc typ)
        | Use name -> Name.to_doc name
        | Const c -> Const.to_doc c
        | Patchable {contents} -> to_doc contents

    and axiom_to_doc (name, universals, l, r) = match Vector.to_list universals with
        | _ :: _ ->
            PPrint.infix 4 1 PPrint.colon (Name.to_doc name)
                (PPrint.infix 4 1 PPrint.tilde
                    (Type.universal_to_doc universals (FcType.to_doc l))
                    (Type.universal_to_doc universals (FcType.to_doc r)))
        | [] ->
            PPrint.infix 4 1 PPrint.colon (Name.to_doc name)
                (PPrint.infix 4 1 PPrint.tilde
                    (Type.to_doc l)
                    (Type.to_doc r))

    and castee_to_doc (castee : t with_pos) = match castee.v with
        | Fn _ -> PPrint.parens (to_doc castee)
        | _ -> to_doc castee

    and selectee_to_doc (selectee : t with_pos) = match selectee.v with
        | Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ | App _ -> PPrint.parens (to_doc selectee)
        | _ -> to_doc selectee

    and field_to_doc {label; expr} =
        PPrint.infix 4 1 PPrint.equals (PPrint.string label) (to_doc expr)

    let letrec defs body = match Vector1.of_vector defs with
        | Some defs -> Letrec (defs, body)
        | None -> body.v
end

and Stmt : FcSigs.STMT
    with type lvalue = Expr.lvalue
    with type expr = Expr.t
= struct
    type lvalue = Expr.lvalue
    type expr = Expr.t

    type def = Util.span * lvalue * expr with_pos

    type t
        = Def of def
        | Expr of Expr.t with_pos

    let def_to_doc ((_, lvalue, expr) : def) =
        PPrint.infix 4 1 PPrint.equals (Expr.lvalue_to_doc lvalue) (Expr.to_doc expr)

    let to_doc = function
        | Def def -> def_to_doc def
        | Expr expr -> Expr.to_doc expr
end

