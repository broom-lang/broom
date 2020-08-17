type span = Util.span
type 'a with_pos = 'a Ast.with_pos
type abs = FcType.abs
type typ = FcType.typ
type ov = FcType.ov
type coercion = FcType.coercion

type lvalue = {name : Name.t; typ : typ}

type expr
    = Fn of FcType.binding Vector.t * lvalue * expr with_pos
    | App of expr with_pos * typ Vector.t * expr with_pos
    | Letrec of def Vector1.t * expr with_pos
    | LetType of FcType.binding Vector1.t * expr with_pos
    | Axiom of (Name.t * FcType.kind Vector.t * typ * typ) Vector1.t * expr with_pos
    | Cast of expr with_pos * coercion
    | Pack of typ Vector1.t * expr with_pos
    | Unpack of FcType.binding Vector1.t * lvalue * expr with_pos * expr with_pos
    | If of expr with_pos * expr with_pos * expr with_pos
    | Record of field Vector.t
    | Select of expr with_pos * string
    | Proxy of abs 
    | Use of Name.t
    | Const of Const.t
    | Patchable of expr with_pos ref

and def = span * lvalue * expr with_pos

and field = {label : string; expr : expr with_pos}

type stmt
    = Def of def
    | Expr of expr with_pos

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module Type = FcType
let coercion_to_doc = Type.coercion_to_doc

let lvalue_to_doc {name; typ} =
    PPrint.infix 4 1 PPrint.colon (Name.to_doc name) (Type.to_doc typ)

let rec expr_to_doc = function
    | Fn (universals, param, body) ->
        PPrint.prefix 4 1
            (PPrint.string "fun"
                 ^^ (PPrint.surround_separate_map 4 0 PPrint.empty
                         (PPrint.blank 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                         FcType.binding_to_doc (Vector.to_list universals)
                     ^^ PPrint.blank 1 ^^ PPrint.parens (lvalue_to_doc param))
                 ^^ PPrint.blank 1 ^^ PPrint.string "=>")
            (expr_to_doc body.v)
    | Letrec (defs, body) ->
        PPrint.group(
            PPrint.surround 4 1 (PPrint.string "letrec")
                (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) def_to_doc (Vector1.to_list defs)))
                (PPrint.string "in")
            ^/^ expr_to_doc body.v)
    | LetType (bindings, body) ->
        PPrint.group(
            PPrint.surround 4 1 (PPrint.string "let type")
                (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                    Type.binding_to_doc (Vector1.to_list bindings)))
                (PPrint.string "in")
            ^/^ expr_to_doc body.v)
    | If (cond, conseq, alt) ->
        PPrint.string "if" ^/^ expr_to_doc cond.v
            ^/^ PPrint.string "then" ^/^ expr_to_doc conseq.v
            ^/^ PPrint.string "else" ^/^ expr_to_doc alt.v
    | App (callee, targs, arg) ->
        PPrint.align (callee_to_doc callee.v
                      ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                            (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                            FcType.to_doc (Vector.to_list targs)
                      ^/^ arg_to_doc arg.v)
    | Axiom (axioms, body) ->
        PPrint.group(
            PPrint.surround 4 1 (PPrint.string "axiom")
                (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) axiom_to_doc (Vector1.to_list axioms)))
                (PPrint.string "in")
            ^/^ expr_to_doc body.v)
    | Cast ({v = expr; _}, coercion) ->
        PPrint.infix 4 1 (PPrint.string "|>") (castee_to_doc expr) (coercion_to_doc coercion)
    | Pack (existentials, impl) ->
        PPrint.string "pack" ^^ PPrint.blank 1
            ^^ PPrint.surround_separate 4 0 PPrint.empty
                PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                (Vector1.to_list (Vector1.map FcType.to_doc existentials) @ [expr_to_doc impl.v])
    | Unpack (existentials, lvalue, expr, body) ->
        PPrint.group(
            PPrint.surround 4 1
                (PPrint.string "unpack" ^^ PPrint.blank 1
                    ^^ PPrint.surround_separate 4 0 PPrint.empty
                        PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                        (Vector1.to_list (Vector1.map FcType.binding_to_doc existentials) @ [lvalue_to_doc lvalue])
                    ^^ PPrint.blank 1 ^^ PPrint.equals)
                (expr_to_doc expr.v)
                (PPrint.string "in")
            ^/^ expr_to_doc body.v)
    | Record defs ->
        PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
            PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
            field_to_doc (Vector.to_list defs)
    | Select (record, label) ->
        PPrint.prefix 4 0 (selectee_to_doc record.v) (PPrint.dot ^^ PPrint.string label)
    | Proxy typ -> PPrint.brackets (Type.abs_to_doc typ)
    | Use name -> Name.to_doc name
    | Const c -> Const.to_doc c
    | Patchable {contents} -> expr_to_doc contents.v

and callee_to_doc = function
    | (Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ | Unpack _) as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and arg_to_doc = function
    | (Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ | Unpack _ | App _) as arg -> PPrint.parens (expr_to_doc arg)
    | arg -> expr_to_doc arg

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

and castee_to_doc = function
    | Fn _ as callee -> PPrint.parens (expr_to_doc callee)
    | callee -> expr_to_doc callee

and selectee_to_doc = function
    | (Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ | If _ | App _) as selectee-> PPrint.parens (expr_to_doc selectee)
    | selectee -> expr_to_doc selectee

and def_to_doc ((_, lvalue, {v = expr; _}) : def) =
    PPrint.infix 4 1 PPrint.equals (lvalue_to_doc lvalue) (expr_to_doc expr)

and field_to_doc {label; expr} =
    PPrint.infix 4 1 PPrint.equals (PPrint.string label) (expr_to_doc expr.v)

let stmt_to_doc = function
    | Def def -> def_to_doc def
    | Expr {v = expr; _} -> expr_to_doc expr

let letrec defs body = match Vector1.of_vector defs with
    | Some defs -> Letrec (defs, body)
    | None -> body.v

