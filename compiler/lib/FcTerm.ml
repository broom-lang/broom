open Streaming

module Make (Type : FcSigs.TYPE) : FcSigs.TERM
    with module Type = Type
= struct 

module Type = Type

type 'a with_pos = 'a Util.with_pos
type typ = Type.typ
type coercion = Type.coercion

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module rec Expr : FcSigs.EXPR
    with module Type = Type
    with type def = Stmt.def
    with type stmt = Stmt.t
= struct
    module Type = Type

    type def = Stmt.def
    type stmt = Stmt.t

    let (!) = TxRef.(!)
    let ref = TxRef.ref

    type lvalue = {name : Name.t; typ : Type.t}

    type t =
        | Values of t with_pos Vector.t
        | Focus of t with_pos * int

        | Fn of Type.binding Vector.t * lvalue * t with_pos
        | App of t with_pos * Type.t Vector.t * t with_pos
        | PrimApp of Primop.t * Type.t Vector.t * t with_pos

        | Let of def * t with_pos
        | Letrec of def Vector1.t * t with_pos
        | LetType of Type.binding Vector1.t * t with_pos
        | Match of t with_pos * clause Vector.t

        | Axiom of (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t * t with_pos
        | Cast of t with_pos * Type.coercion

        | Pack of Type.t Vector1.t * t with_pos
        | Unpack of Type.binding Vector1.t * lvalue * t with_pos * t with_pos

        | Record of (Name.t * t with_pos) Vector.t
        | Where of t with_pos * (Name.t * t with_pos) Vector1.t
        | With of {base : t with_pos; label : Name.t; field : t with_pos}
        | Select of t with_pos * Name.t

        | Proxy of Type.t
        | Const of Const.t

        | Use of Name.t

        | Patchable of t with_pos TxRef.rref

    and pat =
        | ValuesP of pat with_pos Vector.t
        | AppP of t with_pos * pat with_pos Vector.t
        | ProxyP of Type.t
        | UseP of Name.t
        | ConstP of Const.t

    and clause = {pat : pat with_pos; body : t with_pos}

    and field = {label : string; expr : t with_pos}

    let coercion_to_doc = Type.coercion_to_doc

    let rec to_doc s {Util.v = expr; pos = _} = match expr with
        | Values exprs ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (to_doc s) (Vector.to_list exprs)
        | Focus (expr, i) -> selectee_to_doc s expr ^^ PPrint.dot ^^ PPrint.string (Int.to_string i)
        | Fn (universals, param, body) ->
            PPrint.prefix 4 1
                (PPrint.string "fun"
                     ^^ (PPrint.surround_separate_map 4 0 PPrint.empty
                             (PPrint.blank 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                             (Type.binding_to_doc s) (Vector.to_list universals)
                         ^^ PPrint.blank 1 ^^ lvalue_to_doc s param)
                     ^^ PPrint.blank 1 ^^ PPrint.string "->")
                (to_doc s body)
        | Let (def, body) ->
            PPrint.surround 4 1 (PPrint.string "let") (Stmt.def_to_doc s def) (PPrint.string "in")
                ^/^ to_doc s body
        | Letrec (defs, body) ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "letrec")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                        (Stmt.def_to_doc s) (Vector1.to_list defs)))
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | LetType (bindings, body) ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "let type")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                        (Type.binding_to_doc s) (Vector1.to_list bindings)))
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | Match (matchee, clauses) ->
            let start = PPrint.string "match" ^^ PPrint.blank 1 ^^ to_doc s matchee in
            PPrint.surround_separate_map 4 1 (start ^/^ PPrint.string "end")
                start (PPrint.break 1) (PPrint.string "end")
                (clause_to_doc s) (Vector.to_list clauses)
        | App (callee, targs, arg) ->
            PPrint.align (to_doc s callee
                          ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                                (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                                (Type.to_doc s) (Vector.to_list targs)
                          ^/^ to_doc s arg)
        | PrimApp (op, targs, arg) ->
            PPrint.align (PPrint.string "__" ^^ Primop.to_doc op
                          ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                                (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                                (Type.to_doc s) (Vector.to_list targs)
                          ^/^ to_doc s arg)
        | Axiom (axioms, body) ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "axiom")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) (axiom_to_doc s)
                        (Vector1.to_list axioms)))
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | Cast (castee, coercion) ->
            PPrint.infix 4 1 (PPrint.string "|>") (castee_to_doc s castee) (coercion_to_doc s coercion)
        | Pack (existentials, impl) ->
            PPrint.string "pack" ^^ PPrint.blank 1
                ^^ PPrint.surround_separate 4 0 PPrint.empty
                    PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                    (Vector1.to_list (Vector1.map (Type.to_doc s) existentials) @ [to_doc s impl])
        | Unpack (existentials, lvalue, expr, body) ->
            PPrint.group(
                PPrint.surround 4 1
                    (PPrint.string "unpack" ^^ PPrint.blank 1
                        ^^ PPrint.surround_separate 4 0 PPrint.empty
                            PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                            (Vector1.to_list (Vector1.map (Type.binding_to_doc s) existentials)
                                @ [lvalue_to_doc s lvalue])
                        ^^ PPrint.blank 1 ^^ PPrint.equals)
                    (to_doc s expr)
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | Record fields ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                (fun (label, field) -> PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc s field))
                (Vector.to_list fields)
        | Where (base, fields) ->
            PPrint.infix 4 1 (PPrint.string "where")
                (to_doc s base)
                (PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                    PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                    (fun (label, field) -> PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc s field))
                    (Vector1.to_list fields))
        | With {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (base_to_doc s base)
                (PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc s field))
        | Select (record, label) ->
            PPrint.prefix 4 0 (selectee_to_doc s record) (PPrint.dot ^^ Name.to_doc label)
        | Proxy typ -> PPrint.brackets (Type.to_doc s typ)
        | Use name -> Name.to_doc name
        | Const c -> Const.to_doc c
        | Patchable ref -> to_doc s !ref

    and axiom_to_doc s (name, universals, l, r) = match Vector.to_list universals with
        | _ :: _ ->
            PPrint.infix 4 1 PPrint.colon (Name.to_doc name)
                (PPrint.infix 4 1 PPrint.tilde
                    (Type.universal_to_doc s universals (Type.to_doc s l))
                    (Type.universal_to_doc s universals (Type.to_doc s r)))
        | [] ->
            PPrint.infix 4 1 PPrint.colon (Name.to_doc name)
                (PPrint.infix 4 1 PPrint.tilde
                    (Type.to_doc s l)
                    (Type.to_doc s r))

    and clause_to_doc s {pat; body} =
        PPrint.bar ^^ PPrint.blank 1
            ^^ PPrint.infix 4 1 (PPrint.string "->")
                (pat_to_doc s pat) (to_doc s body)

    and castee_to_doc s (castee : t with_pos) = match castee.v with
        | Fn _ -> PPrint.parens (to_doc s castee)
        | _ -> to_doc s castee

    and base_to_doc s (base : t with_pos) = match base.v with
        | Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ -> PPrint.parens (to_doc s base)
        | _ -> to_doc s base

    and selectee_to_doc s (selectee : t with_pos) = match selectee.v with
        | Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ | App _ | Where _ | With _ ->
            PPrint.parens (to_doc s selectee)
        | _ -> to_doc s selectee

    and lvalue_to_doc s {name; typ} =
        PPrint.infix 4 1 PPrint.colon (Name.to_doc name) (Type.to_doc s typ)

    and pat_to_doc s (pat : pat with_pos) = match pat.v with
        | ValuesP pats ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (pat_to_doc s) (Vector.to_list pats)
        | AppP (callee, args) ->
            PPrint.align (to_doc s callee
                ^/^ PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                    PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                    (pat_to_doc s) (Vector.to_list args))
        | ProxyP typ -> PPrint.brackets (Type.to_doc s typ)
        | UseP name -> Name.to_doc name
        | ConstP c -> Const.to_doc c

    and field_to_doc s {label; expr} =
        PPrint.infix 4 1 PPrint.equals (PPrint.string label) (to_doc s expr)

    let letrec defs body = match Vector1.of_vector defs with
        | Some defs -> Letrec (defs, body)
        | None -> body.v

    let map_children f (expr : t with_pos) =
        let v = expr.v in
        let v' = match v with
            | Values vals ->
                let vals' = Vector.map f vals in
                let noop = Stream.from (Source.zip_with (==)
                        (Vector.to_source vals') (Vector.to_source vals))
                    |> Stream.into (Sink.all ~where: Fun.id) in
                if noop then v else Values vals'

            | Focus (tuple, i) ->
                let tuple' = f tuple in
                if tuple' == tuple then v else Focus (tuple', i)

            | Fn (universals, param, body) ->
                let body' = f body in
                if body' == body then v else Fn (universals, param, body')

            | App (callee, universals, arg) ->
                let callee' = f callee in
                let arg' = f arg in
                if callee' == callee && arg' == arg then v else App (callee', universals, arg')

            | PrimApp (op, universals, arg) ->
                let arg' = f arg in
                if arg' == arg then v else PrimApp (op, universals, arg')

            | Let ((pos, def, expr), body) ->
                let expr' = f expr in
                let body' = f body in
                if expr' == expr && body' == body then v else Let ((pos, def, expr'), body')

            | Letrec (defs, body) ->
                let defs' = Vector1.map (fun (pos, def, expr) -> (pos, def, f expr)) defs in
                let body' = f body in
                if body' == body
                    && Stream.from (Source.zip_with (fun (_, _, expr') (_, _, expr) -> expr' == expr)
                        (Vector1.to_source defs') (Vector1.to_source defs))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then v
                else Letrec (defs', body')

            | LetType (typs, body) ->
                let body' = f body in
                if body' == body then v else LetType (typs, body')

            | Axiom (axioms, body) ->
                let body' = f body in
                if body' == body then v else Axiom (axioms, body')

            | Cast (expr, co) ->
                let expr' = f expr in
                if expr' == expr then v else Cast (expr', co)

            | Pack (existentials, expr) ->
                let expr' = f expr in
                if expr' == expr then v else Pack (existentials, expr')

            | Unpack (existentials, def, expr, body) ->
                let expr' = f expr in
                let body' = f body in
                if expr' == expr && body' == body then v else Unpack (existentials, def, expr', body')

            | Record fields ->
                let fields' = Vector.map (fun (label, field) -> (label, f field)) fields in
                let noop = Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                        (Vector.to_source fields') (Vector.to_source fields))
                    |> Stream.into (Sink.all ~where: Fun.id) in
                if noop then v else Record fields'

            | With {base; label; field} ->
                let base' = f base in
                let field' = f field in
                if base' == base && field' == field then v else With {base = base'; label; field = field'}

            | Where (base, fields) ->
                let base' = f base in
                let fields' = Vector1.map (fun (label, field) -> (label, f field)) fields in
                if base' == base
                    && Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                        (Vector1.to_source fields') (Vector1.to_source fields))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then v
                else Where (base', fields')

            | Select (expr, label) ->
                let expr' = f expr in
                if expr' == expr then v else Select (expr', label)

            | Match (matchee, clauses) ->
                let matchee' = f matchee in
                let clauses' = Vector.map (fun {pat; body} -> {pat; body = f body}) clauses in
                if matchee' == matchee
                    && Stream.from (Source.zip_with (fun clause' clause -> clause'.body == clause.body)
                        (Vector.to_source clauses') (Vector.to_source clauses))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then v
                else Match (matchee', clauses')

            | Proxy _ | Use _ | Const _ -> v

            | Patchable rref ->
                let expr = !rref in
                let expr' = f expr in
                if expr' == expr then v else Patchable (ref expr') in
        if v' == v then expr else {expr with v = v'}
end

and Stmt : FcSigs.STMT
    with module Type = Type
    with type pat = Expr.pat
    with type expr = Expr.t
= struct
    module Type = Type

    type expr = Expr.t
    type pat = Expr.pat

    type def = Util.span * pat with_pos * expr with_pos

    type t
        = Def of def
        | Expr of Expr.t with_pos

    let def_to_doc s ((_, pat, expr) : def) =
        PPrint.infix 4 1 PPrint.equals (Expr.pat_to_doc s pat) (Expr.to_doc s expr)

    let to_doc s = function
        | Def def -> def_to_doc s def
        | Expr expr -> Expr.to_doc s expr
end

end

