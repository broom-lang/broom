open Streaming

module Make (Type : FcSigs.TYPE) : FcSigs.TERM
    with module Type = Type
= struct 

module Type = Type

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module rec Expr : sig
    include FcSigs.EXPR
        with module Type = Type
        with type def = Stmt.def

    val def_to_doc : Type.subst -> var -> PPrint.document
end = struct
    module Type = Type

    type def = Stmt.def

    and var =
        { id : int; name : Name.t; vtyp : Type.t
        ; mutable value : t option; uses : use CCVector.vector }

    and use = {mutable expr : t option; mutable var : var}

    and t =
        { term : t'
        ; mutable parent : t option
        ; typ : Type.t
        ; pos : Util.span }

    and t' =
        | Values of t array
        | Focus of {mutable focusee : t; index : int}

        | Fn of {universals : Type.binding Vector.t; param : var; mutable body : t}
        | App of {mutable callee : t; universals : Type.t Vector.t; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; mutable arg : t}

        | Let of {def : def; mutable body : t}
        | Letrec of {defs : def Array1.t; mutable body : t}
        | LetType of {typedefs : Type.binding Vector1.t; mutable body : t}
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        | Axiom of { axioms : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t
            ; mutable body : t }
        | Cast of {mutable castee : t; coercion : Type.coercion}

        | Pack of {existentials : Type.t Vector1.t; mutable impl : t}
        | Unpack of { existentials : Type.binding Vector1.t; var : var; mutable value : t
            ; mutable body : t }

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}

        | Proxy of Type.t
        | Const of Const.t

        | Use of use

        | Patchable of t TxRef.rref

    and clause = {pat : pat; mutable body : t}

    and pat = {pterm : pat'; ptyp : Type.t; ppos : Util.span}
    and pat' =
        | ValuesP of pat Vector.t
        | ProxyP of Type.t
        | ConstP of Const.t
        | VarP of var
        | WildP

    let var_to_doc (var : var) =
        Name.to_doc var.name ^^ PPrint.sharp ^^ PPrint.string (Int.to_string var.id)

    let def_to_doc s (var : var) =
        PPrint.infix 4 1 PPrint.colon (var_to_doc var) (Type.to_doc s var.vtyp)

    let use_to_doc (use : use) = var_to_doc use.var

    let rec to_doc s (expr : t) = match expr.term with
        | Values exprs ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (to_doc s) (Array.to_list exprs)
        | Focus {focusee; index} ->
            selectee_to_doc s focusee ^^ PPrint.dot ^^ PPrint.string (Int.to_string index)
        | Fn {universals; param; body} ->
            PPrint.prefix 4 1
                (PPrint.string "fun"
                     ^^ (PPrint.surround_separate_map 4 0 PPrint.empty
                             (PPrint.blank 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                             (Type.binding_to_doc s) (Vector.to_list universals)
                         ^^ PPrint.blank 1 ^^ def_to_doc s param)
                     ^^ PPrint.blank 1 ^^ PPrint.string "->")
                (to_doc s body)
        | Let {def; body} ->
            PPrint.surround 4 1 (PPrint.string "let") (Stmt.def_to_doc s def) (PPrint.string "in")
                ^/^ to_doc s body
        | Letrec {defs; body} ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "letrec")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                        (Stmt.def_to_doc s) (Array1.to_list defs)))
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | LetType {typedefs; body} ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "let type")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1)
                                        (Type.binding_to_doc s) (Vector1.to_list typedefs)))
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | Match {matchee; clauses} ->
            let start = PPrint.string "match" ^^ PPrint.blank 1 ^^ to_doc s matchee in
            PPrint.surround_separate_map 4 1 (start ^/^ PPrint.string "end")
                start (PPrint.break 1) (PPrint.string "end")
                (clause_to_doc s) (Vector.to_list clauses)
        | App {callee; universals; arg} ->
            PPrint.align (to_doc s callee
                          ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                                (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                                (Type.to_doc s) (Vector.to_list universals)
                          ^/^ to_doc s arg)
        | PrimApp {op; universals; arg} ->
            PPrint.align (PPrint.string "__" ^^ Primop.to_doc op
                          ^^ PPrint.surround_separate_map 4 0 PPrint.empty
                                (PPrint.break 1 ^^ PPrint.langle) (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                                (Type.to_doc s) (Vector.to_list universals)
                          ^/^ to_doc s arg)
        | Axiom {axioms; body} ->
            PPrint.group(
                PPrint.surround 4 1 (PPrint.string "axiom")
                    (PPrint.align (PPrint.separate_map (PPrint.semi ^^ PPrint.break 1) (axiom_to_doc s)
                        (Vector1.to_list axioms)))
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | Cast {castee; coercion} ->
            PPrint.infix 4 1 (PPrint.string "|>") (castee_to_doc s castee) (Type.coercion_to_doc s coercion)
        | Pack {existentials; impl} ->
            PPrint.string "pack" ^^ PPrint.blank 1
                ^^ PPrint.surround_separate 4 0 PPrint.empty
                    PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                    (Vector1.to_list (Vector1.map (Type.to_doc s) existentials) @ [to_doc s impl])
        | Unpack {existentials; var; value; body} ->
            PPrint.group(
                PPrint.surround 4 1
                    (PPrint.string "unpack" ^^ PPrint.blank 1
                        ^^ PPrint.surround_separate 4 0 PPrint.empty
                            PPrint.langle (PPrint.comma ^^ PPrint.break 1) PPrint.rangle
                            (Vector1.to_list (Vector1.map (Type.binding_to_doc s) existentials)
                                @ [def_to_doc s var])
                        ^^ PPrint.blank 1 ^^ PPrint.equals)
                    (to_doc s value)
                    (PPrint.string "in")
                ^/^ to_doc s body)
        | Record fields ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                (fun (label, field) -> PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc s field))
                (Array.to_list fields)
        | Where {base; fields} ->
            PPrint.infix 4 1 (PPrint.string "where")
                (to_doc s base)
                (PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                    PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                    (fun (label, field) ->
                        PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc s field))
                    (Array1.to_list fields))
        | With {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (base_to_doc s base)
                (PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc s field))
        | Select {selectee; label} ->
            PPrint.prefix 4 0 (selectee_to_doc s selectee) (PPrint.dot ^^ Name.to_doc label)
        | Proxy typ -> PPrint.brackets (Type.to_doc s typ)
        | Use use -> use_to_doc use
        | Const c -> Const.to_doc c
        | Patchable r -> TxRef.(to_doc s !r)

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

    and castee_to_doc s (castee : t) = match castee.term with
        | Fn _ -> PPrint.parens (to_doc s castee)
        | _ -> to_doc s castee

    and base_to_doc s (base : t) = match base.term with
        | Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ -> PPrint.parens (to_doc s base)
        | _ -> to_doc s base

    and selectee_to_doc s (selectee : t) = match selectee.term with
        | Fn _ | Cast _ | Letrec _ | LetType _ | Axiom _ | App _ | Where _ | With _ ->
            PPrint.parens (to_doc s selectee)
        | _ -> to_doc s selectee

    and pat_to_doc s (pat : pat) = match pat.pterm with
        | ValuesP pats ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (pat_to_doc s) (Vector.to_list pats)
        | ProxyP typ -> PPrint.brackets (Type.to_doc s typ)
        | VarP var -> PPrint.parens (def_to_doc s var)
        | WildP -> PPrint.underscore
        | ConstP c -> Const.to_doc c

    let id_counter = ref 0

    let var name vtyp value =
        let id = !id_counter in
        id_counter := id + 1;
        {id; name; vtyp; value; uses = CCVector.create ()}

    let fresh_var vtyp value = var (Name.fresh ()) vtyp value

    let at pos typ term = {term; pos; typ; parent = None}

    let values vals = Values vals

    let focus focusee index = Focus {focusee; index}
    let fn universals param body = Fn {universals; param; body}
    let app callee universals arg = App {callee; universals; arg}
    let primapp op universals arg = PrimApp {op; universals; arg}
    let let' def body = Let {def; body}

    let letrec defs body = match Array1.of_array defs with
        | Some defs -> Letrec {defs; body}
        | None -> body.term

    let match' matchee clauses = Match {matchee; clauses}

    let axiom axioms body = match Vector1.of_vector axioms with
        | Some axioms -> Axiom {axioms; body}
        | None -> body.term

    let cast castee = function
        | Type.Refl _ -> castee.term
        | coercion -> Cast {castee; coercion}

    let pack existentials impl = match Vector1.of_vector existentials with
        | Some existentials -> Pack {existentials; impl}
        | None -> impl.term

    let unpack existentials var value body = Unpack {existentials; var; value; body}
    let record fields = Record fields

    let where base fields = match Array1.of_array fields with
        | Some fields -> Where {base; fields}
        | None -> base.term

    let select selectee label = Select {selectee; label}
    let proxy t = Proxy t
    let const c = Const c
    let use var = Use {var; expr = None}
    let patchable ref = Patchable ref

    let map_children f (expr : t) =
        let term = expr.term in
        let term' = match term with
            | Values lets ->
                let lets' = Array.map f lets in
                let noop = Stream.from (Source.zip_with (==)
                        (Source.array lets') (Source.array lets))
                    |> Stream.into (Sink.all ~where: Fun.id) in
                if noop then term else Values lets'

            | Focus {focusee; index} ->
                let focusee' = f focusee in
                if focusee' == focusee then term else Focus {focusee = focusee'; index}

            | Fn {universals; param; body} ->
                let body' = f body in
                if body' == body then term else Fn {universals; param; body = body'}

            | App {callee; universals; arg} ->
                let callee' = f callee in
                let arg' = f arg in
                if callee' == callee && arg' == arg
                then term
                else App {callee = callee'; universals; arg = arg'}

            | PrimApp {op; universals; arg} ->
                let arg' = f arg in
                if arg' == arg then term else PrimApp {op; universals; arg = arg'}

            | Let {def = (pos, def, expr); body} ->
                let expr' = f expr in
                let body' = f body in
                if expr' == expr && body' == body
                then term
                else Let {def = (pos, def, expr'); body = body'}

            | Letrec {defs; body} ->
                let defs' = Array1.map (fun (pos, def, expr) -> (pos, def, f expr)) defs in
                let body' = f body in
                if body' == body
                    && Stream.from (Source.zip_with (fun (_, _, expr') (_, _, expr) -> expr' == expr)
                        (Array1.to_source defs') (Array1.to_source defs))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else Letrec {defs = defs'; body = body'}

            | LetType {typedefs; body} ->
                let body' = f body in
                if body' == body then term else LetType {typedefs; body = body'}

            | Axiom {axioms; body} ->
                let body' = f body in
                if body' == body then term else Axiom {axioms; body = body'}

            | Cast {castee; coercion} ->
                let castee' = f castee in
                if castee' == castee then term else Cast {castee = castee'; coercion}

            | Pack {existentials; impl} ->
                let impl' = f impl in
                if impl' == impl then term else Pack {existentials; impl = impl'}

            | Unpack {existentials; var; value; body} ->
                let value' = f value in
                let body' = f body in
                if value' == value && body' == body
                then term
                else Unpack {existentials; var; value = value'; body = body'}

            | Record fields ->
                let fields' = Array.map (fun (label, field) -> (label, f field)) fields in
                let noop = Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                        (Source.array fields') (Source.array fields))
                    |> Stream.into (Sink.all ~where: Fun.id) in
                if noop then term else Record fields'

            | With {base; label; field} ->
                let base' = f base in
                let field' = f field in
                if base' == base && field' == field then term else With {base = base'; label; field = field'}

            | Where {base; fields} ->
                let base' = f base in
                let fields' = Array1.map (fun (label, field) -> (label, f field)) fields in
                if base' == base
                    && Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                        (Array1.to_source fields') (Array1.to_source fields))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else Where {base = base'; fields = fields'}

            | Select {selectee; label} ->
                let selectee' = f selectee in
                if selectee' == selectee then term else Select {selectee = selectee'; label}

            | Match {matchee; clauses} ->
                let matchee' = f matchee in
                let clauses' = Vector.map (fun {pat; body} -> {pat; body = f body}) clauses in
                if matchee' == matchee
                    && Stream.from (Source.zip_with (fun clause' clause -> clause'.body == clause.body)
                        (Vector.to_source clauses') (Vector.to_source clauses))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else Match {matchee = matchee'; clauses = clauses'}

            | Proxy _ | Use _ | Const _ -> term

            | Patchable rref ->
                let open TxRef in
                let expr = !rref in
                let expr' = f expr in
                if expr' == expr then term else Patchable (ref expr') in
        if term' == term then expr else {expr with term = term'}

    module Var = struct
        type t = var

        let compare (var : var) (var' : var) = Int.compare var.id var'.id
    end

    module VarSet = Set.Make(Var)
end

and Stmt : FcSigs.STMT
    with module Type = Type
    with type expr = Expr.t
    with type var = Expr.var
= struct
    module Type = Type

    type expr = Expr.t
    type var = Expr.var

    type def = Util.span * var * expr

    type t
        = Def of def
        | Expr of expr

    let def_to_doc s ((_, var, expr) : def) =
        PPrint.infix 4 1 PPrint.equals (Expr.def_to_doc s var) (Expr.to_doc s expr)

    let to_doc s = function
        | Def def -> def_to_doc s def
        | Expr expr -> Expr.to_doc s expr

    let rhs (Def (_, _, expr) | Expr expr) = expr
end

end

