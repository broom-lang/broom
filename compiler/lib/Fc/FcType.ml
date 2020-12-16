module rec Uv : FcTypeSigs.UV
    with type kind = Typ.kind
    with type typ = Typ.t
    with type level = Typ.level
= struct
    type kind = Typ.kind
    type typ = Typ.t
    type level = Typ.level

    include UnionFind.Make(TxRef.Store)

    type v =
        | Unassigned of int * kind * Typ.level
        | Assigned of typ

    type subst = v store

    type t = v rref

    let new_subst = new_store

    let make sr kind level =
        make sr (Unassigned (TxRef.fresh_id sr, kind, level)) |> snd

    let get sr uv = get sr uv |> snd

    let set sr uv v = ignore (set sr uv v)
end

and Typ : FcTypeSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst
= struct
    module PP = PPrint

    type uv = Uv.t
    type subst = Uv.subst

    let (!) = TxRef.(!)

    type level = int

    type bv = {depth : int; sibli : int; kind : kind}

    and binding = Name.t * kind

    and ov = binding * level

    and t =
        | Exists of kind Vector1.t * t
        | PromotedArray of t Vector.t
        | PromotedTuple of t Vector.t
        | Tuple of t Vector.t
        | Pi of {universals : kind Vector.t; domain : (t, edomain) Ior.t; codomain : t}
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of t
        | Fn of kind * t
        | App of t * t
        | Bv of bv
        | Ov of ov
        | Uv of uv
        | Prim of Prim.t

    and edomain = {edomain : t; eff : t}

    and template =
        | TupleL of int
        | PiL of template
        | WithL of {base : template; label : Name.t; field : template}
        | ProxyL of t
        | Hole

    and 'a field = {label : string; typ : 'a}

    and coercion =
        | Refl of typ
        | Symm of coercion
        | Trans of coercion * coercion
        | Comp of coercion * coercion Vector1.t
        | Inst of coercion * typ Vector1.t
        | AUse of Name.t
        | PromotedArrayCo of coercion Vector.t
        | PromotedTupleCo of coercion Vector.t
        | TupleCo of coercion Vector.t
        | RecordCo of coercion
        | WithCo of {base : coercion; label : Name.t; field : coercion}
        | ProxyCo of coercion
        | Patchable of coercion TxRef.rref

    and typ = t

    and kind = t

    (* --- *)

    let rec kind_to_doc s kind = to_doc s kind

    and kinds_to_doc s kinds = PPrint.(separate_map (break 1) (kind_to_doc s) kinds)

    and to_doc s typ =
        let open PPrint in
        match typ with
        | Exists (params, body) ->
            prefix 4 1 (group (string "exists" ^/^ (kinds_to_doc s) (Vector1.to_list params)))
                (dot ^^ blank 1 ^^ to_doc s body)
        | PromotedArray typs ->
            surround_separate_map 4 0 (brackets empty)
                lbracket (comma ^^ break 1) rbracket
                (to_doc s) (Vector.to_list typs)
        | PromotedTuple typs ->
            surround_separate_map 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                (to_doc s) (Vector.to_list typs)
        | Tuple typs ->
            surround_separate_map 4 0 (parens colon)
                (lparen ^^ colon) (comma ^^ break 1) rparen
                (to_doc s) (Vector.to_list typs)
        | Pi {universals; domain; codomain} ->
            let codoc = to_doc s codomain in
            let (idoc, edoc, effdoc) = match domain with
                | Left idomain -> (Some (to_doc s idomain), None, None)
                | Right {edomain; eff} -> (None, Some (to_doc s edomain), Some (to_doc s eff))
                | Both (idomain, {edomain; eff}) ->
                    (Some (to_doc s idomain), Some (to_doc s edomain), Some (to_doc s eff)) in
            let doc = match edoc with
                | Some edoc ->
                    let doc = string "->" ^^ blank 1 ^^ codoc in
                    let doc = match effdoc with
                        | Some effdoc ->
                            prefix 4 1 (string "-!" ^^ blank 1 ^^ effdoc) doc
                        | None -> doc in
                    prefix 4 1 edoc doc
                | None -> codoc in
            let doc = match idoc with
                | Some idoc -> prefix 4 1 idoc (string "=>" ^^ blank 1 ^^ doc)
                | None -> doc in
            if Vector.length universals > 0
            then prefix 4 1
                (string "forall" ^^ blank 1 ^^ kinds_to_doc s (Vector.to_list universals))
                (dot ^^ blank 1 ^^ doc)
            else doc
        | Record row -> braces (to_doc s row)
        | With {base; label; field} ->
            infix 4 1 (string "with") (base_to_doc s base)
                (infix 4 1 colon (Name.to_doc label) (to_doc s field))
        | EmptyRow -> parens (bar)
        | Proxy typ -> brackets (equals ^^ blank 1 ^^ to_doc s typ)
        | Fn (param, body) ->
            prefix 4 1
                (string "fun" ^^ blank 1 ^^ kind_to_doc s param)
                (dot ^^ blank 1 ^^ to_doc s body)
        | App (callee, arg) -> callee_to_doc s callee ^/^ arg_to_doc s arg
        | Bv {depth; sibli; kind = _} ->
            caret ^^ string (Int.to_string depth) ^^ slash
                ^^ string (Int.to_string sibli)
        | Ov ((name, _), _) -> Name.to_doc name
        | Uv uv -> uv_to_doc s uv
        | Prim pt -> string "__" ^^ Prim.to_doc pt

    and base_to_doc s = function
        | (Pi _ | Fn _) as base -> PP.parens (to_doc s base)
        | Uv uv ->
            (match Uv.get s uv with
            | Assigned typ -> base_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)
        | base -> to_doc s base

    and callee_to_doc s = function
        | (Pi _ | Fn _) as callee -> PP.parens (to_doc s callee)
        | Uv uv ->
            (match Uv.get s uv with
            | Assigned typ -> callee_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)
        | callee -> to_doc s callee

    and arg_to_doc s = function
        | (Pi _ | Fn _ (*| App _*)) as arg -> PP.parens (to_doc s arg)
        | Uv uv ->
            (match Uv.get s uv with
            | Assigned typ -> arg_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)
        | arg -> to_doc s arg

    and template_to_doc s tpl =
        let open PPrint in
        match tpl with
        | TupleL length ->
            surround_separate 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                (List.init length (fun _ -> underscore))
        | PiL codomain ->
            let domain_doc = parens empty in
            infix 4 1 (string "->") domain_doc (template_to_doc s codomain)
        | WithL {base; label; field} ->
            infix 4 1 (string "with") (basel_to_doc s base)
                (infix 4 1 colon (Name.to_doc label) (template_to_doc s field))
        | ProxyL path -> brackets (equals ^^ blank 1 ^^ to_doc s path)
        | Hole -> underscore

    and basel_to_doc s = function
        | PiL _ as template -> PP.parens (template_to_doc s template)
        | template -> template_to_doc s template

    and binding_to_doc s (name, kind) =
        PPrint.(Name.to_doc name ^/^ colon ^/^ kind_to_doc s kind)

    and universal_to_doc s universals body =
        PPrint.(prefix 4 1 (group (string "forall" ^/^ (kinds_to_doc s) (Vector.to_list universals)))
            (dot ^^ blank 1 ^^ body))

    and uv_to_doc s uv = match Uv.get s uv with
        | Unassigned (id, _, _) -> PPrint.(qmark ^^ string (Int.to_string id))
        | Assigned t -> to_doc s t

    let rec coercion_to_doc s co =
        let open PPrint in
        match co with
        | Refl typ -> to_doc s typ
        | Symm co -> string "symm" ^^ blank 1 ^^ coercion_to_doc s co
        | Trans (co, co') ->
            infix 4 1 (bquotes (string "o"))
                (coercion_to_doc s co) (andco_to_doc s co')
        | Comp (ctor_co, arg_cos) ->
            prefix 4 1 (ctorco_to_doc s ctor_co)
                (separate_map (break 1) (argco_to_doc s) (Vector1.to_list arg_cos))
        | Inst (co, args) ->
            Vector1.fold (fun doc arg -> infix 4 1 at doc (to_doc s arg))
                (instantiee_to_doc s co) args
        | AUse name -> Name.to_doc name
        | PromotedArrayCo coercions ->
            surround_separate_map 4 0 (brackets empty)
                lbracket (comma ^^ break 1) rbracket
                (coercion_to_doc s) (Vector.to_list coercions)
        | PromotedTupleCo coercions ->
            surround_separate_map 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                (coercion_to_doc s) (Vector.to_list coercions)
        | TupleCo coercions ->
            colon
                ^/^ separate_map (comma ^^ break 1) (coercion_to_doc s)
                    (Vector.to_list coercions)
            |> parens
        | RecordCo row_co -> braces (coercion_to_doc s row_co)
        | WithCo {base; label; field} ->
            infix 4 1 (string "with") (base_co_to_doc s base)
                (infix 4 1 colon (Name.to_doc label) (coercion_to_doc s field))
        | ProxyCo co -> brackets (equals ^^ break 1 ^^ coercion_to_doc s co)
        | Patchable ref -> coercion_to_doc s !ref

    and andco_to_doc s = function
        | Trans _ as co -> PP.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and ctorco_to_doc s = function
        | (Symm _ | Trans _ | Inst _) as co -> PP.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and argco_to_doc s = function
        | (Trans _ | Inst _ | Comp _) as co -> PP.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and instantiee_to_doc s = function
        | (Symm _ | Trans _) as co -> PP.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and base_co_to_doc s = function
        | (Trans _ | Comp _ | Inst _) as co -> PP.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co
end

(* HACK: OCaml these constants are 'unsafe' for OCaml recursive modules,
 * so we have to add them here: *)
module Type = struct
    include Typ

    (* __typeIn [__boxed] *)
    let aType = App (Prim TypeIn, PromotedArray (Vector.singleton (Prim Boxed)))
    let aKind = aType

    (* __rowOf (__typeIn [__boxed]) *)
    let aRow = App (Prim RowOf, aType)

    (* __array __singleRep *)
    let rep = App (Prim Array, Prim SingleRep)
end

