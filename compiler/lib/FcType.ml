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
        | Unassigned of Name.t * kind * Typ.level
        | Assigned of typ

    type subst = v store

    type t = v rref

    let new_subst = new_store

    let make sr v = make sr v |> snd

    let get sr uv = get sr uv |> snd

    let set sr uv v = ignore (set sr uv v)
end

and Typ : FcTypeSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst
= struct
    type uv = Uv.t
    type subst = Uv.subst

    let (!) = TxRef.(!)

    type level = int

    type bv = {depth : int; sibli : int; kind : kind}

    and binding = Name.t * kind

    and ov = binding * level

    and abs = Exists of kind Vector.t * t

    and t =
        | PromotedArray of t Vector.t
        | PromotedValues of t Vector.t
        | Values of t Vector.t
        (* TODO: Remove multiargs since they can be implemented with unboxed tuples (`Values`): *)
        | Pi of {universals : kind Vector.t; idomain : t option; edomain : t; eff : t; codomain : abs}
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of abs
        | Fn of kind * t
        | App of t * t
        | Bv of bv
        | Ov of ov
        | Uv of uv
        | Prim of Prim.t

    and template =
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
        | PromotedValuesCo of coercion Vector.t
        | ValuesCo of coercion Vector.t
        | RecordCo of coercion
        | WithCo of {base : coercion; label : Name.t; field : coercion}
        | ProxyCo of coercion
        | Patchable of coercion TxRef.rref

    and typ = t

    and kind = t

    let (^^) = PPrint.(^^)
    let (^/^) = PPrint.(^/^)

    (* --- *)

    let rec kind_to_doc s kind = to_doc s kind

    and kinds_to_doc s kinds = PPrint.separate_map (PPrint.break 1) (kind_to_doc s) kinds

    and abs_to_doc s (Exists (params, body)) =
        if Vector.length params > 0 then
            PPrint.prefix 4 1 (PPrint.group (PPrint.string "exists" ^/^ (kinds_to_doc s) (Vector.to_list params)))
                (PPrint.dot ^^ PPrint.blank 1 ^^ to_doc s body)
        else to_doc s body

    and to_doc s = function
        | PromotedArray typs ->
            PPrint.surround_separate_map 4 0 (PPrint.brackets PPrint.empty)
                PPrint.lbracket (PPrint.comma ^^ PPrint.break 1) PPrint.rbracket
                (to_doc s) (Vector.to_list typs)
        | PromotedValues typs ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (to_doc s) (Vector.to_list typs)
        | Values typs ->
            PPrint.colon
                ^/^ PPrint.separate_map (PPrint.comma ^^ PPrint.break 1) (to_doc s)
                    (Vector.to_list typs)
            |> PPrint.parens
        | Pi {universals; idomain; edomain; eff; codomain} ->
            let idomain = Option.map (to_doc s) idomain in
            let edomain = to_doc s edomain in
            let edoc =
                PPrint.prefix 4 1 edomain
                    (PPrint.string "-!" ^^ PPrint.blank 1
                        ^^ PPrint.infix 4 1 (PPrint.string "->") (to_doc s eff) (abs_to_doc s codomain)) in
            let unquantified_doc = match idomain with
                | Some idomain ->
                    PPrint.prefix 4 1 idomain (PPrint.string "=>" ^^ PPrint.blank 1 ^^ edoc)
                | None -> edoc in
            if Vector.length universals > 0
            then PPrint.prefix 4 1
                (PPrint.group (PPrint.string "forall" ^/^ (kinds_to_doc s) (Vector.to_list universals)))
                (PPrint.dot ^^ PPrint.blank 1 ^^ unquantified_doc)
            else unquantified_doc
        | Record row -> PPrint.braces (to_doc s row)
        | With {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (base_to_doc s base)
                (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (to_doc s field))
        | EmptyRow -> PPrint.parens (PPrint.bar)
        | Proxy typ -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ abs_to_doc s typ)
        | Fn (param, body) ->
            PPrint.prefix 4 1
                (PPrint.string "fun" ^^ PPrint.blank 1 ^^ kind_to_doc s param)
                (PPrint.dot ^^ PPrint.blank 1 ^^ to_doc s body)
        | App (callee, arg) -> callee_to_doc s callee ^/^ arg_to_doc s arg
        | Bv {depth; sibli; kind = _} ->
            PPrint.caret ^^ PPrint.string (Int.to_string depth) ^^ PPrint.slash
                ^^ PPrint.string (Int.to_string sibli)
        | Ov ((name, _), _) -> Name.to_doc name
        | Uv uv -> uv_to_doc s uv
        | Prim pt -> PPrint.string "__" ^^ Prim.to_doc pt

    and base_to_doc s = function
        | (Pi _ | Fn _) as base -> PPrint.parens (to_doc s base)
        | Uv uv ->
            (match Uv.get s uv with
            | Assigned typ -> base_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)
        | base -> to_doc s base

    and callee_to_doc s = function
        | (Pi _ | Fn _) as callee -> PPrint.parens (to_doc s callee)
        | Uv uv ->
            (match Uv.get s uv with
            | Assigned typ -> callee_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)
        | callee -> to_doc s callee

    and arg_to_doc s = function
        | (Pi _ | Fn _ (*| App _*)) as arg -> PPrint.parens (to_doc s arg)
        | Uv uv ->
            (match Uv.get s uv with
            | Assigned typ -> arg_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)
        | arg -> to_doc s arg

    and field_to_doc s {label; typ} =
        PPrint.string label ^/^ PPrint.colon ^/^ to_doc s typ

    and template_to_doc s = function
        | PiL codomain ->
            let domain_doc = PPrint.parens PPrint.empty in
            PPrint.infix 4 1 (PPrint.string "->") domain_doc (template_to_doc s codomain)
        | WithL {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (basel_to_doc s base)
                (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (template_to_doc s field))
        | ProxyL path -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ to_doc s path)
        | Hole -> PPrint.underscore

    and basel_to_doc s = function
        | PiL _ as template -> PPrint.parens (template_to_doc s template)
        | template -> template_to_doc s template

    and binding_to_doc s (name, kind) =
        Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc s kind

    and universal_to_doc s universals body =
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ (kinds_to_doc s) (Vector.to_list universals)))
            (PPrint.dot ^^ PPrint.blank 1 ^^ body)

    and uv_to_doc s uv = match Uv.get s uv with
        | Unassigned (name, _, _) -> PPrint.qmark ^^ Name.to_doc name
        | Assigned t -> to_doc s t

    let rec coercion_to_doc s = function
        | Refl typ -> to_doc s typ
        | Symm co -> PPrint.string "symm" ^^ PPrint.blank 1 ^^ coercion_to_doc s co
        | Trans (co, co') ->
            PPrint.infix 4 1 (PPrint.bquotes (PPrint.string "o"))
                (coercion_to_doc s co) (andco_to_doc s co')
        | Comp (ctor_co, arg_cos) ->
            PPrint.prefix 4 1 (ctorco_to_doc s ctor_co)
                (PPrint.separate_map (PPrint.break 1) (argco_to_doc s) (Vector1.to_list arg_cos))
        | Inst (co, args) ->
            Vector1.fold (fun doc arg -> PPrint.infix 4 1 PPrint.at doc (to_doc s arg))
                (instantiee_to_doc s co) args
        | AUse name -> Name.to_doc name
        | PromotedArrayCo coercions ->
            PPrint.surround_separate_map 4 0 (PPrint.brackets PPrint.empty)
                PPrint.lbracket (PPrint.comma ^^ PPrint.break 1) PPrint.rbracket
                (coercion_to_doc s) (Vector.to_list coercions)
        | PromotedValuesCo coercions ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (coercion_to_doc s) (Vector.to_list coercions)
        | ValuesCo coercions ->
            PPrint.colon
                ^/^ PPrint.separate_map (PPrint.comma ^^ PPrint.break 1) (coercion_to_doc s)
                    (Vector.to_list coercions)
            |> PPrint.parens
        | RecordCo row_co -> PPrint.braces (coercion_to_doc s row_co)
        | WithCo {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (base_co_to_doc s base)
                (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (coercion_to_doc s field))
        | ProxyCo co -> PPrint.brackets (PPrint.equals ^^ PPrint.break 1 ^^ coercion_to_doc s co)
        | Patchable ref -> coercion_to_doc s !ref

    and andco_to_doc s = function
        | Trans _ as co -> PPrint.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and ctorco_to_doc s = function
        | (Symm _ | Trans _ | Inst _) as co -> PPrint.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and argco_to_doc s = function
        | (Trans _ | Inst _ | Comp _) as co -> PPrint.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and instantiee_to_doc s = function
        | (Symm _ | Trans _) as co -> PPrint.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    and base_co_to_doc s = function
        | (Trans _ | Comp _ | Inst _) as co -> PPrint.parens (coercion_to_doc s co)
        | co -> coercion_to_doc s co

    (* --- *)

    let to_abs typ = Exists (Vector.of_list [], typ)

    let freshen (name, kind) = (Name.freshen name, kind)

    let sibling sr kind uv = match Uv.get sr uv with
        | Unassigned (_, _, level) -> Uv.make sr (Unassigned (Name.fresh (), kind, level))
        | Assigned _ -> failwith "unreachable"
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

