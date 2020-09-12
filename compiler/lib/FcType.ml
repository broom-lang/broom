module rec Uv : FcTypeSigs.UV
    with type typ = Type.t
    with type level = Type.level
= struct
    type typ = Type.t
    type level = Type.level

    include UnionFind.Make(TxRef.Store)

    type v =
        | Unassigned of Name.t * Type.level
        | Assigned of typ

    type subst = v store

    type t = v rref

    let new_subst = new_store

    let make sr v = make sr v |> snd

    let get sr uv = get sr uv |> snd

    let set sr uv v = ignore (set sr uv v)
end

and Type : FcTypeSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst
= struct
    type uv = Uv.t
    type subst = Uv.subst

    let (!) = TxRef.(!)

    type kind =
        | ArrowK of kind Vector1.t * kind
        | TypeK

    type bv = {depth : int; sibli : int}

    type level = int

    type binding = Name.t * kind

    type ov = binding * level

    and abs = Exists of kind Vector.t * t

    and t =
        | Values of t Vector.t
        (* TODO: Remove multiargs since they can be implemented with unboxed tuples (`Values`): *)
        | Pi of kind Vector.t * t Vector.t * t * abs (* FIXME: Separate implicit domain *)
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of abs
        | Fn of t
        | App of t * t Vector1.t
        | Bv of bv
        | Use of binding
        | Ov of ov
        | Uv of uv
        | Prim of Prim.t

    and template =
        | PiL of int * template
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
        | ValuesCo of coercion Vector.t
        | RecordCo of coercion
        | WithCo of {base : coercion; label : Name.t; field : coercion}
        | ProxyCo of coercion
        | Patchable of coercion TxRef.rref

    and typ = t

    let (^^) = PPrint.(^^)
    let (^/^) = PPrint.(^/^)

    (* --- *)

    let rec kind_to_doc = function
        | ArrowK (domain, codomain) ->
            PPrint.prefix 4 1 (PPrint.separate_map PPrint.space domain_kind_to_doc (Vector1.to_list domain))
                (PPrint.string "->" ^^ PPrint.blank 1 ^^ kind_to_doc codomain)
        | TypeK -> PPrint.star

    and domain_kind_to_doc domain = match domain with
        | ArrowK _ -> PPrint.parens (kind_to_doc domain)
        | _ -> kind_to_doc domain

    let kinds_to_doc kinds = PPrint.separate_map (PPrint.break 1) kind_to_doc kinds

    let rec abs_to_doc s (Exists (params, body)) =
        if Vector.length params > 0 then
            PPrint.prefix 4 1 (PPrint.group (PPrint.string "exists" ^/^ kinds_to_doc (Vector.to_list params)))
                (PPrint.dot ^^ PPrint.blank 1 ^^ to_doc s body)
        else to_doc s body

    and to_doc s = function
        | Values typs ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (to_doc s) (Vector.to_list typs)
        | Pi (universals, domain, eff, codomain) ->
            let domain_doc =
                PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                    PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                    (to_doc s) (Vector.to_list domain) in
            let unquantified_doc =
                PPrint.prefix 4 1 domain_doc
                    (PPrint.string "-!" ^^ PPrint.blank 1
                        ^^ PPrint.infix 4 1 (PPrint.string "->") (to_doc s eff) (abs_to_doc s codomain)) in
            if Vector.length universals > 0
            then PPrint.prefix 4 1
                (PPrint.group (PPrint.string "forall" ^/^ kinds_to_doc (Vector.to_list universals)))
                (PPrint.dot ^^ PPrint.blank 1 ^^ unquantified_doc)
            else unquantified_doc
        | Record row -> PPrint.braces (to_doc s row)
        | With {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (base_to_doc s base)
                (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (to_doc s field))
        | EmptyRow -> PPrint.parens (PPrint.bar)
        | Proxy typ -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ abs_to_doc s typ)
        | Fn body ->
            PPrint.prefix 4 1
                (PPrint.string "fun" ^^ PPrint.blank 1 ^^ PPrint.dot)
                (to_doc s body)
        | App (callee, args) ->
            callee_to_doc s callee ^/^ PPrint.separate_map PPrint.space (arg_to_doc s)
                (Vector1.to_list args)
        | Bv {depth; sibli} ->
            PPrint.caret ^^ PPrint.string (Int.to_string depth) ^^ PPrint.slash
                ^^ PPrint.string (Int.to_string sibli)
        | Use (name, _) | Ov ((name, _), _) -> Name.to_doc name
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
        | PiL (arity, codomain) ->
            let domain_doc =
                let rec loop doc = function
                    | 0 -> doc
                    | arity -> loop (doc ^^ PPrint.comma ^/^ PPrint.underscore) (arity - 1) in
                PPrint.parens (loop PPrint.empty arity) in
            PPrint.infix 4 1 (PPrint.string "->") domain_doc (template_to_doc s codomain)
        | WithL {base; label; field} ->
            PPrint.infix 4 1 (PPrint.string "with") (basel_to_doc s base)
                (PPrint.infix 4 1 PPrint.colon (Name.to_doc label) (template_to_doc s field))
        | ProxyL path -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ to_doc s path)
        | Hole -> PPrint.underscore

    and basel_to_doc s = function
        | PiL _ as template -> PPrint.parens (template_to_doc s template)
        | template -> template_to_doc s template

    and binding_to_doc (name, kind) =
        Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind

    and universal_to_doc universals body =
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ kinds_to_doc (Vector.to_list universals)))
            (PPrint.dot ^^ PPrint.blank 1 ^^ body)

    and uv_to_doc s uv = match Uv.get s uv with
        | Unassigned (name, _) -> PPrint.qmark ^^ Name.to_doc name
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
        | ValuesCo coercions ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                (coercion_to_doc s) (Vector.to_list coercions)
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

    let sibling sr uv = match Uv.get sr uv with
        | Unassigned (_, level) -> Uv.make sr (Unassigned (Name.fresh (), level))
        | Assigned _ -> failwith "unreachable"
end

