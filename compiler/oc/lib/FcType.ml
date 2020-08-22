module rec Uv : FcSigs.UV
    with type typ = Type.t
    with type level = Type.level
= struct
    type typ = Type.t
    type level = Type.level

    include UnionFind.Make(UnionFind.StoreTransactionalRef)

    type v =
        | Unassigned of Name.t * Type.level
        | Assigned of typ

    type subst = v store

    type t = v rref

    let new_subst = new_store

    let getr sr uv =
        let (s, v) = get (!sr) uv in
        sr := s;
        v
end

and Type : FcSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst
= struct
    type uv = Uv.t
    type subst = Uv.subst

    type kind =
        | ArrowK of kind Vector1.t * kind
        | TypeK

    type bv = {depth : int; sibli : int}

    type level = int

    type binding = Name.t * kind

    type ov = binding * level

    and abs = Exists of kind Vector.t * locator * t

    and t =
        | Pi of kind Vector.t * (locator * t) Vector.t * t * abs
        | Record of t field Vector.t
        | Type of abs
        | Fn of t
        | App of t * t Vector1.t
        | Bv of bv
        | Use of binding
        | Ov of ov
        | Uv of Uv.t
        | Prim of Prim.t

    and locator =
        | PiL of locator
        | RecordL of locator field Vector.t
        | TypeL of t
        | Hole

    and 'a field = {label : string; typ : 'a}

    and coercion =
        | Refl of typ
        | Symm of coercion
        | Trans of coercion * coercion
        | Comp of coercion * coercion Vector1.t
        | Inst of coercion * typ Vector1.t
        | AUse of Name.t
        | TypeCo of coercion
        | Patchable of coercion ref

    and typ = t
    and template = locator

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

    let rec abs_to_doc s (Exists (params, locator, body)) =
        if Vector.length params > 0 then
            PPrint.prefix 4 1 (PPrint.group (PPrint.string "exists" ^/^ kinds_to_doc (Vector.to_list params)))
                (PPrint.dot ^^ PPrint.blank 1
                    ^^ PPrint.parens (locator_to_doc s locator ^^ PPrint.comma ^/^ to_doc s body))
        else to_doc s body

    and to_doc s = function
        | Pi (universals, domain, eff, codomain) ->
            let domain_doc =
                PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                    PPrint.lparen (PPrint.semi ^^ PPrint.break 1) PPrint.rparen
                    (domain_to_doc s) (Vector.to_list domain) in
            let unquantified_doc =
                PPrint.prefix 4 1 domain_doc
                    (PPrint.string "->" ^^ PPrint.blank 1
                        ^^ PPrint.infix 4 1 PPrint.bang (to_doc s eff) (abs_to_doc s codomain)) in
            if Vector.length universals > 0
            then PPrint.prefix 4 1
                (PPrint.group (PPrint.string "forall" ^/^ kinds_to_doc (Vector.to_list universals)))
                (PPrint.dot ^^ PPrint.blank 1 ^^ unquantified_doc)
            else unquantified_doc
        | Record fields ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                (field_to_doc s) (Vector.to_list fields)
        | Type typ -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ abs_to_doc s typ)
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

    and domain_to_doc s (locator, domain) = locator_to_doc s locator ^^ PPrint.comma ^/^ to_doc s domain

    and callee_to_doc s = function
        | (Pi _ | Fn _) as callee -> PPrint.parens (to_doc s callee)
        (* FIXME: | Uv uv ->
            (match !uv with
            | Assigned typ -> callee_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)*)
        | callee -> to_doc s callee

    and arg_to_doc s = function
        | (Pi _ | Fn _ (*| App _*)) as arg -> PPrint.parens (to_doc s arg)
        (* FIXME: | Uv uv ->
            (match !uv with
            | Assigned typ -> arg_to_doc s typ
            | Unassigned _ -> uv_to_doc s uv)*)
        | arg -> to_doc s arg

    and field_to_doc s {label; typ} =
        PPrint.string label ^/^ PPrint.colon ^/^ to_doc s typ

    and locator_to_doc s = function
        | PiL codomain ->
            PPrint.infix 4 1 (PPrint.string "->") PPrint.underscore (locator_to_doc s codomain)
        | RecordL fields ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                (fun {label; typ} -> PPrint.string label ^/^ PPrint.colon ^/^ locator_to_doc s typ)
                (Vector.to_list fields)
        | TypeL path -> PPrint.brackets (PPrint.equals ^^ PPrint.blank 1 ^^ to_doc s path)
        | Hole -> PPrint.underscore

    and binding_to_doc (name, kind) =
        PPrint.parens (Name.to_doc name ^/^ PPrint.colon ^/^ kind_to_doc kind)

    and universal_to_doc universals body =
        PPrint.prefix 4 1 (PPrint.group (PPrint.string "forall" ^/^ kinds_to_doc (Vector.to_list universals)))
            (PPrint.dot ^^ PPrint.blank 1 ^^ body)

    and uv_to_doc s uv = match Uv.get s uv with
        | (_, Unassigned (name, _)) -> PPrint.qmark ^^ Name.to_doc name
        | (s, Assigned t) -> to_doc s t

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
            Vector1.fold_left (fun doc arg -> PPrint.infix 4 1 PPrint.at doc (to_doc s arg))
                (instantiee_to_doc s co) args
        | AUse name -> Name.to_doc name
        | TypeCo co -> PPrint.brackets (PPrint.equals ^^ PPrint.break 1 ^^ coercion_to_doc s co)
        | Patchable {contents} -> coercion_to_doc s contents

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

    (* --- *)

    let to_abs typ = Exists (Vector.of_list [], Hole, typ)

    let freshen (name, kind) = (Name.freshen name, kind)

    let sibling sr uv = match Uv.getr sr uv with
        | Unassigned (_, level) ->
            let (s, uv') = Uv.make (!sr) (Unassigned (Name.fresh (), level)) in
            sr := s;
            uv'
        | Assigned _ -> failwith "unreachable"

    (* --- *)

    let rec expose_abs' sr depth substitution (Exists (params, locator, body)) =
        let depth = depth + 1 in
        Exists (params, expose_locator' sr depth substitution locator, expose' sr depth substitution body)

    and expose' sr depth substitution = function
        | Pi (params, domain, eff, codomain) ->
            let depth = depth + 1 in
            let expose_domain sr (locator, domain) =
                (expose_locator' sr depth substitution locator, expose' sr depth substitution domain) in
            Pi (params, Vector.map (expose_domain sr) domain, eff, expose_abs' sr depth substitution codomain)
        | Record fields ->
            Record (Vector.map (fun {label; typ} ->
                                    {label; typ = expose' sr depth substitution typ}) fields)
        | Type typ -> Type (expose_abs' sr depth substitution typ)
        | Fn body -> Fn (expose' sr (depth + 1) substitution body)
        | App (callee, args) ->
            let args = Vector1.map (expose' sr depth substitution) args in
            (match expose' sr depth substitution callee with
            | App (callee, args') -> App (callee, Vector1.append args' args) (* TODO: is this sufficient? *)
            | callee -> App (callee, args))
        | Bv {depth = depth'; sibli} as typ ->
            if depth' = depth
            then Vector.get substitution sibli
            else typ
        | Uv uv as typ ->
            (match Uv.getr sr uv with
            | Assigned typ -> expose' sr depth substitution typ
            | Unassigned _ -> typ)
        | (Use _ | Ov _ | Prim _) as typ -> typ

    and expose_locator' sr depth substitution = function
        | PiL codomain -> PiL (expose_locator' sr depth substitution codomain)
        | RecordL fields ->
            RecordL (Vector.map (fun {label; typ} ->
                                    {label; typ = expose_locator' sr depth substitution typ}) fields)
        | TypeL path -> TypeL (expose' sr depth substitution path)
        | Hole -> Hole

    let expose_abs sr = expose_abs' sr 0
    let expose sr = expose' sr 0
    let expose_locator sr = expose_locator' sr 0

    (* --- *)

    let rec close_abs' sr depth substitution (Exists (params, locator, body)) =
        let depth = depth + 1 in
        Exists (params, close_locator' sr depth substitution locator, close' sr depth substitution body)

    and close' sr depth substitution = function
        | Pi (params, domain, eff, codomain) ->
            let depth = depth + 1 in
            let close_domain sr (locator, domain) =
                (close_locator' sr depth substitution locator, close' sr depth substitution domain) in
            Pi (params, Vector.map (close_domain sr) domain, eff, close_abs' sr depth substitution codomain)
        | Record fields ->
            Record (Vector.map (fun {label; typ} ->
                                    {label; typ = close' sr depth substitution typ}) fields)
        | Type typ -> Type (close_abs' sr depth substitution typ)
        | Fn body -> Fn (close' sr (depth + 1) substitution body)
        | App (callee, args) ->
            let args = Vector1.map (close' sr depth substitution) args in
            (match close' sr depth substitution callee with
            | App (callee, args') -> App (callee, Vector1.append args' args) (* TODO: is this sufficient? *)
            | callee -> App (callee, args))
        | Ov ((name, _), _) as path ->
            Name.Map.find_opt name substitution
                |> Option.fold ~some: (fun sibli -> Bv {depth; sibli}) ~none: path
        | Uv uv as typ ->
            (match Uv.getr sr uv with
            | Assigned typ -> close' sr depth substitution typ
            | Unassigned _ -> typ)
        | (Use _ | Bv _ | Prim _) as typ -> typ

    and close_locator' sr depth substitution = function
        | PiL codomain -> PiL (close_locator' sr depth substitution codomain)
        | RecordL fields ->
            RecordL (Vector.map (fun {label; typ} ->
                                    {label; typ = close_locator' sr depth substitution typ}) fields)
        | TypeL path -> TypeL (close' sr depth substitution path)
        | Hole -> Hole

    let close sr = close' sr 0
    let close_locator sr = close_locator' sr 0
    let close_abs sr = close_abs' sr 0
end

