module Tx = Transactional
open Tx.Ref

module Typ = struct
    type level = int

    type t =
        | Uv of uv
        | Ov of ov
        | Bv of bv
        | Exists of {existentials : kind Vector1.t; body : t}
        | Pi of {universals : kind Vector.t; domain : t; eff : t; codomain : t}
        | Impli of {universals : kind Vector.t; domain : t; codomain : t}
        | Pair of {fst : t; snd : t}
        | Record of t
        | Variant of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of t
        | Fn of {param : kind; body : t}
        | App of {callee : t; arg : t}
        | Prim of Prim.t

    and uv = uvv Tx.Ref.t

    and uvv =
        | Unassigned of bool * Name.t * kind * level
        | Assigned of typ

    and ov = {name : Name.t; kind : kind; level : level}

    and bv = {depth : int; sibli : int; bkind : kind}

    and def = Name.t * kind

    and 'typ coercion =
        | Refl of 'typ
        | Symm of 'typ coercion
        | Trans of 'typ coercion * 'typ coercion
        | Comp of 'typ coercion * 'typ coercion Vector1.t
        | Axiom of kind Vector.t * 'typ * 'typ
        | AUse of Name.t
        | ExistsCo of kind Vector1.t * 'typ coercion
        | Inst of 'typ coercion * 'typ Vector1.t
        | PiCo of {universals : kind Vector.t
            ; domain : 'typ coercion; codomain : 'typ coercion}
        | PairCo of 'typ coercion * 'typ coercion
        | RecordCo of 'typ coercion
        | VariantCo of 'typ coercion
        | WithCo of {base : 'typ coercion; label : Name.t; field : 'typ coercion}
        | ProxyCo of 'typ coercion
        | Patchable of 'typ coercion Tx.Ref.t

    and typ = t

    and kind = t

    (* --- *)

    let exists_prec = 0
    let pi_prec = exists_prec
    let fn_prec = pi_prec
    let with_prec = fn_prec + 1
    let app_prec = with_prec + 1

    let prec_parens required doc = if required then PPrint.parens doc else doc

    let rec to_doc t =
        let open PPrint in

        let rec to_doc_prec prec = function
            | Uv uv -> (match !uv with
                | Assigned t -> to_doc_prec prec t
                | Unassigned (_, name, _, _) -> qmark ^^ Name.to_doc name)

            | Exists {existentials; body} ->
                prefix 4 1
                    (string "exists" ^/^ tparams_to_doc (Vector1.to_list existentials))
                    (dot ^^ blank 1 ^^ to_doc_prec exists_prec body)
                |> prec_parens (prec > exists_prec)

            | Pi {universals; domain; eff; codomain} when Vector.length universals > 0 ->
                prefix 4 1
                    (string "forall" ^/^ tparams_to_doc (Vector.to_list universals))
                    (dot ^^ blank 1
                    ^^ infix 4 1 (string "-!" ^^ blank 1 ^^ to_doc eff)
                        (to_doc_prec (pi_prec + 1) domain)
                        (string "->" ^^ blank 1 ^^ to_doc_prec pi_prec codomain))
                |> prec_parens (prec > pi_prec)

            | Pi {universals = _; domain; eff; codomain} ->
                infix 4 1 (string "-!" ^^ blank 1 ^^ to_doc eff)
                    (to_doc_prec (pi_prec + 1) domain)
                    (string "->" ^^ blank 1 ^^ to_doc_prec pi_prec codomain)

            | Impli {universals = _; domain; codomain} ->
                infix 4 1 (string "=>")
                    (to_doc_prec (pi_prec + 1) domain) (to_doc_prec pi_prec codomain)

            | Fn {param; body} ->
                prefix 4 1
                    (string "fn" ^/^ to_doc param)
                    (dot ^^ blank 1 ^^ to_doc_prec fn_prec body)
                |> prec_parens (prec > fn_prec)

            | App {callee; arg} ->
                prefix 4 1 (to_doc_prec app_prec callee) (to_doc_prec (app_prec + 1) arg)
                |> prec_parens (prec > app_prec)

            | Pair {fst; snd} ->
                surround_separate_map 4 0 (parens colon)
                    (lparen ^^ colon) (comma ^^ break 1) rparen
                    to_doc [fst; snd]

            | Record row -> braces (to_doc row)

            | Variant row -> parens (prefix 4 1 sharp (to_doc row))

            | With {base; label; field} ->
                infix 4 1 (string "with" ^^ blank 1 ^^ Name.to_doc label ^^ blank 1 ^^ equals)
                    (to_doc_prec with_prec base) (to_doc_prec (with_prec + 1) field)
                |> prec_parens (prec > with_prec)

            | EmptyRow -> parens bar

            | Proxy carrie -> brackets (prefix 4 1 equals (to_doc carrie))

            | Ov {name; kind = _; level = _} -> Name.to_doc name

            | Bv {depth; sibli; bkind = _} ->
                string (Int.to_string depth) ^^ dot ^^ string (Int.to_string sibli)

            | Prim pt -> string "__" ^^ Prim.to_doc pt in

        to_doc_prec 0 t

    and kind_to_doc t = to_doc t

    and tparams_to_doc kinds = PPrint.(separate_map (break 1) kind_to_doc kinds)

    let def_to_doc (name, kind) =
        PPrint.(infix 4 1 colon (Name.to_doc name) (kind_to_doc kind))

    let coercion_to_doc' typ_to_doc =
        let open PPrint in

        let rec to_doc = function
            | ExistsCo (existentials, body) ->
                infix 4 1 dot
                    (string "exists" ^^ blank 1
                        ^^ separate_map (blank 1) kind_to_doc (Vector1.to_list existentials))
                    (to_doc body)
            | Refl typ -> typ_to_doc typ
            | Symm co -> string "symm" ^^ blank 1 ^^ to_doc co
            | Trans (co, co') ->
                infix 4 1 (bquotes (string "o"))
                    (to_doc co) (andco_to_doc'  co')
            | Comp (ctor_co, arg_cos) ->
                prefix 4 1 (ctorco_to_doc'  ctor_co)
                    (separate_map (break 1) (argco_to_doc' )
                    (Vector1.to_list arg_cos))
            | Inst (co, args) ->
                Vector1.fold (fun doc arg -> infix 4 1 at doc (typ_to_doc arg))
                    (instantiee_to_doc'  co) args
            | AUse name -> Name.to_doc name
            | Axiom (universals, l, r) ->
                let body_doc = infix 4 1 (string "~") (typ_to_doc l) (typ_to_doc r) in
                (match Vector.length universals with
                | 0 -> body_doc
                | _ -> infix 4 1 dot
                    (string "forall" ^^ blank 1
                        ^^ separate_map (blank 1) kind_to_doc (Vector.to_list universals))
                    body_doc)

            | PiCo {universals; domain; codomain} ->
                let body_doc = infix 4 1 (string "->") (to_doc domain) (to_doc codomain) in
                (match Vector.length universals with
                | 0 -> body_doc
                | _ -> infix 4 1 dot
                    (string "forall" ^^ blank 1
                        ^^ separate_map (blank 1) kind_to_doc (Vector.to_list universals))
                    body_doc)

            | PairCo (fst, snd) ->
                surround_separate_map 4 1 (parens colon)
                    (lparen ^^ colon) (comma ^^ break 1) rparen
                    to_doc [fst; snd]

            | RecordCo row_co -> braces (to_doc row_co)
            
            | VariantCo row_co -> parens (prefix 4 1 sharp (to_doc row_co))

            | WithCo {base; label; field} ->
                infix 4 1 (string "with") (base_co_to_doc'  base)
                    (infix 4 1 colon (Name.to_doc label)
                    (to_doc field))
            | ProxyCo co ->
                brackets (equals ^^ break 1 ^^ to_doc co)
            | Patchable ref -> to_doc !ref

        and andco_to_doc'  = function
            | Trans _ as co -> PPrint.parens (to_doc co)
            | co -> to_doc co

        and ctorco_to_doc'  = function
            | (Symm _ | Trans _ | Inst _) as co -> PPrint.parens (to_doc co)
            | co -> to_doc co

        and argco_to_doc'  = function
            | (Trans _ | Inst _ | Comp _) as co ->
                PPrint.parens (to_doc co)
            | co -> to_doc co

        and instantiee_to_doc'  = function
            | (Symm _ | Trans _) as co -> PPrint.parens (to_doc co)
            | co -> to_doc co

        and base_co_to_doc'  = function
            | (Trans _ | Comp _ | Inst _) as co ->
                PPrint.parens (to_doc co)
            | co -> to_doc co

        in to_doc

    let coercion_to_doc = coercion_to_doc' to_doc

    let map_coercion_children f co = match co with
        | Symm arg ->
            let arg' = f arg in
            if arg' == arg then co else Symm arg'

        | Trans (co1, co2) ->
            let co1' = f co1 in
            let co2' = f co2 in
            if co1' == co1 && co2' == co2 then co else Trans (co1', co2')

        | ExistsCo (existentials, body) ->
            let body' = f body in
            if body' == body then co else ExistsCo (existentials, body')

        | PiCo {universals; domain; codomain} ->
            let domain' = f domain in
            let codomain' = f codomain in
            if domain' == domain && codomain' == codomain
            then co
            else PiCo {universals; domain = domain'; codomain = codomain'}

        | RecordCo row ->
            let row' = f row in
            if row' == row then co else RecordCo row'

        | VariantCo row ->
            let row' = f row in
            if row' == row then co else VariantCo row'

        | PairCo (fst, snd) ->
            let fst' = f fst in
            let snd' = f snd in
            if fst' == fst && snd' == snd then co else PairCo (fst', snd')

        | WithCo {base; label; field} ->
            let base' = f base in
            let field' = f field in
            if base' == base && field' == field
            then co
            else WithCo {base = base'; label; field = field'}

        | ProxyCo carrie ->
            let carrie' = f carrie in
            if carrie' == carrie then co else ProxyCo carrie'

        | Comp (callee, args) ->
            let callee' = f callee in
            let args' = Vector1.map_children f args in
            if callee' == callee && args' == args then co else Comp (callee', args')

        | Inst (co', args) ->
            let co'' = f co' in
            if co'' == co' then co else Inst (co'', args)

        | Refl _ | Axiom _ | AUse _ -> co

        | Patchable rco -> Patchable (ref (f !rco))

    (* OPTIMIZE: map_children: *)
    let rec close' depth substitution : t -> t = function
        | Exists {existentials; body} ->
            let depth = depth + 1 in
            Exists {existentials; body = close' depth substitution body}
        | Pi {universals; domain; eff; codomain} ->
            let depth = depth + 1 in
            Pi { universals
               ; domain = close' depth substitution domain
               ; eff = close' depth substitution eff
               ; codomain = close' depth substitution codomain }
        | Impli {universals; domain; codomain} ->
            let depth = depth + 1 in
            Impli { universals
                   ; domain = close' depth substitution domain
                   ; codomain = close' depth substitution codomain }
        | Pair {fst; snd} -> Pair {fst = close' depth substitution fst
            ; snd = close' depth substitution snd}
        | Record row -> Record (close' depth substitution row)
        | Variant row -> Variant (close' depth substitution row)
        | With {base; label; field} ->
            With {base = close' depth substitution base; label
                ; field = close' depth substitution field}
        | EmptyRow -> EmptyRow
        | Proxy typ -> Proxy (close' depth substitution typ)
        | Fn {param; body} -> Fn {param; body = close' (depth + 1) substitution body}
        | App {callee; arg} -> App {callee = close' depth substitution callee
            ; arg = close' depth substitution arg}
        | (Ov {name; kind; _}) as path ->
            Name.Map.find_opt name substitution
                |> Option.fold ~some: (fun sibli -> Bv {depth; sibli; bkind = kind}) ~none: path
        | Uv uv as typ ->
            (match !uv with
            | Assigned typ -> close' depth substitution typ
            | Unassigned _ -> typ)
        | (Bv _ | Prim _) as typ -> typ
 
    let close = close' 0

    (* OPTIMIZE: map_children: *)
    let rec close_coercion' depth substitution : t coercion -> t coercion = function
        | ExistsCo (params, body) ->
            let depth = depth + 1 in
            ExistsCo (params, close_coercion' depth substitution body)
        | PiCo {universals; domain; codomain} ->
            let depth = depth + 1 in
            PiCo { universals
               ; domain = close_coercion' depth substitution domain
               ; codomain = close_coercion' depth substitution codomain }
        | PairCo (fst, snd) -> PairCo (close_coercion' depth substitution fst
            , close_coercion' depth substitution snd)
        | RecordCo row -> RecordCo (close_coercion' depth substitution row)
        | VariantCo row -> VariantCo (close_coercion' depth substitution row)
        | WithCo {base; label; field} ->
            WithCo {base = close_coercion' depth substitution base
                ; label; field = close_coercion' depth substitution field}
        | ProxyCo co -> ProxyCo (close_coercion' depth substitution co)
        | Refl typ -> Refl (close' depth substitution typ)
        | Symm co -> Symm (close_coercion' depth substitution co)
        | Trans (co, co') -> Trans (close_coercion' depth substitution co
            , close_coercion' depth substitution co')
        | Comp (co, cos) -> Comp (close_coercion' depth substitution co
            , Vector1.map (close_coercion' depth substitution) cos)
        | Inst (co, typs) -> Inst (close_coercion' depth substitution co
            , Vector1.map (close' depth substitution) typs)
        | AUse _ as co -> co
        | Axiom (universals, l, r) ->
            let depth = depth + 1 in
            Axiom (universals, close' depth substitution l
                , close' depth substitution r)
        | Patchable r as co ->
            r := (close_coercion' depth substitution !r);
            co

    let close_coercion = close_coercion' 0

    (* OPTIMIZE: map_children: *)
    let rec expose' depth substitution : t -> t = function
        | Exists {existentials; body} ->
            let depth = depth + 1 in
            Exists {existentials; body = expose' depth substitution body}
        | Pi {universals; domain; eff; codomain} ->
            let depth = depth + 1 in
            Pi { universals
                ; domain = expose' depth substitution domain
                ; eff = expose' depth substitution eff
                ; codomain = expose' depth substitution codomain }
        | Impli {universals; domain; codomain} ->
            let depth = depth + 1 in
            Impli { universals
                    ; domain = expose' depth substitution domain
                    ; codomain = expose' depth substitution codomain }
        | Pair {fst; snd} -> Pair {fst = expose' depth substitution fst
            ; snd = expose' depth substitution snd}
        | Record row -> Record (expose' depth substitution row)
        | Variant row -> Variant (expose' depth substitution row)
        | With {base; label; field} ->
            With {base = expose' depth substitution base; label
                ; field = expose' depth substitution field}
        | EmptyRow -> EmptyRow
        | Proxy typ -> Proxy (expose' depth substitution typ)
        | Fn {param; body} -> Fn {param; body = expose' (depth + 1) substitution body}
        | App {callee; arg} -> App {callee = expose' depth substitution arg
            ; arg = expose' depth substitution callee}
        | Bv {depth = depth'; sibli; bkind = _} as typ ->
            if depth' = depth
            then Vector.get substitution sibli
            else typ
        | Uv uv as typ ->
            (match !uv with
            | Assigned typ -> expose' depth substitution typ
            | Unassigned _ -> typ)
        | (Ov _ | Prim _) as typ -> typ

    let expose = expose' 0

    let ov_eq {name; _} {name = name'; _} = Name.equal name name'

    module OvHashSet = CCHashSet.Make (struct
        type t = ov
        let hash {name; _} = Name.hash name
        let equal = ov_eq
    end)
end

(* HACK: OCaml these constants are 'unsafe' for OCaml recursive modules,
 * so we have to add them here: *)
module Type = struct
    include Typ

    (* __typeIn __boxed *)
    let aType = App {callee = Prim TypeIn; arg = Prim Boxed}
    let aKind = aType

    (* __rowOf (__typeIn __boxed) *)
    let aRow = App {callee = Prim RowOf; arg = aType}
end

