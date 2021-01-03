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
        | Pi of {universals : kind Vector.t; domain : t; eff : t; codomain : t}
        | Impli of {universals : kind Vector.t; domain : t; codomain : t}
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

    let rec non_uv_head s = function
        | Uv uv -> (match Uv.get s uv with
            | Assigned typ -> non_uv_head s typ
            | Unassigned _ -> failwith "TODO: Unassigned")
        | typ -> typ

    let grammar s =
        let exists = PIso.prism (fun (existentials, body) -> Exists (existentials, body))
            (fun typ ->
                match non_uv_head s typ with
                | Exists (existentials, body) -> Some (existentials, body)
                | _ -> None) in

        let pi = PIso.prism (fun (universals, domain, eff, codomain) ->
                Pi {universals; domain; eff; codomain}) (fun typ ->
            match non_uv_head s typ with
            | Pi {universals; domain; eff; codomain} -> Some (universals, domain, eff, codomain)
            | _ -> None) in

        let impli = PIso.prism (fun (universals, domain, codomain) ->
                Impli {universals; domain; codomain}) (fun typ ->
            match non_uv_head s typ with
            | Impli {universals; domain; codomain} -> Some (universals, domain, codomain)
            | _ -> None) in

        let promoted_array = PIso.prism (fun typs -> PromotedArray typs) (fun typ ->
            match non_uv_head s typ with
            | PromotedArray typs -> Some typs
            | _ -> None) in

        let promoted_tuple = PIso.piso (fun typs ->
                if Vector.length typs <> 1 then Some (PromotedTuple typs) else None)
            (fun typ ->
                match non_uv_head s typ with
                | PromotedTuple typs -> Some typs
                | _ -> None) in

        let tuple = PIso.prism (fun typs -> Tuple typs) (fun typ ->
            match non_uv_head s typ with
            | Tuple typs -> Some typs
            | _ -> None) in

        let record = PIso.prism (fun typ -> Record typ) (fun typ ->
            match non_uv_head s typ with
            | Record typ -> Some typ
            | _ -> None) in

        let empty_row = PIso.prism (fun () -> EmptyRow) (fun typ ->
            match non_uv_head s typ with
            | EmptyRow -> Some ()
            | _ -> None) in

        let proxy = PIso.prism (fun typ -> Proxy typ) (fun typ ->
            match non_uv_head s typ with
            | Proxy typ -> Some typ
            | _ -> None) in

        let fn = PIso.prism (fun (param, body) -> Fn (param, body)) (fun typ ->
            match non_uv_head s typ with
            | Fn (param, body) -> Some (param, body)
            | _ -> None) in

        let app = PIso.prism (fun (callee, arg) -> App (callee, arg)) (fun typ ->
            match non_uv_head s typ with
            | App (callee, arg) -> Some (callee, arg)
            | _ -> None) in

        let bv = PIso.prism (fun (depth, sibli) ->
                Bv {depth; sibli; (* HACK: *) kind = EmptyRow})
            (fun typ -> 
                match non_uv_head s typ with
                | Bv {depth; sibli; kind = _} -> Some (depth, sibli)
                | _ -> None) in

        let prim = PIso.prism (fun op -> Prim op) (fun typ ->
            match non_uv_head s typ with
            | Prim op -> Some op
            | _ -> None) in

        let open Grammar in let open Grammar.Infix in
        fix (fun typ ->
            let promoted_array =
                surround_separate 4 0 (brackets (pure Vector.empty))
                    lbracket (comma <* break 1) rbracket typ
                |> map promoted_array in

            let promoted_tuple =
                surround_separate 4 0 (parens (pure Vector.empty))
                    lparen (comma <* break 1) rparen typ
                |> map promoted_tuple in

            let tuple =
                surround_separate 4 0 (parens (colon *> pure Vector.empty))
                    (lparen <* colon) (comma <* break 1) rparen typ
                |> map tuple in

            let surrounded =
                promoted_array <|> promoted_tuple <|> tuple
                <|> (record <$> braces typ)
                <|> (empty_row <$> parens bar)
                <|> (proxy <$> brackets (equals *> blank 1 *> typ))
                <|> parens typ in

            let atom =
                let ov = PIso.prism (fun _ -> failwith "TODO") (fun typ ->
                    match non_uv_head s typ with
                    | Ov ((name, _), _) -> Some name
                    | _ -> None) in
                ov <$> Name.grammar
                <|> (bv <$> (caret *> int <*> slash *> int))
                <|> (prim <$> text "__" *> Prim.grammar) in

            let nestable = atom <|> surrounded in

            let app = app <$> (nestable <* break 1 <*> nestable)
                <|> nestable in

            let non_fn = 
                let f = PIso.iso (fun (base, fields) ->
                    List.fold_left (fun base (label, field) -> With {base; label; field})
                        base (Option.value ~default: [] fields))
                    (fun typ ->
                        let rec loop fields typ =
                            match non_uv_head s typ with
                            | With {base; label; field} ->
                                loop ((label, field) :: fields) base
                            | base -> (match fields with
                                | _ :: _ -> (base, Some fields)
                                | [] -> (base, None)) in
                        loop [] typ) in
                let label =
                    PIso.string <$> (many1 (sat (Fun.negate (String.contains " \t\r\n"))))
                    |> map Name.basename_iso in
                f <$> (app <*> opt (break 1 *> (many1 (text "with" *> blank 1 *> infix 4 1 equals label app)))) in

            let exists =
                let adapt = PIso.iso (fun (existentials, body) ->
                        (Option.get (Vector1.of_list existentials), body))
                    (fun (existentials, body) -> (Vector1.to_list existentials, body)) in
                let existentials = separate1 (blank 1) nestable in
                PIso.comp exists adapt <$> infix 4 1 dot (text "exists" *> existentials) typ in

            let pi =
                let adapt = PIso.iso (fun (universals, ((domain, eff), codomain)) ->
                        ( Vector.of_list universals
                        , Option.value ~default: EmptyRow eff
                        , domain, codomain ))
                    (fun (universals, domain, eff, codomain) ->
                        let eff = match non_uv_head s eff with
                            | EmptyRow -> None
                            | eff -> Some eff in
                        (Vector.to_list universals, ((domain, eff), codomain))) in
                let universals = text "forall" *> blank 1 *> separate1 (blank 1) nestable
                    <* blank 1 <* dot in
                let arrow = opt (text "-!" *> blank 1 *> non_fn <* blank 1) <* text "->" in
                let monomorphic = prefix 4 1 (non_fn <*> blank 1 *> arrow) typ in
                PIso.comp pi adapt <$>
                    (prefix 4 1 universals monomorphic
                    <|> (pure [] <*> monomorphic)) in

            let impli =
                let adapt = PIso.iso (fun (universals, (domain, codomain)) ->
                        ( Vector.of_list (Option.value ~default: [] universals)
                        , domain, codomain ))
                    (fun (universals, domain, codomain) ->
                        let universals = match Vector.length universals with
                            | 0 -> Some (Vector.to_list universals)
                            | _ -> None in
                        (universals, (domain, codomain))) in
                let universals = text "forall" *> blank 1 *> separate1 (blank 1) nestable
                    <* blank 1 <* dot in
                let monomorphic = infix 4 1 (text "=>") non_fn typ in
                PIso.comp impli adapt <$> prefix 4 1 (opt universals) monomorphic in

            exists <|> pi <|> impli
            <|> (fn <$> (infix 4 1 dot (text "fn" *> blank 1 *> non_fn) typ))
            <|> non_fn)

    let to_doc s = PPrinter.of_grammar (grammar s) (* OPTIMIZE *)

    let rec kind_to_doc s kind = to_doc s kind

    and kinds_to_doc s kinds = PPrint.(separate_map (break 1) (kind_to_doc s) kinds)

    let rec template_to_doc s tpl =
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

