open Streaming

open Asserts

type 'a txref = 'a TxRef.t

let ref = TxRef.ref
let (!) = TxRef.(!)
let (:=) = TxRef.(:=)

module Typ = struct
    module PP = PPrint

    type quantifier = ForAll | Exists

    type t =
        | Uv of {quant : quantifier; bound : bound txref}
        | Ov of {binder : scope; kind : t}
        | Pi of {domain : t; eff : t; codomain : t} (* -! -> *)
        | Impli of {domain : t; codomain : t} (* => *)
        | Fn of {param : kind; body : t} (* type lambda *)
        | App of t * t
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of t
        | Tuple of t Vector.t
        | PromotedTuple of t Vector.t
        | PromotedArray of t Vector.t
        | Prim of Prim.t

    and kind = t

    and bound =
        | Bot of {level :int; binder : binder; kind : kind}
        | Flex of {level :int; binder : binder; bound : t}
        | Rigid of {level :int; binder : binder; bound : t}

    and binder =
        | Scope of scope
        | Type of bound txref

    and scope =
        | Local of {level : int; parent : scope}
        | Global

    and coercion = Refl of t

(*
    and template = TupleL of int

    and 'typ coercion =
        | ExistsCo of kind Vector1.t * 'typ coercion
        | Refl of 'typ
        | Symm of 'typ coercion
        | Trans of 'typ coercion * 'typ coercion
        | Comp of 'typ coercion * 'typ coercion Vector1.t
        | Inst of 'typ coercion * 'typ Vector1.t
        | AUse of Name.t
        | Axiom of kind Vector.t * 'typ * 'typ
        | PiCo of {universals : kind Vector.t
            ; domain : 'typ coercion; codomain : 'typ coercion}
        | PromotedArrayCo of 'typ coercion Vector.t
        | PromotedTupleCo of 'typ coercion Vector.t
        | TupleCo of 'typ coercion Vector.t
        | RecordCo of 'typ coercion
        | WithCo of {base : 'typ coercion; label : Name.t; field : 'typ coercion}
        | ProxyCo of 'typ coercion
*)

    (* --- *)

    type typ = t
    module Hashtbl = CCHashtbl.Make (struct
        type t = typ

        let equal = (==)
        let hash = Hashtbl.hash
    end)

    (* --- *)

    module Bound = struct
        type t = bound

        let binder = function
            | Bot {binder; _} -> binder
            | Flex {binder; _} -> binder
            | Rigid {binder; _} -> binder

        module Hashtbl = TxRef.Hashtbl.Make (struct type t = bound end)
    end

    module Scope = struct
        type t = scope

        let level = function
            | Local {level; _} -> level
            | Global -> 0
    end

    module Binder = struct
        type t = binder

        let level = function
            | Type t -> (match !t with
                | Bot {level; _} | Flex {level; _} | Rigid {level; _} ->
                    assert (level > 0);
                    level)
            | Scope scope -> Scope.level scope
    end

    (* --- *)

    (* OPTIMIZE: Path compression, ranking: *)
    let rec force = fun t -> match t with
        | Uv {quant = _; bound} -> (match !bound with
            | Flex _ | Bot _ -> t
            | Rigid {level = _; binder = _; bound} -> force bound)
        | Ov _ | Fn _ | App _ | Pi _ | Impli _
        | Record _ | With _ | EmptyRow | Proxy _ | Prim _
        | Tuple _ | PromotedTuple _ | PromotedArray _ -> t

    let iter f = function
        | Fn {param; body} -> f param; f body
        | App (callee, arg) -> f callee; f arg
        | Pi {domain; eff; codomain} -> f domain; f eff; f codomain
        | Impli {domain; codomain} -> f domain; f codomain
        | Record row -> f row
        | With {base; label = _; field} -> f base; f field
        | Tuple typs | PromotedTuple typs | PromotedArray typs -> Vector.iter f typs
        | Proxy typ -> f typ
        | EmptyRow | Prim _ | Uv _ | Ov _ -> ()

    let map_children =
        let all_eq xs ys =
            Stream.from (Source.zip_with (==) (Vector.to_source xs) (Vector.to_source ys))
            |> Stream.into (Sink.all ~where: Fun.id) in

        fun f t -> match force t with
        | Uv {quant; bound} -> (match !bound with
            | Bot _ -> t
            | Flex {level; binder; bound} ->
                let bound' = f bound in
                if bound' == bound
                then t
                else Uv {quant; bound = ref (Flex {level; binder; bound = bound'})}
            | Rigid _ -> unreachable None)

        | Fn {param; body} ->
            let body' = f body in
            if body' == body then t else Fn {param; body = body'}

        | App (callee, arg) ->
            let callee' = f callee in
            let arg' = f arg in
            if callee' == callee && arg' == arg then t else App (callee', arg')

        | Pi {domain; eff; codomain} ->
            let domain' = f domain in
            let eff' = f eff in
            let codomain' = f codomain in
            if domain' == domain && eff' == eff && codomain' == codomain
            then t
            else Pi {domain = domain'; eff = eff'; codomain = codomain'}

        | Impli {domain; codomain} ->
            let domain' = f domain in
            let codomain' = f codomain in
            if domain' == domain && codomain' == codomain
            then t
            else Impli {domain = domain'; codomain = codomain'}

        | Record row ->
            let row' = f row in
            if row' == row then t else Record row'

        | With {base; label; field} ->
            let base' = f base in
            let field' = f field in
            if base' == base && field' == field
            then t
            else With {base = base'; label; field = field'}

        | Proxy carrie ->
            let carrie' = f carrie in
            if carrie' == carrie then t else Proxy carrie'

        | Tuple typs ->
            let typs' = Vector.map f typs in
            if all_eq typs' typs then t else Tuple typs

        | PromotedTuple typs ->
            let typs' = Vector.map f typs in
            if all_eq typs' typs then t else PromotedTuple typs

        | PromotedArray typs ->
            let typs' = Vector.map f typs in
            if all_eq typs' typs then t else PromotedArray typs

        | EmptyRow | Prim _ | Ov _ -> t

    (* --- *)

    type flag = SFlex | SRigid

    type syn =
        | SExists of squant_param Vector1.t * syn
        | SForAll of squant_param Vector1.t * syn
        | SFn of {param : stypedef; body : syn} (* type lambda *)
        | SApp of {callee : syn; arg : syn}
        | SVar of Name.t
        | SBot
        | SPi of {domain : syn; eff : syn; codomain : syn} (* -! -> *)
        | SImpli of {domain : syn; codomain : syn} (* => *)
        | SRecord of syn
        | SWith of {base : syn; label : Name.t; field : syn}
        | SEmptyRow
        | SProxy of syn
        | STuple of syn Vector.t
        | SPromotedTuple of syn Vector.t
        | SPromotedArray of syn Vector.t
        | SPrim of Prim.t

    and stypedef = Name.t * skind

    and squant_param = Name.t * flag * syn

    and skind = syn

    (*let flag_to_string = function
        | SFlex -> ">="
        | SRigid -> "="*)

    let arrow_prec = 1

    let syn_to_doc syn =
        let open PPrint in

        let rec to_doc _ = function
            | SPi {domain; eff = _; codomain} ->
                infix 4 1 (string "->") (to_doc (arrow_prec + 1) domain)
                    (to_doc arrow_prec codomain)
            | SVar name -> Name.to_doc name
            | SBot -> qmark ^^ underscore
            | SEmptyRow -> parens bar
            | STuple typs -> surround_separate_map 4 1 (parens empty)
                lparen (comma ^^ break 1) rparen
                (to_doc 0) (Vector.to_list typs)
            | SPrim p -> Prim.to_doc p
            | _ -> todo None in

        to_doc 0 syn

    let to_syn ctx t =
        let bindees = Bound.Hashtbl.create 0 in
        let add_bindee t = match force t with
            | Uv {quant = _; bound} -> (match Bound.binder !bound with
                | Type binder ->
                    Bound.Hashtbl.update bindees ~k: binder ~f: (fun _ -> function
                        | Some bs as v -> CCVector.push bs t; v
                        | None -> Some (CCVector.of_list [t]))
                | Scope _ -> ())
            | _ -> () in

        let inlineabilities = Hashtbl.create 0 in
        let add_inlineability t inlineable' =
            Hashtbl.update inlineabilities ~k: t ~f: (fun _ -> function
                | Some inlineable -> Some (inlineable && inlineable')
                | None -> Some inlineable') in

        let rec analyze (parent : bound txref option) covariant t =
            let t = force t in
            if Hashtbl.mem inlineabilities t
            then add_inlineability t false
            else begin
                let inlineable = match parent with
                    | Some parent -> (match force t with
                        | Uv {quant = _; bound} -> (match Bound.binder !bound with
                            | Type binder ->
                                TxRef.equal binder parent && (match !bound with
                                | Bot _ | Flex _ -> covariant
                                | Rigid _ -> not covariant)
                            | Scope _ -> false)
                        | _ -> true)
                    | None -> false in
                add_inlineability t inlineable;

                let parent = match force t with
                    | Uv {quant = _; bound} -> Some bound
                    | _ -> None in
                (match force t with
                | Pi {domain; eff; codomain} ->
                    analyze parent false domain;
                    analyze parent false eff;
                    analyze parent true codomain;
                | Impli {domain; codomain} ->
                    analyze parent false domain;
                    analyze parent true codomain;

                | Record _ | With _ | Tuple _ -> iter (analyze parent true) t

                | Fn _ | App _ | Proxy _ | PromotedTuple _ | PromotedArray _ ->
                    iter (analyze parent false) t
                | EmptyRow | Prim _ | Uv _ | Ov _ -> ());

                add_bindee t;
            end in
        analyze None false t;

        let vne = Hashtbl.create 0 in
        let fresh_qname t =
            let name = Name.fresh () in
            Hashtbl.add vne t (SVar name);
            name in

        let rec contextualize t = match Hashtbl.get ctx t with
            | Some (name, _) -> name
            | None ->
                let name = Name.fresh () in
                Hashtbl.add ctx t (name, to_syn t);
                name

        and to_syn t =
            let bindees = match force t with
                | Uv {quant = _; bound} -> (match Bound.Hashtbl.get bindees bound with
                    | Some bindees -> bindees
                    | None -> CCVector.create ())
                | _ -> CCVector.create () in
            CCVector.rev_in_place bindees;
            let bindees = CCVector.to_array bindees in
            let (existentials, universals) = Stream.from (Source.array bindees)
                |> Stream.filter (Hashtbl.find inlineabilities)
                |> Stream.map (function
                    | Uv {quant; bound} as bindee ->
                        let sbindee = to_syn bindee in
                        let flag = match !bound with
                            | Bot _ | Flex _ -> SFlex
                            | Rigid _ -> SRigid in
                        let name = fresh_qname bindee in
                        (quant, (name, flag, sbindee))
                    | _ -> unreachable None)
                |> Stream.into (Sink.zip
                    (Sink.prefilter (function (Exists, _) -> true | _ -> false)
                        (Sink.premap snd (Vector.sink ())))
                    (Sink.prefilter (function (ForAll, _) -> true | _ -> false)
                        (Sink.premap snd (Vector.sink ())))) in

            let body = match force t with
                | Uv {quant = _; bound} -> (match !bound with
                    | Bot _ -> SBot
                    | Flex _ -> (match Hashtbl.get vne t with
                        | Some syn -> syn
                        | None -> SVar (contextualize t))
                    | Rigid _ -> unreachable None)
                | Ov _ -> SVar (contextualize t)
                | Fn {param; body} ->
                    let pname = fresh_qname (force param) in
                    SFn {param = (pname, child_to_syn param); body = child_to_syn body}
                | App (callee, arg) ->
                    SApp {callee = child_to_syn callee; arg = child_to_syn arg}
                | Pi {domain; eff; codomain} ->
                    SPi {domain = child_to_syn domain; eff = child_to_syn eff
                        ; codomain = child_to_syn codomain}
                | Impli {domain; codomain} ->
                    SImpli {domain = child_to_syn domain; codomain = child_to_syn codomain}
                | Record row -> SRecord (child_to_syn row)
                | With { base; label; field} ->
                    SWith {base = child_to_syn base; label; field = child_to_syn field}
                | EmptyRow -> SEmptyRow
                | Tuple typs -> STuple (Vector.map child_to_syn typs)
                | PromotedTuple typs -> SPromotedTuple (Vector.map child_to_syn typs)
                | PromotedArray typs -> SPromotedArray (Vector.map child_to_syn typs)
                | Proxy typ -> SProxy (child_to_syn typ)
                | Prim p -> SPrim p in

            let syn = match Vector1.of_vector (Vector.rev universals) with
                | Some universals -> SForAll (universals, body)
                | None -> body in
            match Vector1.of_vector (Vector.rev existentials) with
            | Some existentials -> SExists (existentials, body)
            | None -> syn

        and child_to_syn (t : t) =
            let t = force t in
            if Hashtbl.find inlineabilities t
            then to_syn t
            else match Hashtbl.get vne t with
                | Some syn -> syn
                | None -> SVar (contextualize t) in

        to_syn (force t)

    let to_doc t =
        let ctx = Hashtbl.create 0 in
        let syn = to_syn ctx t in
        (*PPrint.(match Hashtbl.to_list ctx with
            | (_ :: _) as ctx ->
                infix 4 1 (string "in") (syn_to_doc syn)
                    (separate_map (comma ^^ blank 1) (fun (t, (name, syn)) ->
                        infix 4 1 (string (flag_to_string (t |> binder |> Binder.flag)))
                            (Name.to_doc name) (syn_to_doc syn)
                    ) ctx)
            | [] ->*) syn_to_doc syn(* )*)

    let kind_to_doc = to_doc

    (* --- *)

    (*
    let rec non_uv_head s = function
        | Var uv -> (match Uv.get s uv with
            | Assigned typ -> non_uv_head s typ
            | Unassigned _ -> todo None ~msg: "Unassigned")
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

        let with' = PIso.prism (fun (base, (label, field)) -> With {base; label; field})
            (fun typ -> match non_uv_head s typ with
            | With {base; label; field} -> Some (base, (label, field))
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
                let ov = PIso.prism (fun _ -> todo None) (fun typ ->
                    match non_uv_head s typ with
                    | Ov ((name, _), _) -> Some name
                    | _ -> None) in
                ov <$> Name.grammar
                <|> (bv <$> (caret *> int <*> slash *> int))
                <|> (prim <$> text "__" *> Prim.grammar) in

            let nestable = atom <|> surrounded in

            let app =
                PIso.fold_left app <$> (nestable <*> many (break 1 *> nestable)) in

            let non_fn =
                let adapt = PIso.map_snd PIso.opt_non_empty_list in
                let f = PIso.comp (PIso.fold_left with') adapt in
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
                        (Vector.of_list universals, domain, codomain))
                    (fun (universals, domain, codomain) ->
                        (Vector.to_list universals, (domain, codomain))) in
                let universals = text "forall" *> blank 1 *> separate1 (blank 1) nestable
                    <* blank 1 <* dot in
                let monomorphic = infix 4 1 (text "=>") non_fn typ in
                PIso.comp impli adapt <$>
                    (prefix 4 1 universals monomorphic
                    <|> (pure [] <*> monomorphic)) in

            exists <|> pi <|> impli
            <|> (fn <$> (infix 4 1 dot (text "fn" *> blank 1 *> non_fn) typ))
            <|> non_fn)

    let to_doc s = PPrinter.of_grammar (grammar s) (* OPTIMIZE *)

    let rec kind_to_doc s kind = to_doc s kind

    and kinds_to_doc s kinds = PPrint.(separate_map (break 1) (kind_to_doc s) kinds) *)

(*
    let template_to_doc _ tpl =
        let open PPrint in
        match tpl with
        | TupleL length ->
            surround_separate 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                (List.init length (fun _ -> underscore))

    and universal_to_doc s universals body =
        PPrint.(prefix 4 1 (group (string "forall" ^/^ (kinds_to_doc s) (Vector.to_list universals)))
            (dot ^^ blank 1 ^^ body))

    let rec coercion_to_doc' typ_to_doc s co =
        let open PPrint in
        match co with
        | ExistsCo (existentials, body) ->
            infix 4 1 dot
                (string "exists" ^^ blank 1
                    ^^ separate_map (blank 1) (kind_to_doc s) (Vector1.to_list existentials))
                (coercion_to_doc' typ_to_doc s body)
        | Refl typ -> typ_to_doc s typ
        | Symm co -> string "symm" ^^ blank 1 ^^ coercion_to_doc' typ_to_doc s co
        | Trans (co, co') ->
            infix 4 1 (bquotes (string "o"))
                (coercion_to_doc' typ_to_doc s co) (andco_to_doc' typ_to_doc s co')
        | Comp (ctor_co, arg_cos) ->
            prefix 4 1 (ctorco_to_doc' typ_to_doc s ctor_co)
                (separate_map (break 1) (argco_to_doc' typ_to_doc s)
                (Vector1.to_list arg_cos))
        | Inst (co, args) ->
            Vector1.fold (fun doc arg -> infix 4 1 at doc (typ_to_doc s arg))
                (instantiee_to_doc' typ_to_doc s co) args
        | AUse name -> Name.to_doc name
        | Axiom (universals, l, r) ->
            let body_doc = infix 4 1 (string "~") (typ_to_doc s l) (typ_to_doc s r) in
            (match Vector.length universals with
            | 0 -> body_doc
            | _ -> infix 4 1 dot
                (string "forall" ^^ blank 1
                    ^^ separate_map (blank 1) (kind_to_doc s) (Vector.to_list universals))
                body_doc)

        | PiCo {universals; domain; codomain} ->
            let body_doc = infix 4 1 (string "->")
                (coercion_to_doc' typ_to_doc s domain)
                (coercion_to_doc' typ_to_doc s codomain) in
            (match Vector.length universals with
            | 0 -> body_doc
            | _ -> infix 4 1 dot
                (string "forall" ^^ blank 1
                    ^^ separate_map (blank 1) (kind_to_doc s) (Vector.to_list universals))
                body_doc)

        | PromotedArrayCo coercions ->
            surround_separate_map 4 0 (brackets empty)
                lbracket (comma ^^ break 1) rbracket
                (coercion_to_doc' typ_to_doc s) (Vector.to_list coercions)
        | PromotedTupleCo coercions ->
            surround_separate_map 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                (coercion_to_doc' typ_to_doc s) (Vector.to_list coercions)
        | TupleCo coercions ->
            colon
                ^/^ separate_map (comma ^^ break 1) (coercion_to_doc' typ_to_doc s)
                    (Vector.to_list coercions)
            |> parens
        | RecordCo row_co -> braces (coercion_to_doc' typ_to_doc s row_co)
        | WithCo {base; label; field} ->
            infix 4 1 (string "with") (base_co_to_doc' typ_to_doc s base)
                (infix 4 1 colon (Name.to_doc label)
                (coercion_to_doc' typ_to_doc s field))
        | ProxyCo co ->
            brackets (equals ^^ break 1 ^^ coercion_to_doc' typ_to_doc s co)
        | Patchable ref -> coercion_to_doc' typ_to_doc s !ref

    and andco_to_doc' typ_to_doc s = function
        | Trans _ as co -> PP.parens (coercion_to_doc' typ_to_doc s co)
        | co -> coercion_to_doc' typ_to_doc s co

    and ctorco_to_doc' typ_to_doc s = function
        | (Symm _ | Trans _ | Inst _) as co -> PP.parens (coercion_to_doc' typ_to_doc s co)
        | co -> coercion_to_doc' typ_to_doc s co

    and argco_to_doc' typ_to_doc s = function
        | (Trans _ | Inst _ | Comp _) as co ->
            PP.parens (coercion_to_doc' typ_to_doc s co)
        | co -> coercion_to_doc' typ_to_doc s co

    and instantiee_to_doc' typ_to_doc s = function
        | (Symm _ | Trans _) as co -> PP.parens (coercion_to_doc' typ_to_doc s co)
        | co -> coercion_to_doc' typ_to_doc s co

    and base_co_to_doc' typ_to_doc s = function
        | (Trans _ | Comp _ | Inst _) as co ->
            PP.parens (coercion_to_doc' typ_to_doc s co)
        | co -> coercion_to_doc' typ_to_doc s co

    let coercion_to_doc = coercion_to_doc' to_doc
*)

    let coercion_to_doc = function
        | Refl t -> to_doc t

    let instantiate scope t = match force t with
        | Uv {quant = _; bound = root_bound} ->
            let rec locally_bound bound = match Bound.binder !bound with
                | Type bound' ->
                    bound' == root_bound || locally_bound bound
                | Scope _ -> false in

            let copies = Hashtbl.create 0 in

            let bound_copies = Bound.Hashtbl.create 0 in
            let new_binder = function
                | Type binder -> Bound.Hashtbl.get bound_copies binder
                | Scope _ -> None in

            let rec clone_term t =
                let t = force t in
                match Hashtbl.get copies t with
                | Some t' -> t'
                | None ->
                    let t' = match t with
                        | Uv {quant; bound} when locally_bound bound ->
                            let bound' = match !bound with
                                | Bot _ as bound -> bound
                                | Flex {level; binder; bound = bound_t} as bound ->
                                    let bound_t' = clone_term bound_t in
                                    if bound_t' == bound_t
                                    then bound
                                    else Flex {level; binder; bound = bound_t'}
                                | Rigid _ -> unreachable None in
                            let bound' = ref bound' in
                            Bound.Hashtbl.add bound_copies bound bound';
                            Uv {quant; bound = bound'}

                        | Uv _ -> t
                        | t -> map_children clone_term t in
                    Hashtbl.add copies t t';
                    t' in

            let root = clone_term t in

            let rec rebind t = match force t with
                | Uv {quant = _; bound} -> (match !bound with
                    | Bot {level; binder; kind} -> (match new_binder binder with
                        | Some binder ->
                            bound := Bot {level; binder = Type binder; kind}
                        | None -> ())

                    | Flex {level; binder; bound = bound_t} ->
                        iter rebind bound_t;

                        if t == root
                        then bound := Flex {level; binder = Scope scope; bound = bound_t}
                        else (match new_binder binder with
                            | Some binder ->
                                bound := Flex {level; binder = Type binder; bound = bound_t}
                            | None -> ())
                        
                    | Rigid _ -> unreachable None)
                | t -> iter rebind t in

            if root != t then rebind root;
            root

        | t -> t
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

