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
        | Uv of {quant : quantifier; name : Name.t; bound : bound txref}
        | Ov of {binder : scope; name : Name.t; kind : t}
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
        | Bot of {binder : binder; kind : kind}
        | Flex of {level :int; bindees : bound TxRef.Set.t; binder : binder; typ : t}
        | Rigid of {level :int; bindees : bound TxRef.Set.t; binder : binder; typ : t}

    and binder =
        | Scope of scope
        | Type of bound txref

    and scope =
        | Local of {level : int; bindees : bound TxRef.Set.t txref; parent : scope}
        | Global of bound TxRef.Set.t txref

    and coercion = Refl of t

    (* --- *)

    type typ = t

    module Hashtbl = CCHashtbl.Make (struct
        type t = typ

        let equal = (==)
        let hash = Hashtbl.hash
    end)

    module HashSet = CCHashSet.Make (struct
        type t = typ

        let equal = (==)
        let hash = Stdlib.Hashtbl.hash
    end)

    (* --- *)

    module Scope = struct
        type t = scope

        let level = function
            | Local {level; _} -> level
            | Global _ -> 0

        let add_bindee bindee (Local {bindees; _} | Global bindees) =
            bindees := TxRef.Set.add bindee !bindees

        let remove_bindee bindee (Local {bindees; _} | Global bindees) =
            bindees := TxRef.Set.remove bindee !bindees
    end

    module Binder = struct
        type t = binder

        let level = function
            | Type t -> (match !t with
                | Bot _ -> unreachable None
                | Flex {level; _} | Rigid {level; _} -> assert (level > 0); level)
            | Scope scope -> Scope.level scope

        let add_bindee bindee bref = match bref with
            | Type t -> t := (match !t with
                | Bot _ -> unreachable None
                | Flex {level; bindees; binder; typ} ->
                    Flex {level; bindees = TxRef.Set.add bindee bindees; binder; typ}
                | Rigid {level; bindees; binder; typ} ->
                    Rigid {level; bindees = TxRef.Set.add bindee bindees; binder; typ})
            | Scope scope -> Scope.add_bindee bindee scope

        let remove_bindee bindee bref = match bref with
            | Type t -> t := (match !t with
                | Bot _ -> unreachable None
                | Flex {level; bindees; binder; typ} ->
                    Flex {level; bindees = TxRef.Set.remove bindee bindees; binder; typ}
                | Rigid {level; bindees; binder; typ} ->
                    Rigid {level; bindees = TxRef.Set.remove bindee bindees; binder; typ})
            | Scope scope -> Scope.remove_bindee bindee scope

    end

    module Bound = struct
        type t = bound

        let fresh binder kind =
            let bref = ref (Bot {binder; kind}) in
            Binder.add_bindee bref binder;
            bref

        let binder = function
            | Bot {binder; _} -> binder
            | Flex {binder; _} -> binder
            | Rigid {binder; _} -> binder

        let level = function
            | Bot _ -> -1
            | Flex {level; _} | Rigid {level; _} -> level

        let bindees = function
            | Bot _ -> TxRef.Set.empty
            | Flex {bindees; _} | Rigid {bindees; _} -> bindees

        let with_level bound level = match bound with
            | Bot {binder; kind} -> Bot {binder; kind}
            | Flex {level = _; bindees; binder; typ} -> Flex {level; bindees; binder; typ}
            | Rigid {level = _; bindees; binder; typ} -> Rigid {level; bindees; binder; typ}

        let with_binder bound binder = match bound with
            | Bot {binder = _; kind} -> Bot {binder; kind}
            | Flex {level; bindees; binder = _; typ} -> Flex {level; bindees; binder; typ}
            | Rigid {level; bindees; binder = _; typ} -> Rigid {level; bindees; binder; typ}

        (* NOTE: Assumes Shallow MLF / HML: *)
        let is_locked bound = match binder bound with
            | Type binder -> (match !binder with
                | Bot _ | Flex _ -> false
                | Rigid _ -> true)
            | Scope _ -> false

        let bind (bref : t txref) (binder : Binder.t) =
            Binder.add_bindee bref binder;
            bref := with_binder !bref binder

        let rebind (bref : t txref) (binder' : Binder.t) =
            Binder.remove_bindee bref (binder !bref);
            bind bref binder'

        let graft_mono (bref : t txref) (typ : typ) = bref := (match !bref with
            | Bot {binder; kind = _} ->
                Rigid {level = -1; bindees = TxRef.Set.empty; binder; typ}
            | _ -> unreachable None)

        let set_level bref level = bref := with_level !bref level

        module Hashtbl = TxRef.Hashtbl.Make (struct type t = bound end)
        module HashSet = TxRef.HashSet.Make (struct type t = bound end)
    end

    (* --- *)

    let fix binder f =
        let bound = ref (Rigid {level = -1; bindees = TxRef.Set.empty
            ; binder; (*tmp_*)typ = EmptyRow}) in
        bound := Rigid {level = Bound.level !bound; bindees = Bound.bindees !bound
            ; binder; typ = f bound};
        Uv {quant = ForAll; name = Name.fresh (); bound}

    (* --- *)

    let fresh binder kind =
        Uv {quant = ForAll; name = Name.fresh (); bound = Bound.fresh binder kind}

    (* OPTIMIZE: Path compression, ranking: *)
    let rec force = fun t -> match t with
        | Uv {quant = _; name = _; bound} -> (match !bound with
            | Rigid {level = _; bindees; binder = _; typ} when TxRef.Set.is_empty bindees ->
                force typ
            | _ -> t)
        | Ov _ | Fn _ | App _ | Pi _ | Impli _
        | Record _ | With _ | EmptyRow | Proxy _ | Prim _
        | Tuple _ | PromotedTuple _ | PromotedArray _ -> t

    let iter f = function
        | Uv {quant = _; name = _; bound} -> (match !bound with
            | Bot _ -> ()
            | Flex {level = _; bindees = _; binder = _; typ}
            | Rigid {level = _; bindees = _; binder = _; typ} -> f typ)
        | Fn {param; body} -> f param; f body
        | App (callee, arg) -> f callee; f arg
        | Pi {domain; eff; codomain} -> f domain; f eff; f codomain
        | Impli {domain; codomain} -> f domain; f codomain
        | Record row -> f row
        | With {base; label = _; field} -> f base; f field
        | Tuple typs | PromotedTuple typs | PromotedArray typs -> Vector.iter f typs
        | Proxy typ -> f typ
        | EmptyRow | Prim _ | Ov _ -> ()

    let map_children =
        let all_eq xs ys =
            Stream.from (Source.zip_with (==) (Vector.to_source xs) (Vector.to_source ys))
            |> Stream.into (Sink.all ~where: Fun.id) in

        fun f t -> match force t with
        | Uv {quant; name; bound} -> (match !bound with
            | Bot _ -> t
            | Flex {level; bindees; binder; typ} ->
                let typ' = f typ in
                if typ' == typ
                then t
                else Uv {quant; name; bound = ref (Flex {level; bindees; binder; typ = typ'})}
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

    let flag_to_string = function
        | SFlex -> ">="
        | SRigid -> "="

    let quant_prec = 0
    let arrow_prec = 1
    let with_prec = 2
    let app_prec = 3

    let show_parens should_show doc = if should_show then PPrint.parens doc else doc

    let syn_to_doc syn =
        let open PPrint in

        let rec sbound_to_doc (name, flag, bound) =
            PPrint.(parens (infix 4 1 (string (flag_to_string flag))
                (Name.to_doc name) (to_doc 0 bound)))

        and sbounds_to_doc bounds =
            separate_map (break 1) sbound_to_doc (Vector1.to_list bounds)

        and to_doc prec = function
            | SExists (bounds, body) ->
                prefix 4 1 
                    (string "exists" ^^ blank 1 ^^ sbounds_to_doc bounds)
                    (to_doc quant_prec body)
                |> show_parens (prec > quant_prec)
            | SForAll (bounds, body) ->
                prefix 4 1 
                    (string "forall" ^^ blank 1 ^^ sbounds_to_doc bounds)
                    (to_doc quant_prec body)
                |> show_parens (prec > quant_prec)
            | SPi {domain; eff = _; codomain} ->
                infix 4 1 (string "->") (to_doc (arrow_prec + 1) domain)
                    (to_doc arrow_prec codomain)
            | SApp {callee; arg} ->
                prefix 4 1 (to_doc app_prec callee) (to_doc (app_prec + 1) arg)
            | SVar name -> Name.to_doc name
            | SBot -> qmark ^^ underscore
            | SRecord row -> braces (to_doc 0 row)
            | SWith {base; label; field} ->
                infix 4 1
                    (string "with"
                        ^^ blank 1 ^^ string (Option.get (Name.basename label))
                        ^^ blank 1 ^^ equals)
                    (to_doc with_prec base) (to_doc (with_prec + 1) field)
            | SEmptyRow -> parens bar
            | STuple typs -> surround_separate_map 4 1 (parens colon)
                (lparen ^^ colon) (comma ^^ break 1) rparen
                (to_doc 0) (Vector.to_list typs)
            | SPromotedTuple typs -> surround_separate_map 4 1 (parens empty)
                lparen (comma ^^ break 1) rparen
                (to_doc 0) (Vector.to_list typs)
            | SPromotedArray typs -> surround_separate_map 4 1 (brackets empty)
                lbracket (comma ^^ break 1) rbracket
                (to_doc 0) (Vector.to_list typs)
            | SProxy carrie -> brackets (prefix 4 1 equals (to_doc 0 carrie))
            | SPrim p -> string "__" ^^ Prim.to_doc p
            | _ -> todo None ~msg: "syn_to_doc" in

        to_doc 0 syn

    let to_syn ctx t =
        let existentials = Bound.Hashtbl.create 0 in
        let universals = Bound.Hashtbl.create 0 in

        let visited = HashSet.create 0 in
        let visited_bounds = Bound.HashSet.create 0 in

        let rec analyze t =
            let t = force t in
            if not (HashSet.mem visited t) then begin
                HashSet.insert visited t;
                (match t with
                | Uv {quant = _; name = _; bound} ->
                    Bound.HashSet.insert visited_bounds bound
                | _ -> ());

                iter analyze t;

                match t with
                | Uv {quant; name = _; bound} -> (match Bound.binder !bound with
                    | Type binder when Bound.HashSet.mem visited_bounds binder ->
                        let bindees = match quant with
                            | Exists -> existentials
                            | ForAll -> universals in
                        Bound.Hashtbl.update bindees ~k: binder ~f: (fun _ -> function
                            | Some bs as v -> CCVector.push bs t; v
                            | None -> Some (CCVector.of_list [t]))
                    | Type _ | Scope _ -> Bound.HashSet.insert ctx bound)
                | _ -> ()
            end in
        analyze t;

        let rec to_syn t =
            let t = force t in

            let (existentials, universals) = match t with
                | Uv {quant = _; name = _; bound} ->
                    let existentials = match Bound.Hashtbl.get existentials bound with
                        | Some existentials -> existentials
                        | None -> CCVector.create () in
                    let universals = match Bound.Hashtbl.get universals bound with
                        | Some universals -> universals
                        | None -> CCVector.create () in
                    ( Vector.build existentials |> Vector.map bindee_to_syn
                    , Vector.build universals |> Vector.map bindee_to_syn )
                | _ -> (Vector.empty, Vector.empty) in

            let body = match t with
                | Uv {quant = _; name; bound} -> (match !bound with
                    | Bot _ | Flex _ -> SVar name
                    | Rigid {level = _; bindees = _; binder = _; typ} -> to_syn typ)
                | Ov {binder = _; name; kind = _} -> SVar name
                | Fn {param; body} ->
                    SFn {param = (Name.fresh (), to_syn param); body = to_syn body}
                | App (callee, arg) ->
                    SApp {callee = to_syn callee; arg = to_syn arg}
                | Pi {domain; eff; codomain} ->
                    SPi {domain = to_syn domain; eff = to_syn eff
                        ; codomain = to_syn codomain}
                | Impli {domain; codomain} ->
                    SImpli {domain = to_syn domain; codomain = to_syn codomain}
                | Record row -> SRecord (to_syn row)
                | With { base; label; field} ->
                    SWith {base = to_syn base; label; field = to_syn field}
                | EmptyRow -> SEmptyRow
                | Tuple typs -> STuple (Vector.map to_syn typs)
                | PromotedTuple typs -> SPromotedTuple (Vector.map to_syn typs)
                | PromotedArray typs -> SPromotedArray (Vector.map to_syn typs)
                | Proxy typ -> SProxy (to_syn typ)
                | Prim p -> SPrim p in

            let syn = match Vector1.of_vector universals with
                | Some universals -> SForAll (universals, body)
                | None -> body in
            match Vector1.of_vector existentials with
            | Some existentials -> SExists (existentials, body)
            | None -> syn

        and bindee_to_syn = function
            | Uv {quant = _; name; bound} -> (match !bound with
                | Bot {binder = _; kind = _} -> (name, SFlex, SBot)
                | Flex {level = _; bindees = _; binder = _; typ} ->
                    (name, SFlex, to_syn typ)
                | Rigid {level = _; bindees = _; binder = _; typ} ->
                    (name, SRigid, to_syn typ))
            | _ -> unreachable None in

        to_syn (force t)

    let to_doc t =
        let ctx = Bound.HashSet.create 0 in
        let syn = to_syn ctx t in
        (*PPrint.(match Hashtbl.to_list ctx with
            | (_ :: _) as ctx ->
                infix 4 1 (string "in") (syn_to_doc syn)
                    (separate_map (comma ^^ blank 1) (fun (t, (name, syn)) ->
                        match t with
                        | Uv {quant = _; name = _; bound} -> (match !bound with
                            | Bot {binder = _; kind} ->
                                infix 4 1 colon (Name.to_doc name) (to_doc kind)
                            | Flex _ ->
                                infix 4 1 (string ">=") (Name.to_doc name) (syn_to_doc syn)
                            | Rigid _ ->
                                infix 4 1 equals (Name.to_doc name) (syn_to_doc syn))
                        | _ -> unreachable None ~msg: "Type.to_doc"
                    ) ctx)
            | [] ->*) syn_to_doc syn(* )*)

    let kind_to_doc = to_doc

    (* --- *)

    let coercion_to_doc = function
        | Refl t -> to_doc t

    let instantiate scope t = match force t with
        | Uv {quant = _; name = _; bound = root_bound} ->
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
                        | Uv {quant; name; bound} when locally_bound bound ->
                            let bound' = match !bound with
                                | Bot _ as bound -> bound
                                | Flex {level; bindees; binder; typ} as bound ->
                                    let typ' = clone_term typ in
                                    if typ' == typ
                                    then bound
                                    else Flex {level; bindees; binder; typ = typ'}
                                | Rigid _ -> unreachable None in
                            let bound' = ref bound' in
                            Bound.Hashtbl.add bound_copies bound bound';
                            Uv {quant; name; bound = bound'}

                        | Uv _ -> t
                        | t -> map_children clone_term t in
                    Hashtbl.add copies t t';
                    t' in

            let root = clone_term t in

            let rec rebind t = match force t with
                | Uv {quant = _; name = _; bound} ->
                    (match !bound with
                    | Bot _ -> ()

                    | Flex {level; bindees = _; binder = _; typ} ->
                        iter rebind typ;

                        if t == root then begin
                            let bindees = Bound.bindees !bound in
                            bound := Flex {level; bindees; binder = Scope scope; typ};
                        end
                        
                    | Rigid {level; bindees = _; binder = _; typ} ->
                        iter rebind typ;

                        if t == root then begin
                            let bindees = Bound.bindees !bound in
                            bound := Rigid {level; bindees; binder = Scope scope; typ}
                        end);
                    (match new_binder (Bound.binder !bound) with
                    | Some binder -> Bound.rebind bound (Type binder)
                    | None -> ())
                | t -> iter rebind t in

            if root != t then rebind root;
            root

        | t -> t

    let reabstract scope t = match force t with
        | Uv {quant = _; name = _; bound = root_bound} ->
            let copies = Hashtbl.create 0 in

            let bound_copies = Bound.Hashtbl.create 0 in
            let new_binder = function
                | Type binder ->
                    if TxRef.equal binder root_bound
                    then Some (Scope scope)
                    else Bound.Hashtbl.get bound_copies binder
                        |> Option.map (fun binder -> Type binder)
                | Scope _ -> None in

            let rec clone_term t =
                let t = force t in
                match Hashtbl.get copies t with
                | Some t' -> t'
                | None ->
                    let t' = map_children clone_term t in
                    Hashtbl.add copies t t';
                    t' in

            let root = clone_term t in

            let rec rebind t =
                let t = force t in

                iter rebind t;

                match force t with
                | Uv {quant = _; name = _; bound} ->
                    (match new_binder (Bound.binder !bound) with
                    | Some binder -> Bound.rebind bound binder
                    | None -> ())
                | _ -> () in

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

