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

        module Hashtbl = TxRef.Hashtbl.Make (struct type t = bound end)
    end

    (* --- *)

    let fix binder f =
        let bound = ref (Rigid {level = -1; bindees = TxRef.Set.empty
            ; binder; (*tmp_*)typ = EmptyRow}) in
        bound := Rigid {level = Bound.level !bound; bindees = Bound.bindees !bound
            ; binder; typ = f bound};
        Uv {quant = ForAll; bound}

    (* --- *)

    let fresh binder kind = Uv {quant = ForAll; bound = Bound.fresh binder kind}

    (* OPTIMIZE: Path compression, ranking: *)
    let rec force = fun t -> match t with
        | Uv {quant = _; bound} -> (match !bound with
            | Rigid {level = _; bindees; binder = _; typ} when TxRef.Set.is_empty bindees ->
                force typ
            | _ -> t)
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
            | Flex {level; bindees; binder; typ} ->
                let typ' = f typ in
                if typ' == typ
                then t
                else Uv {quant; bound = ref (Flex {level; bindees; binder; typ = typ'})}
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
                                | Flex {level; bindees; binder; typ} as bound ->
                                    let typ' = clone_term typ in
                                    if typ' == typ
                                    then bound
                                    else Flex {level; bindees; binder; typ = typ'}
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
                | Uv {quant = _; bound} ->
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

