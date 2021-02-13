open Streaming

open Asserts

type 'a txref = 'a TxRef.t

let ref = TxRef.ref
let (!) = TxRef.(!)
let (:=) = TxRef.(:=)

module rec Uv : (FcTypeSigs.UV
    with type typ = Typ.t
    with type kind = Typ.kind
    with type ov = Ov.t
) = struct
    type typ = Typ.t
    type kind = Typ.kind
    type ov = Ov.t

    type t =
        { name : Name.t
        ; quant : quantifier
        ; binder : binder txref
        ; bindees : t Vector.t txref
        ; level : int txref
        ; bound : bound txref }

    and quantifier = ForAll | Exists

    and bound =
        | Bot of kind
        | Flex of typ
        | Rigid of typ

    and binder =
        | Scope of scope
        | Type of t

    and scope =
        | Local of {level : int; parent : scope
            ; bindees : t Vector.t txref; ovs : ov Vector.t txref}
        | Global of {bindees : t Vector.t txref; ovs : ov Vector.t txref}

    let hash uv = Name.hash uv.name
    let equal = (==)

    (* NOTE: Assumes Shallow MLF / HML: *)
    let is_locked uv = match !(uv.binder) with
        | Type binder -> (match !(binder.bound) with
            | Bot _ | Flex _ -> false
            | Rigid _ -> true)
        | Scope _ -> false

    let graft_mono uv typ = uv.bound := Rigid typ

    module Scope = struct
        type t = scope

        let level = function
            | Local {level; _} -> level
            | Global _ -> 0

        let bindees (Local {bindees; _} | Global {bindees; _}) = bindees
        let ovs (Local {ovs; _} | Global {ovs; _}) = ovs

        let add_bindee scope bindee =
            let bindees = bindees scope in
            if not (Vector.exists ((==) bindee) !bindees)
            then bindees := Vector.push !bindees bindee

        let remove_bindee scope bindee =
            let bindees = bindees scope in
            bindees := Vector.filter ((!=) bindee) !bindees

        let fresh_ov scope kind =
            let ovs = ovs scope in
            let ov = {Ov.name = Name.fresh (); binder = scope; kind} in
            ovs := Vector.push !ovs ov;
            ov
    end

    module Binder = struct
        type t = binder

        let level = function
            | Type t -> !(t.level)
            | Scope scope -> Scope.level scope

        let add_bindee binder bindee = match binder with
            | Type binder ->
                let bindees = binder.bindees in
                if not (Vector.exists ((==) bindee) !bindees)
                then bindees := Vector.push !bindees bindee
            | Scope scope -> Scope.add_bindee scope bindee

        let remove_bindee binder bindee = match binder with
            | Type binder ->
                let bindees = binder.bindees in
                bindees := Vector.filter ((!=) bindee) !bindees
            | Scope scope -> Scope.remove_bindee scope bindee
    end

    let fresh quant binder kind =
        let uv = {name = Name.fresh (); quant; binder = ref binder
            ; bindees = ref Vector.empty; level = ref (-1)
            ; bound = ref (Bot kind)} in
        Binder.add_bindee binder uv;
        uv

    let bind uv binder =
        Binder.add_bindee binder uv;
        uv.binder := binder

    let rebind uv binder' =
        Binder.remove_bindee !(uv.binder) uv;
        bind uv binder'

    let map_bound f ({name = _; quant; binder; bindees = _; level; bound} as uv) =
        match !bound with
        | Bot _ -> uv
        | Flex typ ->
            let typ' = f typ in
            if typ' == typ
            then uv
            else begin
                let uv = {name = Name.fresh (); quant; binder
                    ; bindees = ref Vector.empty; level = ref !level
                    ; bound = ref (Flex (f typ))} in
                Binder.add_bindee !binder uv;
                uv
            end

        | Rigid typ ->
            let typ' = f typ in
            if typ' == typ
            then uv
            else begin
                let uv = {name = Name.fresh (); quant; binder
                    ; bindees = ref Vector.empty; level = ref !level
                    ; bound = ref (Rigid (f typ))} in
                Binder.add_bindee !binder uv;
                uv
            end

    type uv = t
    module Key = struct
        type t = uv

        let hash = hash
        let equal = equal
    end

    module Hashtbl = CCHashtbl.Make (Key)
    module HashSet = CCHashSet.Make (Key)
end

and Ov : (FcTypeSigs.OV
    with type kind = Typ.kind
    with type scope = Uv.scope
) = struct
    type kind = Typ.kind
    type scope = Uv.scope

    type t = {name : Name.t; binder : scope; kind : kind}
end

and Typ : (FcTypeSigs.TYPE
    with type uv = Uv.t
    with type bound = Uv.bound
    with type binder = Uv.binder
    with type scope = Uv.scope
    with type ov = Ov.t
) = struct
    type uv = Uv.t
    type bound = Uv.bound
    type binder = Uv.binder
    type scope = Uv.scope
    type ov = Ov.t

    type t =
        | Uv of uv
        | Ov of ov
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

    let fix binder f =
        let root = Uv.fresh ForAll binder (*tmp:*)EmptyRow in
        Uv.graft_mono root (f root);
        Uv root

    (* --- *)

    (* OPTIMIZE: Path compression, ranking: *)
    let rec force t = match t with
        | Uv uv -> (match !(uv.bound) with
            | Rigid typ when Vector.length !(uv.bindees) = 0 ->
                force typ
            | _ -> t)
        | Ov _ | Fn _ | App _ | Pi _ | Impli _
        | Record _ | With _ | EmptyRow | Proxy _ | Prim _
        | Tuple _ | PromotedTuple _ | PromotedArray _ -> t

    let iter f = function
        | Uv uv -> (match !(uv.bound) with
            | Bot _ -> ()
            | Flex typ | Rigid typ -> f typ)
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

        fun f t ->
            let t = force t in
            match force t with
            | Uv uv ->
                let uv' = Uv.map_bound f uv in
                if uv' == uv then t else Uv uv'

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

    let postwalk_rebinding f t =
        let copies = Hashtbl.create 0 in
        let binder_copies = Uv.Hashtbl.create 0 in

        let rec clone_term t =
            let t = force t in
            match Hashtbl.get copies t with
            | Some t' -> t'
            | None ->
                let t' = f (map_children clone_term t) in
                (match (t, t') with
                | (Uv uv, Uv uv') ->
                    if not (Uv.equal uv' uv)
                    then Uv.Hashtbl.add binder_copies uv uv'
                | _ -> ());
                Hashtbl.add copies t t';
                t' in
        let t' = clone_term t in

        if t' != t then begin
            let rec rebind t =
                let t = force t in

                iter rebind t;

                match t with
                | Uv uv -> (match !(uv.binder) with
                    | Type binder -> (match Uv.Hashtbl.get binder_copies binder with
                        | Some binder' -> Uv.rebind uv (Type binder')
                        | None -> ())
                    | Scope _ -> ())
                | _ -> () in
            rebind t'
        end;

        t'

    (* --- *)

    type flag = SBot | SFlex | SRigid

    type syn =
        | SExists of squant_param Vector1.t * syn
        | SForAll of squant_param Vector1.t * syn
        | SFn of {param : stypedef; body : syn} (* type lambda *)
        | SApp of {callee : syn; arg : syn}
        | SVar of Name.t
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
        | SBot -> ":"
        | SFlex -> ">="
        | SRigid -> "="

    let quant_prec = 0
    let arrow_prec = 1
    let with_prec = 2
    let app_prec = 3

    let show_parens should_show doc = if should_show then PPrint.parens doc else doc

    let rec syn_to_doc syn =
        let open PPrint in

        let rec to_doc prec = function
            | SExists (bounds, body) ->
                prefix 4 1 
                    (string "exists" ^^ blank 1 ^^ sbounds_to_doc bounds)
                    (dot ^^ blank 1 ^^ to_doc quant_prec body)
                |> show_parens (prec > quant_prec)
            | SForAll (bounds, body) ->
                prefix 4 1 
                    (string "forall" ^^ blank 1 ^^ sbounds_to_doc bounds)
                    (dot ^^ blank 1 ^^ to_doc quant_prec body)
                |> show_parens (prec > quant_prec)
            | SPi {domain; eff = _; codomain} ->
                infix 4 1 (string "->") (to_doc (arrow_prec + 1) domain)
                    (to_doc arrow_prec codomain)
            | SApp {callee; arg} ->
                prefix 4 1 (to_doc app_prec callee) (to_doc (app_prec + 1) arg)
            | SVar name -> Name.to_doc name
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

    and sbound_to_doc (name, flag, bound) =
        PPrint.(parens (infix 4 1 (string (flag_to_string flag))
            (Name.to_doc name) (syn_to_doc bound)))

    and sbounds_to_doc bounds =
        PPrint.(separate_map (break 1) sbound_to_doc (Vector1.to_list bounds))

    let to_syn ctx t =
        let existentials = Uv.Hashtbl.create 0 in
        let universals = Uv.Hashtbl.create 0 in

        let visited = HashSet.create 0 in
        let visited_bounds = Uv.HashSet.create 0 in

        let rec analyze t =
            let t = force t in
            if not (HashSet.mem visited t) then begin
                HashSet.insert visited t;
                (match t with
                | Uv uv -> Uv.HashSet.insert visited_bounds uv
                | _ -> ());

                iter analyze t;

                match t with
                | Uv ({name = _; quant; binder; bindees = _; level = _; bound = _} as uv) ->
                    (match !binder with
                    | Type binder when Uv.HashSet.mem visited_bounds binder ->
                        let bindees = match quant with
                            | Exists -> existentials
                            | ForAll -> universals in
                        Uv.Hashtbl.update bindees ~k: binder ~f: (fun _ -> function
                            | Some bs as v -> CCVector.push bs t; v
                            | None -> Some (CCVector.of_list [t]))
                    | Type _ | Scope _ ->
                        Uv.Hashtbl.add ctx uv (bindee_to_syn t)) (* HACK *)
                | _ -> ()
            end

        and to_syn t =
            let t = force t in

            let (existentials, universals) = match t with
                | Uv uv ->
                    let existentials = match Uv.Hashtbl.get existentials uv with
                        | Some existentials -> existentials
                        | None -> CCVector.create () in
                    let universals = match Uv.Hashtbl.get universals uv with
                        | Some universals -> universals
                        | None -> CCVector.create () in
                    ( Vector.build existentials |> Vector.map bindee_to_syn
                    , Vector.build universals |> Vector.map bindee_to_syn )
                | _ -> (Vector.empty, Vector.empty) in

            let body = match t with
                | Uv uv -> (match !(uv.bound) with
                    | Bot _ | Flex _ -> SVar uv.name
                    | Rigid typ -> to_syn typ)
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
            | Uv {name; quant = _; binder = _; bindees = _; level = _; bound} -> (match !bound with
                | Bot kind -> (name, SBot, to_syn kind)
                | Flex typ -> (name, SFlex, to_syn typ)
                | Rigid typ -> (name, SRigid, to_syn typ))
            | _ -> unreachable None in

        analyze t;
        to_syn (force t)

    let to_doc t =
        let ctx = Uv.Hashtbl.create 0 in
        let syn = to_syn ctx t in
        PPrint.(match Uv.Hashtbl.to_list ctx with
            | (_ :: _) as ctx ->
                infix 4 1 (string "in") (syn_to_doc syn)
                    (separate_map (comma ^^ blank 1)
                        (fun (_, sbound) -> sbound_to_doc sbound)
                        ctx)
            | [] -> syn_to_doc syn )

    let kind_to_doc = to_doc

    (* --- *)

    let coercion_to_doc = function
        | Refl t -> to_doc t

    let forall_scope_ovs ~binder scope t =
        let binder = Uv.Scope binder in
        fix binder (fun root_bound ->
            t |> postwalk_rebinding (fun t -> match t with
                | Ov {binder; name = _; kind} when binder == scope ->
                    Uv (Uv.fresh ForAll (Type root_bound) kind)
                | t -> t
            )
        )

    let instantiate scope t =
        let t = force t in
        match t with
        | Uv root ->
            let rec locally_bound = function
                | Uv.Type binder ->
                    Uv.equal binder root
                    || locally_bound !(binder.binder)
                | Scope _ -> false in

            let t = t |> postwalk_rebinding (fun t -> match t with
                | Uv {name = _; quant = ForAll; binder; bindees = _; level = _; bound} ->
                    (match !bound with
                    | Bot kind when locally_bound !binder ->
                        Uv (Uv.fresh ForAll !binder kind)
                    | _ -> t)
                | t -> t) in

            (match t with
            | Uv ({name = _; quant = _; binder = _; bindees = _; level = _; bound} as uv) ->
                (match !bound with
                | Bot _ -> ()
                | Flex typ | Rigid typ ->
                    bound := Flex typ;
                    Uv.rebind uv (Scope scope))
            | _ -> ());

            t
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

