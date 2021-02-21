open Streaming
open Asserts

module Sigs = ComplexFcSigs

type 'a txref = 'a TxRef.t
let ref = TxRef.ref
let (!) = TxRef.(!)
let (:=) = TxRef.(:=)

module rec Types : Sigs.TYPES with type Coercer.expr = Term.Expr.t = struct
    module Expr = Term.Expr

    module Coercer : Sigs.COERCER with type expr = Expr.t = struct
        type expr = Expr.t

        type t = expr -> expr

        let id () = Fun.id

        let coercer = Fun.id

        let apply f (expr : expr) = match expr.term with
            | Use _ | Const _ -> f expr
            | _ ->
                let {Expr.term = _; pos; typ} = expr in
                let var = Expr.fresh_var typ in
                let body = f (Expr.at pos typ (Expr.use var)) in
                Expr.at pos typ
                    (Expr.let' (Vector.singleton (Term.Stmt.Def (pos, var, expr))) body)

        let apply_opt f expr = match f with
            | Some f -> apply f expr
            | None -> expr
    end

    module rec Uv : (Sigs.UV
        with type typ = Typ.t
        with type kind = Typ.kind
        with type ov = Ov.t
        with type coercer = Coercer.t
    ) = struct
        type typ = Typ.t
        type kind = Typ.kind
        type ov = Ov.t
        type coercer = Coercer.t

        type t =
            { name : Name.t
            ; quant : quantifier
            ; binder : binder txref
            ; bindees : t Vector.t txref
            ; level : int txref
            ; bound : bound txref }

        and quantifier = ForAll | Exists

        and bound =
            | Bot of {kind : kind; coerce : coercer option}
            | Flex of {typ : typ; coerce : coercer option}
            | Rigid of {typ : typ; coerce : coercer option}

        and binder =
            | Scope of scope
            | Type of t

        and scope =
            | Local of {level : int; bindees : t Vector.t txref; ovs : ov Vector.t txref}
            | Global of {bindees : t Vector.t txref; ovs : ov Vector.t txref}

        let hash uv = Name.hash uv.name
        let equal = (==)

        (* NOTE: Assumes Shallow MLF / HML: *)
        let is_locked uv = match !(uv.binder) with
            | Type binder -> (match !(binder.bound) with
                | Bot _ | Flex _ -> false
                | Rigid _ -> true)
            | Scope _ -> false

        let graft_mono uv typ coerce = uv.bound := Rigid {typ; coerce}

        module Scop = struct
            type t = scope

            let level = function
                | Local {level; _} -> level
                | Global _ -> 0

            let bindees (Local {bindees; _} | Global {bindees; _}) = bindees
            let ovs_mut (Local {ovs; _} | Global {ovs; _}) = ovs
            let ovs scope = !(ovs_mut scope)

            let add_bindee scope bindee =
                let bindees = bindees scope in
                if not (Vector.exists ((==) bindee) !bindees)
                then bindees := Vector.push !bindees bindee

            let remove_bindee scope bindee =
                let bindees = bindees scope in
                bindees := Vector.filter ((!=) bindee) !bindees

            let fresh_ov scope kind =
                let ovs = ovs_mut scope in
                let ov = {Ov.name = Name.fresh (); binder = scope; kind} in
                ovs := Vector.push !ovs ov;
                ov
        end

        module Binder = struct
            type t = binder

            let level = function
                | Type t -> !(t.level)
                | Scope scope -> Scop.level scope

            let add_bindee binder bindee = match binder with
                | Type binder ->
                    let bindees = binder.bindees in
                    if not (Vector.exists ((==) bindee) !bindees)
                    then bindees := Vector.push !bindees bindee
                | Scope scope -> Scop.add_bindee scope bindee

            let remove_bindee binder bindee = match binder with
                | Type binder ->
                    let bindees = binder.bindees in
                    bindees := Vector.filter ((!=) bindee) !bindees
                | Scope scope -> Scop.remove_bindee scope bindee
        end

        let fresh quant binder kind =
            let uv = {name = Name.fresh (); quant; binder = ref binder
                ; bindees = ref Vector.empty; level = ref (-1)
                ; bound = ref (Bot {kind; coerce = None})} in
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
            | Flex {typ; coerce} ->
                let typ' = f typ in
                if typ' == typ
                then uv
                else begin
                    let uv = {name = Name.fresh (); quant; binder
                        ; bindees = ref Vector.empty; level = ref !level
                        ; bound = ref (Flex {typ = f typ; coerce})} in
                    Binder.add_bindee !binder uv;
                    uv
                end

            | Rigid {typ; coerce} ->
                let typ' = f typ in
                if typ' == typ
                then uv
                else begin
                    let uv = {name = Name.fresh (); quant; binder
                        ; bindees = ref Vector.empty; level = ref !level
                        ; bound = ref (Rigid {typ = f typ; coerce})} in
                    Binder.add_bindee !binder uv;
                    uv
                end

        module Scope = struct
            include Scop

            let exit parent scope =
                let level = level scope in
                !(bindees scope) |> Vector.iter (fun bindee -> match !(bindee.bound) with
                    | Bot {kind; _} ->
                        if Typ.ov_tied level kind
                        then () (* TODO: assign some default? *)
                        else rebind bindee (Scope parent)
                    | Flex {typ; coerce} ->
                        if Typ.ov_tied level typ
                        then bindee.bound := Rigid {typ; coerce}
                        else rebind bindee (Scope parent)
                    | Rigid _ -> ())
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

    and Ov : (Sigs.OV
        with type kind = Typ.kind
        with type scope = Uv.scope
    ) = struct
        type kind = Typ.kind
        type scope = Uv.scope

        type t = {name : Name.t; binder : scope; kind : kind}

        let equal = (==)
    end

    and Typ : (Sigs.TYPE
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
            Uv.graft_mono root (f root) None;
            Uv root

        (* --- *)

        (* OPTIMIZE: Path compression, ranking: *)
        let rec force t = match t with
            | Uv uv -> (match !(uv.bound) with
                | Rigid {typ; coerce = _} when Vector.length !(uv.bindees) = 0 ->
                    force typ
                | _ -> t)
            | Ov _ | Fn _ | App _ | Pi _ | Impli _
            | Record _ | With _ | EmptyRow | Proxy _ | Prim _
            | Tuple _ | PromotedTuple _ | PromotedArray _ -> t

        let iter f = function
            | Uv uv -> (match !(uv.bound) with
                | Bot _ -> ()
                | Flex {typ; coerce = _} | Rigid {typ; coerce = _} -> f typ)
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
                match t with
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
                    | Uv uv -> (match !(uv.binder) with
                        | Type binder when Uv.HashSet.mem visited_bounds binder ->
                            let bindees = match uv.quant with
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
                        | Rigid {typ; coerce = _} -> to_syn typ)
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
                | Uv {name; bound; _} -> (match !bound with
                    | Bot {kind; _} -> (name, SBot, to_syn kind)
                    | Flex {typ; _} -> (name, SFlex, to_syn typ)
                    | Rigid {typ; _} -> (name, SRigid, to_syn typ))
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

        let coercion_to_doc = function
            | Refl t -> to_doc t

        (* --- *)

        let ov_tied level t =
            let rec tied = function
            | Ov {binder; _} -> Uv.Scope.level binder = level (* the actual work *)

            | Uv uv -> (match !(uv.bound) with
                | Bot {kind; _} -> tied kind
                | Flex {typ; _} | Rigid {typ; _} -> tied typ)
            | Pi {domain; eff; codomain} -> tied domain || tied eff || tied codomain
            | Impli {domain; codomain} -> tied domain || tied codomain
            | Fn {param; body} -> tied param || tied body
            | App (callee, arg) -> tied callee || tied arg
            | Record row -> tied row
            | With {base; label = _; field} -> tied base || tied field
            | EmptyRow -> false
            | Tuple typs | PromotedTuple typs | PromotedArray typs -> Vector.exists tied typs
            | Proxy carrie -> tied carrie
            | Prim _ -> false in

            tied t

        let forall_scope_ovs ~binder scope t =
            let binder = Uv.Scope binder in
            fix binder (fun root_bound ->
                t |> postwalk_rebinding (fun t -> match t with
                    | Ov {binder; name = _; kind} when binder == scope ->
                        Uv (Uv.fresh ForAll (Type root_bound) kind)
                    | t -> t
                )
            )

        let exists_scope_ovs ~binder scope t =
            let binder = Uv.Scope binder in
            fix binder (fun root_bound ->
                t |> postwalk_rebinding (fun t -> match t with
                    | Ov {binder; name = _; kind} when binder == scope ->
                        Uv (Uv.fresh Exists (Type root_bound) kind)
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
                    | Uv {quant = ForAll; binder; bound; _} ->
                        (match !bound with
                        | Bot {kind; _} when locally_bound !binder ->
                            Uv (Uv.fresh ForAll !binder kind)
                        | _ -> t)
                    | t -> t) in

                (match t with
                | Uv ({quant = ForAll; bound; _} as uv) ->
                    (match !bound with
                    | Bot _ -> ()
                    | Flex {typ; coerce} | Rigid {typ; coerce} ->
                        bound := Flex {typ; coerce};
                        Uv.rebind uv (Scope scope))
                | _ -> ());

                t
            | t -> t
    end
end

and Term : ComplexFcSigs.TERM
    with type Expr.typ = Types.Typ.t
    with type Expr.coercion = Types.Typ.coercion
    with type Expr.t_scope = Types.Uv.Scope.t
    with type Expr.coercer = Types.Coercer.t
= struct
    module Uv = Types.Uv
    module Ov = Types.Ov

    module rec Expr : sig
        include ComplexFcSigs.EXPR
            with type typ = Types.Typ.t
            with type coercion = Types.Typ.coercion
            with type t_scope = Types.Uv.Scope.t
            with type def = Stmt.def
            with type stmt = Stmt.t
            with type coercer = Types.Coercer.t

        val def_to_doc : var -> PPrint.document
    end = struct
        module Type = Types.Typ

        type typ = Types.Typ.t
        type coercion = Types.Typ.coercion
        type t_scope = Types.Uv.Scope.t
        type def = Stmt.def
        type stmt = Stmt.t
        type coercer = Types.Coercer.t

        and var = {name : Name.t; vtyp : typ}

        and typedef = Name.t * typ

        and t =
            { term : t'
            ; typ : typ
            ; pos : Util.span }

        and t' =
            | Use of var
            | Fn of {t_scope : t_scope; param : var; body : t}
            | App of {callee : t; universals : typ Vector.t; arg : t}
            | PrimApp of {op : Primop.t; universals : typ Vector.t; arg : t}
            | PrimBranch of {op : Branchop.t; universals : typ Vector.t; arg : t
                ; clauses : prim_clause Vector.t}

            | Let of {defs : stmt Vector1.t; body : t}
            | Letrec of {defs : def Vector1.t; body : t}
            | Match of {matchee : t; clauses : clause Vector.t}

            (*| Axiom of { axioms : (Name.t * Type.kind Vector.t * typ * typ) Vector1.t
                ; body : t }*)
            | Cast of {castee : t; coercion : coercion}
            | Convert of {coerce : coercer option txref; arg : t}

            | Record of (Name.t * t) Vector.t
            | Where of {base : t; fields : (Name.t * t) Vector1.t}
            | With of {base : t; label : Name.t; field : t}
            | Select of {selectee : t; label : Name.t}

            | Tuple of t Vector.t
            | Focus of {focusee : t; index : int}

            | Proxy of typ

            | Const of Const.t

        and clause = {pat : pat; body : t}
        and prim_clause = {res : var option; prim_body : t}

        and pat = {pterm: pat'; ptyp : typ; ppos : Util.span}
        and pat' =
            | TupleP of pat Vector.t
            | ProxyP of typ
            | ConstP of Const.t
            | VarP of var
            | WildP of Name.t

        let prec_parens show_parens doc = if show_parens then PPrint.parens doc else doc

        let var_to_doc (var : var) = Name.to_doc var.name

        let def_to_doc (var : var) =
            PPrint.(infix 4 1 colon (var_to_doc var) (Type.to_doc var.vtyp))

        let cast_prec = 1
        let app_prec = 2
        let dot_prec = 3

        let rec to_doc (expr : t) =
            let open PPrint in

            let ov_to_doc {Ov.name; binder = _; kind} =
                infix 4 1 colon (Name.to_doc name) (Type.kind_to_doc kind) in

            let rec to_doc prec expr = match expr.term with
                | Tuple exprs ->
                    surround_separate_map 4 0 (parens empty)
                        lparen (comma ^^ break 1) rparen
                        (to_doc 0) (Vector.to_list exprs)
                | Focus {focusee; index} ->
                    prefix 4 1 (to_doc dot_prec focusee) (dot ^^ string (Int.to_string index))
                | Fn {t_scope; param; body} ->
                    string "fun"
                    ^^ surround_separate_map 4 0 empty
                        (blank 1 ^^ langle) (comma ^^ break 1) rangle
                        ov_to_doc (Vector.to_list (Uv.Scope.ovs t_scope))
                    ^^ blank 1 ^^ parens (def_to_doc param) ^^ blank 1
                    ^^ surround 4 1 lbrace (to_doc 0 body) rbrace 
                | Let {defs; body} ->
                    surround 4 1 (string "let" ^^ blank 1 ^^ lbrace)
                        (separate_map (semi ^^ hardline)
                            Stmt.to_doc (Vector1.to_list defs)
                        ^^ semi ^^ hardline ^^ to_doc 0 body)
                        rbrace
                | Letrec {defs; body} ->
                    surround 4 1 (string "letrec" ^^ blank 1 ^^ lbrace)
                        (separate_map (semi ^^ hardline)
                            Stmt.def_to_doc (Vector1.to_list defs)
                        ^^ semi ^^ hardline ^^ to_doc 0 body)
                        rbrace
                (*| LetType {typedefs; body} ->
                    surround 4 1 (string "letrec" ^^ blank 1 ^^ lbrace)
                        (separate_map (semi ^^ hardline)
                            (Type.binding_to_doc s) (Vector1.to_list typedefs)
                        ^^ semi ^^ hardline ^^ to_doc s body)
                        rbrace*)
                | Match {matchee; clauses} ->
                    let start = string "match" ^^ blank 1 ^^ to_doc 0 matchee ^^ blank 1 ^^ lbrace in
                    surround_separate_map 0 1 (start ^^ rbrace)
                        start (break 1) rbrace
                        clause_to_doc (Vector.to_list clauses)
                | App {callee; universals = _; arg} ->
                    prefix 4 1 (to_doc app_prec callee)
                        ((*surround_separate_map 4 0 empty
                            (break 1 ^^ langle) (comma ^^ break 1) (rangle ^^ break 1)
                            (Type.to_doc s) (Vector.to_list universals)
                        ^^*) to_doc (app_prec + 1) arg)
                    |> prec_parens (prec > app_prec)
                | PrimApp {op; universals = _; arg} ->
                    prefix 4 1 (string "__" ^^ Primop.to_doc op)
                        ((*surround_separate_map 4 0 empty
                            (break 1 ^^ langle) (comma ^^ break 1) (rangle ^^ break 1)
                            (Type.to_doc s) (Vector.to_list universals)
                        ^^*) to_doc (app_prec + 1) arg)
                    |> prec_parens (prec > app_prec)
                | PrimBranch {op; universals = _; arg; clauses} ->
                    prefix 4 1 (string "__" ^^ Branchop.to_doc op)
                        ((*surround_separate_map 4 0 empty
                            (break 1 ^^ langle) (comma ^^ break 1) (rangle ^^ break 1)
                            (Type.to_doc s) (Vector.to_list universals)
                        ^^*) to_doc (app_prec + 1) arg
                        ^^ blank 1 ^^ surround_separate_map 0 1 (braces bar)
                            lbrace (break 1) rbrace
                            prim_clause_to_doc (Vector.to_list clauses))
                    |> prec_parens (prec > app_prec)
                (*| Axiom {axioms; body} ->
                    group(
                        surround 4 1 (string "axiom")
                            (align (separate_map (semi ^^ break 1) (axiom_to_doc s)
                                (Vector1.to_list axioms)))
                            (string "in")
                        ^/^ to_doc s body)*)
                | Cast {castee; coercion} ->
                    infix 4 1 (string "|>") (to_doc cast_prec castee)
                        (Type.coercion_to_doc coercion)
                    |> prec_parens (prec > cast_prec)

                | Convert {coerce = _; arg} ->
                    infix 4 1 (string "|>>") (to_doc cast_prec arg)
                        (Type.to_doc expr.typ)
                    |> prec_parens (prec > cast_prec)
                
                | Record fields ->
                    surround_separate_map 4 0 (braces empty)
                        lbrace (comma ^^ break 1) rbrace
                        (fun (label, field) ->
                            infix 4 1 equals (string (Name.basename label |> Option.get))
                                (to_doc 0 field))
                        (Vector.to_list fields)
                | Where {base; fields} ->
                    surround 4 0 (to_doc 0 base ^^ blank 1 ^^ string "where" ^^ blank 1 ^^ lbrace)
                        (separate_map (comma ^^ break 1) 
                            (fun (label, field) ->
                                infix 4 1 equals (Name.to_doc label) (to_doc 1 field))
                            (Vector1.to_list fields))
                        rbrace
                    |> prec_parens (prec > 0)
                | With {base; label; field} ->
                    infix 4 1 (string "with") (to_doc 0 base)
                        (infix 4 1 equals (Name.to_doc label) (to_doc 1 field))
                    |> prec_parens (prec > 0)
                | Select {selectee; label} ->
                    prefix 4 0 (to_doc dot_prec selectee)
                        (dot ^^ string (Option.get (Name.basename label)))
                | Proxy typ -> brackets (Type.to_doc typ)
                | Use var -> var_to_doc var
                | Const c -> Const.to_doc c in

            to_doc 0 expr

    (*
        and axiom_to_doc s (name, universals, l, r) =
            let open PPrint in
            match Vector.to_list universals with
            | _ :: _ ->
                infix 4 1 colon (Name.to_doc name)
                    (infix 4 1 tilde
                        (Type.universal_to_doc s universals (Type.to_doc s l))
                        (Type.universal_to_doc s universals (Type.to_doc s r)))
            | [] ->
                infix 4 1 colon (Name.to_doc name)
                    (infix 4 1 tilde (Type.to_doc s l) (Type.to_doc s r))
    *)

        and clause_to_doc {pat; body} =
            PPrint.(bar ^^ blank 1
                ^^ infix 4 1 (string "->") (pat_to_doc pat) (to_doc body))

        and prim_clause_to_doc {res; prim_body} =
            PPrint.(bar ^^ blank 1
                ^^ infix 4 1 (string "->")
                    (match res with
                    | Some var -> def_to_doc var
                    | None -> empty)
                    (to_doc prim_body))

        and pat_to_doc (pat : pat) =
            let open PPrint in
            match pat.pterm with
            | TupleP pats ->
                surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    pat_to_doc (Vector.to_list pats)
            | ProxyP typ -> brackets (Type.to_doc typ)
            | VarP var -> parens (def_to_doc var)
            | WildP name -> underscore ^^ Name.to_doc name
            | ConstP c -> Const.to_doc c

        let var name vtyp = {name; vtyp}

        let fresh_var vtyp = var (Name.fresh ()) vtyp

        let at pos typ term = {term; pos; typ}

        let tuple vals = Tuple vals

        let focus focusee index = Focus {focusee; index}
        let fn t_scope param body = Fn {t_scope; param; body}
        let app callee universals arg = App {callee; universals; arg}
        let primapp op universals arg = PrimApp {op; universals; arg}
        let primbranch op universals arg clauses = PrimBranch {op; universals; arg; clauses}

        let let' defs body = match Vector1.of_vector defs with
            | Some defs -> (match body.term with
                | Let {defs = defs'; body} -> Let {defs = Vector1.append defs defs'; body}
                | _ -> Let {defs; body})
            | None -> body.term

        let letrec defs body = match Vector1.of_vector defs with
            | Some defs -> (match body.term with
                | Letrec {defs = defs'; body} ->
                    (* NOTE: expects alphatization, would be unsound otherwise: *)
                    Letrec {defs = Vector1.append defs defs'; body}
                | _ -> Letrec {defs; body})
            | None -> body.term

        let match' matchee clauses = Match {matchee; clauses}

    (*
        let axiom axioms body = match Vector1.of_vector axioms with
            | Some axioms -> Axiom {axioms; body}
            | None -> body.term
    *)
        let cast castee = function
            (*| Type.Refl _ -> castee.term*)
            | coercion -> Cast {castee; coercion}

        let convert arg coerce = Convert {coerce; arg}

        let record fields = Record fields

        let where base fields = match Vector1.of_vector fields with
            | Some fields -> Where {base; fields}
            | None -> base.term

        let select selectee label = Select {selectee; label}
        let proxy t = Proxy t
        let const c = Const c
        let use v = Use v

        let map_children f (expr : t) =
            let term = expr.term in
            let term' = match term with
                | Tuple vals ->
                    let vals' = Vector.map f vals in
                    let noop = Stream.from (Source.zip_with (==)
                            (Vector.to_source vals') (Vector.to_source vals))
                        |> Stream.into (Sink.all ~where: Fun.id) in
                    if noop then term else tuple vals'

                | Focus {focusee; index} ->
                    let focusee' = f focusee in
                    if focusee' == focusee then term else focus focusee' index

                | Fn {t_scope; param; body} ->
                    let body' = f body in
                    if body' == body then term else fn t_scope param body'

                | App {callee; universals; arg} ->
                    let callee' = f callee in
                    let arg' = f arg in
                    if callee' == callee && arg' == arg
                    then term
                    else app callee' universals arg'

                | PrimApp {op; universals; arg} ->
                    let arg' = f arg in
                    if arg' == arg then term else primapp op universals arg'

                | PrimBranch {op; universals; arg; clauses} ->
                    let arg' = f arg in
                    let clauses' = clauses |> Vector.map (fun {res; prim_body} ->
                        {res; prim_body = f prim_body}) in
                    if arg' == arg
                        && Stream.from (Source.zip_with (fun clause' clause ->
                                clause'.prim_body == clause.prim_body)
                            (Vector.to_source clauses') (Vector.to_source clauses))
                        |> Stream.into (Sink.all ~where: Fun.id)
                    then term
                    else primbranch op universals arg' clauses'

                | Let {defs; body} ->
                    let defs' = Vector1.map (fun stmt -> match stmt with
                        | Stmt.Def (pos, var, expr) ->
                            let expr' = f expr in
                            if expr' == expr then stmt else Def (pos, var, expr')
                        | Expr expr ->
                            let expr' = f expr in
                            if expr' == expr then stmt else Expr expr'
                    ) defs in
                    let body' = f body in
                    if body' == body
                        && Stream.from (Source.zip_with (==)
                            (Vector1.to_source defs') (Vector1.to_source defs))
                        |> Stream.into (Sink.all ~where: Fun.id)
                    then term
                    else let' (Vector1.to_vector defs') body'

                | Letrec {defs; body} ->
                    let defs' = Vector1.map (fun ((pos, var, expr) as def) ->
                        let expr' = f expr in
                        if expr' == expr then def else (pos, var, expr')
                    ) defs in
                    let body' = f body in
                    if body' == body
                        && Stream.from (Source.zip_with (==)
                            (Vector1.to_source defs') (Vector1.to_source defs))
                        |> Stream.into (Sink.all ~where: Fun.id)
                    then term
                    else letrec (Vector1.to_vector defs') body'

                (*| LetType {typedefs; body} ->
                    let body' = f body in
                    if body' == body then term else LetType {typedefs; body = body'}

                | Axiom {axioms; body} ->
                    let body' = f body in
                    if body' == body then term else Axiom {axioms; body = body'}*)

                | Cast {castee; coercion} ->
                    let castee' = f castee in
                    if castee' == castee then term else cast castee' coercion

                | Convert {coerce; arg} ->
                    let arg' = f arg in
                    if arg' == arg then term else convert arg' coerce

                | Record fields ->
                    let fields' = Vector.map (fun (label, field) -> (label, f field)) fields in
                    let noop = Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                            (Vector.to_source fields') (Vector.to_source fields))
                        |> Stream.into (Sink.all ~where: Fun.id) in
                    if noop then term else record fields'

                | With {base; label; field} ->
                    let base' = f base in
                    let field' = f field in
                    if base' == base && field' == field then term else With {base = base'; label; field = field'}

                | Where {base; fields} ->
                    let base' = f base in
                    let fields' = Vector1.map (fun (label, field) -> (label, f field)) fields in
                    if base' == base
                        && Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                            (Vector1.to_source fields') (Vector1.to_source fields))
                        |> Stream.into (Sink.all ~where: Fun.id)
                    then term
                    else where base' (Vector1.to_vector fields')

                | Select {selectee; label} ->
                    let selectee' = f selectee in
                    if selectee' == selectee then term else select selectee' label

                | Match {matchee; clauses} ->
                    let matchee' = f matchee in
                    let clauses' = Vector.map (fun {pat; body} -> {pat; body = f body}) clauses in
                    if matchee' == matchee
                        && Stream.from (Source.zip_with (fun clause' clause -> clause'.body == clause.body)
                            (Vector.to_source clauses') (Vector.to_source clauses))
                        |> Stream.into (Sink.all ~where: Fun.id)
                    then term
                    else match' matchee' clauses'

                | Proxy _ | Use _ | Const _ -> term in
            if term' == term then expr else {expr with term = term'}

        module Var = struct
            type t = var

            let compare (var : var) (var' : var) = Name.compare var.name var'.name
        end

        module VarSet = Set.Make(Var)
    end

    and Stmt : ComplexFcSigs.STMT
        with type expr = Expr.t
        with type var = Expr.var
    = struct
        type expr = Expr.t
        type var = Expr.var

        type def = Util.span * var * expr

        type t
            = Def of def
            | Expr of expr

        let def_to_doc ((_, var, expr) : def) =
            PPrint.(infix 4 1 equals (Expr.def_to_doc var) (Expr.to_doc expr))

        let to_doc = function
            | Def def -> def_to_doc def
            | Expr expr -> Expr.to_doc expr

        let rhs (Def (_, _, expr) | Expr expr) = expr
    end
end

(* HACK: These constants are 'unsafe' for OCaml recursive modules,
 * so we have to add them here: *)
module Type = struct
    include Types.Typ

    (* __typeIn [__boxed] *)
    let aType = App (Prim TypeIn, PromotedArray (Vector.singleton (Prim Boxed)))
    let aKind = aType

    (* __rowOf (__typeIn [__boxed]) *)
    let aRow = App (Prim RowOf, aType)

    (* __array __singleRep *)
    let rep = App (Prim Array, Prim SingleRep)
end

module Program = struct
    module Type = Type
    module Term = Term

    type t =
        { type_fns : Term.Expr.typedef Vector.t
        ; defs : Term.Stmt.def Vector.t
        ; main : Term.Expr.t }

    let type_fn_to_doc (name, kind) =
        let open PPrint in
        infix 4 1 equals (string "type" ^^ blank 1 ^^ Name.to_doc name)
            (Type.to_doc kind)

    let to_doc {type_fns; defs; main} =
        let open PPrint in
        separate_map (twice hardline) type_fn_to_doc (Vector.to_list type_fns)
        ^/^ separate_map (twice hardline) (fun def -> Term.Stmt.def_to_doc def ^^ semi)
            (Vector.to_list defs)
        ^^ twice (twice hardline) ^^ Term.Expr.to_doc main
end

