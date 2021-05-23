open Asserts

open Cps
module Builder = Program.Builder
module FExpr = Fc.Term.Expr
module Stmt = Fc.Term.Stmt

module Env : sig
    type t

    val empty : t

    val add : t -> Name.t -> Expr.Id.t -> t
    val find : t -> Name.t -> Expr.Id.t

    val add_typ : t -> Name.t -> Type.t -> t
    (*val find_typ : t -> Name.t -> Type.t*)

    val add_co : t -> Name.t -> Type.t Fc.Type.coercion -> t
    val find_co : t -> Name.t -> Type.t Fc.Type.coercion
end = struct
    module Vals = Name.HashMap
    module Typs = Name.HashMap
    module Coercions = Name.HashMap

    type t = {vals : Expr.Id.t Vals.t; typs : Type.t Typs.t
        ; cos : Type.t Fc.Type.coercion Coercions.t}

    let empty = {vals = Vals.empty; typs = Typs.empty
        ; cos = Coercions.empty}

    let add env k v = {env with vals = Vals.add k v env.vals}
    let find env k = Vals.get_exn k env.vals

    let add_typ env k t = {env with typs = Typs.add k t env.typs}
    (*let find_typ env k = Typs.get_exn k env.typs*)

    let add_co env k co = {env with cos = Coercions.add k co env.cos}
    let find_co env k = Coercions.get_exn k env.cos
end

type meta_cont =
    | FnK of { pos : Util.span; domain : Type.t
        ; f : parent: Cont.Id.t option -> state: Expr.Id.t -> value: Expr.Id.t -> Transfer.t }
    | ExprK of {pos : Util.span; id : Expr.Id.t}
    | DirectK of {pos : Util.span; typ : Type.t; label : Cont.Id.t}

let convert_typ state_typ _ pos =
    let rec convert : Fc.Type.t -> Type.t = function
        | Exists {existentials; body} -> Exists (existentials, convert body)
        | Pair {fst; snd} -> Pair {fst = convert fst; snd = convert snd}

        | Pi {universals; domain; eff = _; codomain} | Impli {universals; domain; codomain} ->
            (* FIXME: bv indices in codomain go off by one: *)
            let domain = convert domain in
            Pi {universals; domain = Vector.of_list [ state_typ
                ; Type.Pi {universals = Vector.empty
                    ; domain = Vector.of_list [state_typ; convert codomain]}
                ; domain ]}

        | Record row -> Record (convert row)
        | Variant row -> Variant (convert row)
        | With {base; label; field} -> With {base = convert base; label; field = convert field}
        | EmptyRow -> EmptyRow
        | Proxy typ -> Proxy (convert typ)
        | Fn {param; body} -> Fn (param, convert body)
        | App {callee; arg} -> App (convert callee, convert arg)
        | Prim p -> Prim p
        | Bv bv -> Bv bv
        | Ov _ (*((name, _), _)*) -> todo None (*Env.find_typ env name*)

        | Uv r -> (match Transactional.Ref.(!) r with
            | Assigned typ -> convert typ
            | Unassigned _ -> todo (Some pos) ~msg: "unassigned uv in CPS conversion") in
    convert

let convert_co state_typ env pos =
    let rec convert : Fc.Type.t Fc.Type.coercion -> Type.t Fc.Type.coercion = function
        | PiCo {universals; domain; codomain} ->
            PiCo {universals; domain = convert domain; codomain = convert codomain}
        | PairCo (fst, snd) -> PairCo (convert fst, convert snd)
        | RecordCo row_co -> RecordCo (convert row_co)
        | VariantCo row_co -> VariantCo (convert row_co)
        | WithCo {base; label; field} ->
            WithCo {base = convert base; label; field = convert field}
        | ProxyCo co -> ProxyCo (convert co)
        | ExistsCo (existentials, co) -> ExistsCo (existentials, convert co)
        | Inst (co, targs) ->
            Inst (convert co, Vector1.map (convert_typ state_typ env pos) targs)
        | Symm co -> Symm (convert co)
        | Trans (co, co') -> Trans (convert co, convert co')
        | Refl typ -> Refl (convert_typ state_typ env pos typ)
        | Comp (co, co') -> Comp (convert co, Vector1.map convert co')
        | AUse name -> Env.find_co env name
        | Axiom (universals, l, r) -> Axiom (universals, convert_typ state_typ env pos l
            , convert_typ state_typ env pos r)
        | Patchable r -> convert (Transactional.Ref.(!) r) in
    convert

let convert state_typ ({type_fns; defs; main = main_body} : Fc.Program.t) =
    let builder = Builder.create type_fns in
    let env = Env.empty in
    let state_typ = convert_typ ((* HACK *) Prim Int) env main_body.pos state_typ in
    let convert_typ = convert_typ state_typ in
    let convert_co = convert_co state_typ in
    let (main_span, main_body) =
        let pos =
            ( (if Vector.length defs > 0
              then (let (pos, _, _) = Vector.get defs 0 in fst pos)
              else fst main_body.pos)
            , snd main_body.pos ) in
        let codomain = main_body.typ in
        let defs = defs |> Vector.map (fun def -> Stmt.Def def) in
        let stmts = Vector.append defs (Vector.singleton (Stmt.Expr main_body)) in
        let body = FExpr.at pos (Prim Int) (FExpr.const (Int 0)) in
        (pos, FExpr.at pos codomain (FExpr.let' stmts body)) in

    let rec convert parent state k env (expr : FExpr.t) = match expr.term with
        | Pair {fst; snd} ->
            let fst_typ = convert_typ env fst.pos fst.typ in
            let k = FnK {pos = fst.pos; domain = fst_typ
                ; f = fun ~parent ~state ~value: fst ->
                    let snd_typ = convert_typ env snd.pos snd.typ in
                    let k = FnK {pos = snd.pos; domain = snd_typ
                        ; f = fun ~parent ~state ~value: snd ->
                            Builder.express builder {pos = expr.pos; cont = parent
                                ; typ = convert_typ env expr.pos expr.typ
                                ; term = PrimApp {op = Pair
                                    ; universals = Vector.of_array_unsafe [|fst_typ; snd_typ|]
                                    ; args = Vector.of_array_unsafe [|fst; snd|]}} (* OPTIMIZE *)
                            |> continue k parent state} in
                    convert parent state k env snd} in
            convert parent state k env fst

        | Fst arg ->
            let k = FnK {pos = arg.pos; domain = convert_typ env arg.pos arg.typ
                ; f = fun ~parent ~state ~value: arg ->
                    let typ = convert_typ env expr.pos expr.typ in
                    Builder.express builder {pos = expr.pos; cont = parent; typ
                        ; term = PrimApp {op = Fst
                            ; universals = Vector.singleton typ
                            ; args = Vector.singleton arg}}
                    |> continue k parent state} in
            convert parent state k env arg

        | Snd arg ->
            let k = FnK {pos = arg.pos; domain = convert_typ env arg.pos arg.typ
                ; f = fun ~parent ~state ~value: arg ->
                    let typ = convert_typ env expr.pos expr.typ in
                    Builder.express builder {pos = expr.pos; cont = parent; typ
                        ; term = PrimApp {op = Snd 
                            ; universals = Vector.singleton typ
                            ; args = Vector.singleton arg}}
                    |> continue k parent state} in
            convert parent state k env arg

        | Fn {universals; param = {name = param_id; _} as param; body} ->
            let label = Cont.Id.fresh () in
            let env = Vector.foldi (fun env index (name, _) ->
                Env.add_typ env name (TParam {label; index})
            ) env universals in
            let domain = convert_typ env expr.pos param.vtyp in
            let ret_typ : Type.t = Pi {universals = Vector.empty
                ; domain = Vector.of_list [state_typ; convert_typ env body.pos body.typ]} in
            let domain' = Vector.of_list [state_typ; ret_typ; domain] in
            let f : Cont.t = 
                let parent = Some label in
                let state = Builder.express builder {pos = expr.pos; cont = parent; typ = state_typ
                    ; term = Param {label; index = 0}} in
                let ret_id = Builder.express builder {pos = expr.pos; cont = parent; typ = ret_typ
                    ; term = Param {label; index = 1}} in
                let ret = ExprK {pos = expr.pos; id = ret_id} in
                let param = Builder.express builder {pos = expr.pos; cont = parent; typ = domain
                    ; term = Param {label; index = 2}} in
                let env = Env.add env param_id param in
                (* TODO: name = Some ... *)
                { pos = expr.pos; name = None; universals; params = domain'
                    ; body = convert parent state ret env body } in
            Builder.add_cont builder label f;
            Builder.express builder {pos = expr.pos; cont = parent
                ; typ = Pi {universals = Vector.map snd universals; domain = domain'}
                ; term = Label label }
            |> continue k parent state

        | App {callee; universals; arg} ->
            let k = FnK {pos = callee.pos; domain = convert_typ env callee.pos callee.typ
                    ; f = fun ~parent ~state ~value: callee ->
                        let k = FnK {pos = arg.pos; domain = convert_typ env arg.pos arg.typ
                            ; f = fun ~parent ~state ~value: arg ->
                                let ret = cont_value parent k in
                                { pos = expr.pos; term = Jump { callee
                                    ; universals = Vector.map (convert_typ env expr.pos)
                                        universals
                                    ; args = Vector.of_list [state; ret; arg] } } } in
                        convert parent state k env arg } in
            convert parent state k env callee

        | PrimApp {op; universals; args} ->
            let argc = Vector.length args in
            let rec convert_args parent state i args' =
                if i < argc then begin
                    let arg = Vector.get args i in
                    let k = FnK {pos = arg.pos; domain = convert_typ env arg.pos arg.typ
                        ; f = fun ~parent ~state ~value ->
                            convert_args parent state (i + 1) (value :: args') } in
                    convert parent state k env arg
                end else if Primop.is_pure op then begin
                    Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = convert_typ env expr.pos expr.typ
                        ; term = PrimApp {op
                            ; universals = Vector.map (convert_typ env expr.pos) universals
                            ; args = Vector.of_list (List.rev args')}} (* OPTIMIZE *)
                    |> continue k parent state
                end else begin
                    let codomain = convert_typ env expr.pos expr.typ in
                    let app = Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = Pair {fst = state_typ; snd = codomain}
                        ; term = PrimApp {op 
                            ; universals = Vector.map (convert_typ env expr.pos) universals
                            ; args = Vector.append (Vector.singleton state)
                                (Vector.of_list (List.rev args'))}} in (* OPTIMIZE *)
                    let state = Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = state_typ
                        ; term = PrimApp {op = Fst
                            ; universals = Vector.singleton state_typ
                            ; args = Vector.singleton app}} in
                    let result = Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = codomain
                        ; term = PrimApp {op = Snd
                            ; universals = Vector.singleton codomain
                            ; args = Vector.singleton app}} in
                    continue k parent state result
                end in
            convert_args parent state 0 []

        | PrimBranch {op; universals; args; clauses} ->
            let argc = Vector.length args in
            let rec convert_args parent state i args' =
                if i < argc then begin
                    let arg = Vector.get args i in
                    let k = FnK {pos = arg.pos; domain = convert_typ env arg.pos arg.typ
                        ; f = fun ~parent ~state ~value ->
                            convert_args parent state (i + 1) (value :: args') } in
                    convert parent state k env arg
                end else begin
                    let join = trivialize_cont k in
                    let clauses = clauses |> Vector.map (fun {FExpr.res; prim_body = body} ->
                        let branch = Cont.Id.fresh () in
                        let cont : Cont.t = 
                            let parent = Some branch in
                            let state = Builder.express builder {pos = body.pos; cont = parent; typ = state_typ
                                ; term = Param {label = branch; index = 0}} in
                            let (params, env) = match res with
                                | Some res ->
                                    let codomain = convert_typ env expr.pos res.vtyp in
                                    let v = Builder.express builder {pos = body.pos; cont = parent; typ = codomain
                                        ; term = Param {label = branch; index = 1}} in
                                    (Vector.of_list [state_typ; codomain], Env.add env res.name v)
                                | None -> (Vector.singleton state_typ, env) in
                            {pos = body.pos; name = None
                                ; universals = Vector.empty; params
                                ; body = convert parent state join env body } in
                        Builder.add_cont builder branch cont;
                        {Transfer.pat = Wild; dest = branch}) in
                    {pos = expr.pos; term = PrimApp {op
                        ; universals = Vector.map (convert_typ env expr.pos) universals
                        ; state; args = Vector.of_list (List.rev args') (* OPTIMIZE *)
                        ; clauses}}
                end in
            convert_args parent state 0 []

        | LetType {typedefs; body} ->
            let env = Vector1.fold (fun env (name, kind) ->
                Env.add_typ env name (Abstract kind)
            ) env typedefs in
            convert parent state k env body

        | Axiom {axioms; body} ->
            let env = Vector1.fold (fun env (name, universals, l, r) ->
                Env.add_co env name (Axiom (universals, convert_typ env expr.pos l
                    , convert_typ env expr.pos r))
            ) env axioms in
            convert parent state k env body

        | Cast {castee; coercion} ->
            let k = FnK {pos = castee.pos; domain = convert_typ env castee.pos castee.typ
                ; f = fun ~parent: _ ~state ~value: castee ->
                    Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = convert_typ env expr.pos expr.typ
                        ; term = Cast {castee; coercion = convert_co env expr.pos coercion}}
                    |> continue k parent state} in
            convert parent state k env castee

        | Pack {existentials; impl} ->
            let k = FnK {pos = impl.pos; domain = convert_typ env impl.pos impl.typ
                ; f = fun ~parent: _ ~state ~value ->
                    Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = convert_typ env expr.pos expr.typ
                        ; term = Pack {impl = value
                            ; existentials = Vector1.map (convert_typ env expr.pos) existentials}}
                    |> continue k parent state} in
            convert parent state k env impl

        | Unpack {existentials; var; value; body} ->
            let env = Vector1.foldi (fun env index (name, _) ->
                Env.add_typ env name (Existing {value = var.name; index})
            ) env existentials in
            let k = FnK { pos = expr.pos; domain = convert_typ env value.pos value.typ
                ; f = fun ~parent: _ ~state ~value: packed ->
                    let env =
                        Builder.express builder {pos = value.pos; cont = parent
                            ; typ = convert_typ env expr.pos var.vtyp
                            ; term = Unpack packed}
                    |> Env.add env var.name in
                    convert parent state k env body } in
            convert parent state k env value

        | Let {defs; body} ->
            let rec convert_defs state i env =
                if i < Vector1.length defs then match Vector1.get defs i with
                    | Def (_, {pterm = VarP {name; _}; _}, value) ->
                        let k = FnK {pos = value.pos; domain = convert_typ env value.pos value.typ
                            ; f = fun ~parent: _ ~state ~value ->
                                let env = Env.add env name value in
                                convert_defs state (i + 1) env } in
                        convert parent state k env value
                    | Def (span, _, _) -> unreachable (Some span)
                    | Expr expr ->
                        let k = FnK {pos = expr.pos; domain = convert_typ env expr.pos expr.typ
                            ; f = fun ~parent: _ ~state ~value: _ ->
                                convert_defs state (i + 1) env} in
                        convert parent state k env expr
                else convert parent state k env body in
            convert_defs state 0 env

        | Use {name; _} -> continue k parent state (Env.find env name)

        | Match {matchee; clauses} ->
            let k = FnK { pos = expr.pos; domain = convert_typ env matchee.pos matchee.typ
                ; f = fun ~parent: _ ~state ~value: matchee ->
                    let join = trivialize_cont k in
                    let clauses = clauses |> Vector.map (fun {FExpr.pat; body} ->
                        let pat = convert_pattern pat in
                        let branch = Cont.Id.fresh () in
                        let cont : Cont.t = 
                            let parent = Some branch in
                            let state = Builder.express builder {pos = body.pos; cont = parent; typ = state_typ
                                ; term = Param {label = branch; index = 0}} in
                            let transfer = convert parent state join env body in
                            {pos = body.pos; name = None
                                ; universals = Vector.empty; params = Vector.singleton state_typ
                                ; body = transfer } in
                        Builder.add_cont builder branch cont;
                        {Transfer.pat; dest = branch}) in
                    {pos = expr.pos; term = Match {matchee; state; clauses}} } in
            convert parent state k env matchee

        | Record fields ->
            let rec convert_fields state i fields' =
                if i < Vector.length fields then begin
                    let (label, field) = Vector.get fields i in
                    let k = FnK {pos = field.pos; domain = convert_typ env field.pos field.typ
                        ; f = fun ~parent: _ ~state ~value: field' ->
                            convert_fields state (i + 1) ((label, field') :: fields') } in
                    convert parent state k env field
                end else
                    Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = convert_typ env expr.pos expr.typ
                        ; term = Record (Vector.of_list (List.rev fields')) } (* OPTIMIZE *)
                    |> continue k parent state in
            convert_fields state 0 []

        | With {base; label; field} ->
            let k = FnK {pos = expr.pos; domain = convert_typ env base.pos base.typ
                ; f = fun ~parent ~state ~value: base ->
                    let k = FnK {pos = expr.pos; domain = convert_typ env field.pos field.typ
                        ; f = fun ~parent ~state ~value: field ->
                            Builder.express builder {pos = expr.pos; cont = parent
                                ; typ = convert_typ env expr.pos expr.typ
                                ; term = With {base; label; field}}
                            |> continue k parent state } in
                    convert parent state k env field} in
            convert parent state k env base

        | Where {base; fields} ->
            let k = FnK {pos = expr.pos; domain = convert_typ env base.pos base.typ
                ; f = fun ~parent ~state ~value: base ->
                    let rec convert_fields state i fields' =
                        if i < Vector1.length fields then begin
                            let (label, field) = Vector1.get fields i in
                            let k = FnK {pos = field.pos
                                ; domain = convert_typ env field.pos field.typ
                                ; f = fun ~parent: _ ~state ~value: field' ->
                                    convert_fields state (i + 1) ((label, field') :: fields') } in
                            convert parent state k env field
                        end else
                            Builder.express builder {pos = expr.pos; cont = parent
                                ; typ = convert_typ env expr.pos expr.typ
                                ; term = Where {base
                                    ; fields = Vector.of_list (List.rev fields')}} (* OPTIMIZE *)
                            |> continue k parent state in
                    convert_fields state 0 [] } in
            convert parent state k env base

        | Select {selectee; label} ->
                let k = FnK {pos = expr.pos; domain = convert_typ env selectee.pos selectee.typ
                    ; f = fun ~parent ~state ~value: selectee ->
                        Builder.express builder {pos = expr.pos; cont = parent
                            ; typ = convert_typ env expr.pos expr.typ
                            ; term = Select {selectee; field = label}}
                        |> continue k parent state} in
            convert parent state k env selectee

        | Proxy typ ->
            Builder.express builder {pos = expr.pos; cont = parent
                ; typ = convert_typ env expr.pos expr.typ
                ; term = Proxy (convert_typ env expr.pos typ)}
            |> continue k parent state

        | Const c ->
            let typ = convert_typ env expr.pos expr.typ in
            Builder.express builder {pos = expr.pos; cont = parent; typ; term = Const c}
            |> continue k parent state

        | Convert _ -> bug (Some expr.pos) ~msg: "encountered Convert in CPS conversion"
        | Letrec _ -> bug (Some expr.pos) ~msg: "encountered `letrec` in CPS conversion"

    and convert_pattern pat : Pattern.t = match pat.pterm with
        | ConstP c -> Const c
        | WildP _ -> Wild
        | View _ | VarP _ | PairP _ | ProxyP _ ->
            bug (Some pat.ppos) ~msg: "unexpanded pattern in CPS conversion"

    and continue k parent state value = match k with
        | FnK {pos = _; domain = _; f} -> f ~parent ~state ~value
        | ExprK {pos; id = callee} ->
            {pos; term = Jump {callee; universals = Vector.empty
                ; args = Vector.of_list [state; value]}}
        | DirectK {pos; typ = _; label = callee} ->
            {pos; term = Goto {callee; universals = Vector.empty
                ; args = Vector.of_list [state; value]}}

    and trivialize_cont = function
        | FnK {pos; domain; f} ->
            let label = Cont.Id.fresh () in
            let parent = Some label in
            let state = Builder.express builder { pos; cont = parent; typ = state_typ
                ; term = Param {label; index = 0} } in
            let param = Builder.express builder { pos; cont = parent; typ = domain
                ; term = Param {label; index = 1} } in
            let universals = Vector.empty in
            let domain = Vector.of_list [state_typ; domain] in
            let cont : Cont.t = { pos; name = None; universals; params = domain
                ; body = f ~parent ~state ~value: param } in
            Builder.add_cont builder label cont;
            DirectK {pos; typ = Pi {universals; domain}; label}
        | (ExprK _ | DirectK _) as k -> k

    and cont_value parent k =
        match trivialize_cont k with
        | ExprK {pos = _; id} -> id
        | DirectK {pos; typ; label} ->
            Builder.express builder {pos; cont = parent; typ; term = Label label}
        | FnK _ -> unreachable None in

    let convert_export env pos name params (body : FExpr.t) =
        let id = Cont.Id.fresh () in
        let parent = Some id in
        let codomain = convert_typ env body.pos body.typ in
        let state =
            Builder.express builder {pos; cont = parent; typ = state_typ
                ; term = Const (Int 0)} in (* FIXME *)
        let k = FnK {pos = body.pos; domain = codomain
            ; f = fun ~parent: _ ~state: _ ~value ->
                {pos; term = Return (Vector.singleton codomain, Vector.singleton value)} } in
        let cont : Cont.t =
            { pos; name; universals = Vector.empty; params
            ; body = convert parent state k env body } in
        Builder.add_cont builder id cont;
        id in

    let main_id = convert_export env main_span None Vector.empty main_body in
    Builder.build builder main_id

