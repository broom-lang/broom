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
end = struct
    module Map = CCHashTrie.Make (struct
        type t = Name.t
        let equal = Name.equal
        let hash = Name.hash
    end)

    type t = Expr.Id.t Map.t

    let empty = Map.empty
    let add env k v = Map.add k v env
    let find = Fun.flip Map.get_exn
end

type meta_cont =
    | FnK of { pos : Util.span; domain : Type.t
        ; f : parent: Cont.Id.t option -> state: Expr.Id.t -> value: Expr.Id.t -> Transfer.t }
    | ExprK of {pos : Util.span; id : Expr.Id.t}
    | DirectK of {pos : Util.span; typ : Type.t; label : Cont.Id.t}

let log = TxRef.log () (* HACK *)

let convert_typ pos state_typ =
    let rec convert : Fc.Type.t -> Type.t = function
        | Exists (existentials, body) -> Exists (existentials, convert body)
        | Tuple typs -> Tuple (Vector.map convert typs)
        | PromotedTuple typs -> PromotedTuple (Vector.map convert typs)
        | PromotedArray typs -> PromotedArray (Vector.map convert typs)
        | Pi {universals; domain; eff = _; codomain} | Impli {universals; domain; codomain} ->
            let domain = convert domain in
            Pi {universals; domain = Vector.of_list [ state_typ
                ; Type.Pi {universals = Vector.empty
                    ; domain = Vector.of_list [state_typ; convert codomain]}
                ; domain ]}
        | Record row -> Record (convert row)
        | With {base; label; field} ->
            With {base = convert base; label; field = convert field}
        | EmptyRow -> EmptyRow
        | Proxy typ -> Proxy (convert typ)
        | Fn (param, body) -> Fn (param, convert body)
        | App (callee, arg) -> App (convert callee, convert arg)
        | Prim p -> Prim p
        | Bv bv -> Bv bv
        | Ov _ -> todo (Some pos)
        | Uv r -> (match Fc.Uv.get log r with
            | Assigned typ -> convert typ
            | Unassigned _ -> todo (Some pos) ~msg: "unassigned uv in CPS conversion") in
    convert

let convert state_typ ({type_fns; defs; main = main_body} : Fc.Program.t) =
    let builder = Builder.create type_fns in
    let state_typ = convert_typ main_body.pos ((* HACK *) Prim Int) state_typ in
    let convert_typ = convert_typ main_body.pos state_typ in
    let (main_span, main_body) =
        let pos =
            ( (if Vector.length defs > 0
              then (let (pos, _, _) = Vector.get defs 0 in fst pos)
              else fst main_body.pos)
            , snd main_body.pos ) in
        let codomain = main_body.typ in
        let defs = defs |> Vector.to_array |> Array.map (fun def -> Stmt.Def def) in
        (pos, FExpr.at pos codomain (FExpr.let' defs main_body)) in

    let rec convert parent state k env (expr : FExpr.t) = match expr.term with
        | Tuple values ->
            let rec convert_values parent state i values' =
                if i < Array.length values then begin
                    let value = Array.get values i in
                    let k = FnK {pos = value.pos; domain = convert_typ value.typ
                        ; f = fun ~parent ~state ~value ->
                            convert_values parent state (i + 1) (value :: values') } in
                    convert parent state k env value
                end else
                    Builder.express builder { pos = expr.pos; cont = parent
                        ; typ = convert_typ expr.typ
                        ; term = Tuple (Vector.of_list (List.rev values')) } (* OPTIMIZE *)
                    |> continue k parent state in
            convert_values parent state 0 []

        | Focus {focusee; index} ->
            let k = FnK {pos = focusee.pos; domain = convert_typ focusee.typ
                    ; f = fun ~parent ~state ~value: focusee ->
                        Builder.express builder { pos = expr.pos; cont = parent
                            ; typ = convert_typ expr.typ; term = Focus {focusee; index} }
                        |> continue k parent state } in
            convert parent state k env focusee

        | Fn {universals; param = {name = param_id; _} as param; body} ->
            let label = Cont.Id.fresh () in
            let domain = convert_typ param.vtyp in
            let ret_typ : Type.t = Pi {universals = Vector.empty
                ; domain = Vector.of_list [state_typ; convert_typ body.typ]} in
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
            let k = FnK {pos = callee.pos; domain = convert_typ callee.typ
                    ; f = fun ~parent ~state ~value: callee ->
                        let k = FnK {pos = arg.pos; domain = convert_typ arg.typ
                            ; f = fun ~parent ~state ~value: arg ->
                                let ret = cont_value parent k in
                                { pos = expr.pos; term = Jump { callee
                                    ; universals = Vector.map convert_typ universals
                                    ; args = Vector.of_list [state; ret; arg] } } } in
                        convert parent state k env arg } in
            convert parent state k env callee

        | PrimApp {op; universals; arg} ->
            if Primop.is_pure op then begin
                let k = FnK {pos = arg.pos; domain = convert_typ arg.typ
                    ; f = fun ~parent ~state ~value: arg ->
                        Builder.express builder {pos = expr.pos; cont = parent
                            ; typ = convert_typ expr.typ
                            ; term = PrimApp {op
                                ; universals = Vector.map convert_typ universals
                                ; args = Vector.singleton arg}}
                        |> continue k parent state } in
                convert parent state k env arg
            end else begin
                let codomain = convert_typ expr.typ in
                let k = FnK {pos = arg.pos; domain = convert_typ arg.typ
                    ; f = fun ~parent ~state ~value: arg ->
                        let app = Builder.express builder {pos = expr.pos; cont = parent
                            ; typ = Tuple (Vector.of_list [state_typ; codomain])
                            ; term = PrimApp {op
                                ; universals = Vector.map convert_typ universals
                                ; args = Vector.of_list [state; arg]}} in
                        let state = Builder.express builder {pos = expr.pos; cont = parent
                            ; typ = state_typ
                            ; term = Focus {focusee = app; index = 0}} in
                        let result = Builder.express builder {pos = expr.pos; cont = parent
                            ; typ = codomain
                            ; term = Focus {focusee = app; index = 1}} in
                        continue k parent state result } in
                convert parent state k env arg
            end

        | PrimBranch {op; universals; arg; clauses} ->
            let k = FnK { pos = expr.pos; domain = convert_typ arg.typ
                ; f = fun ~parent: _ ~state ~value: arg ->
                    let join = trivialize_cont k in
                    let clauses = clauses |> Vector.map (fun {FExpr.res; prim_body = body} ->
                        let branch = Cont.Id.fresh () in
                        let cont : Cont.t = 
                            let parent = Some branch in
                            let state = Builder.express builder {pos = body.pos; cont = parent; typ = state_typ
                                ; term = Param {label = branch; index = 0}} in
                            let (params, env) = match res with
                                | Some res ->
                                    let codomain = convert_typ res.vtyp in
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
                        ; universals = Vector.map convert_typ universals
                        ; state; args = Vector.singleton arg 
                        ; clauses}} } in
            convert parent state k env arg

        | Let {defs; body} ->
            let rec convert_defs state i env =
                if i < Array1.length defs then match Array1.get defs i with
                    | Def (_, {name; _}, value) ->
                        let k = FnK {pos = value.pos; domain = convert_typ value.typ
                            ; f = fun ~parent: _ ~state ~value ->
                                let env = Env.add env name value in
                                convert_defs state (i + 1) env } in
                        convert parent state k env value
                    | Expr expr ->
                        let k = FnK {pos = expr.pos; domain = convert_typ expr.typ
                            ; f = fun ~parent: _ ~state ~value: _ ->
                                convert_defs state (i + 1) env} in
                        convert parent state k env expr
                else convert parent state k env body in
            convert_defs state 0 env

        | Use {name; _} -> continue k parent state (Env.find env name)

        | Match {matchee; clauses} ->
            let k = FnK { pos = expr.pos; domain = convert_typ matchee.typ
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
                if i < Array.length fields then begin
                    let (label, field) = Array.get fields i in
                    let k = FnK {pos = field.pos; domain = convert_typ field.typ
                        ; f = fun ~parent: _ ~state ~value: field' ->
                            convert_fields state (i + 1) ((label, field') :: fields') } in
                    convert parent state k env field
                end else
                    Builder.express builder {pos = expr.pos; cont = parent
                        ; typ = convert_typ expr.typ
                        ; term = Record (Vector.of_list (List.rev fields')) } (* OPTIMIZE *)
                    |> continue k parent state in
            convert_fields state 0 []

        | With {base; label; field} ->
            let k = FnK {pos = expr.pos; domain = convert_typ base.typ
                ; f = fun ~parent ~state ~value: base ->
                    let k = FnK {pos = expr.pos; domain = convert_typ field.typ
                        ; f = fun ~parent ~state ~value: field ->
                            Builder.express builder {pos = expr.pos; cont = parent
                                ; typ = convert_typ expr.typ; term = With {base; label; field}}
                            |> continue k parent state } in
                    convert parent state k env field} in
            convert parent state k env base

        | Where {base; fields} ->
            let k = FnK {pos = expr.pos; domain = convert_typ base.typ
                ; f = fun ~parent ~state ~value: base ->
                    let rec convert_fields state i fields' =
                        if i < Array1.length fields then begin
                            let (label, field) = Array1.get fields i in
                            let k = FnK {pos = field.pos; domain = convert_typ field.typ
                                ; f = fun ~parent: _ ~state ~value: field' ->
                                    convert_fields state (i + 1) ((label, field') :: fields') } in
                            convert parent state k env field
                        end else
                            Builder.express builder {pos = expr.pos; cont = parent
                                ; typ = convert_typ expr.typ
                                ; term = Where {base
                                    ; fields = Vector.of_list (List.rev fields')}} (* OPTIMIZE *)
                            |> continue k parent state in
                    convert_fields state 0 [] } in
            convert parent state k env base

        | Select {selectee; label} ->
                let k = FnK {pos = expr.pos; domain = convert_typ selectee.typ
                    ; f = fun ~parent ~state ~value: selectee ->
                        Builder.express builder {pos = expr.pos; cont = parent
                            ; typ = convert_typ expr.typ
                            ; term = Select {selectee; field = label}}
                        |> continue k parent state} in
            convert parent state k env selectee

        | Proxy typ ->
            Builder.express builder {pos = expr.pos; cont = parent; typ = convert_typ expr.typ
                ; term = Proxy (convert_typ typ)}
            |> continue k parent state

        | Const c ->
            let typ = convert_typ expr.typ in
            Builder.express builder {pos = expr.pos; cont = parent; typ; term = Const c}
            |> continue k parent state

        | Patchable r -> TxRef.(convert parent state k env !r)

        | Letrec _ -> bug (Some expr.pos) ~msg: "encountered `letrec` in CPS conversion"

        | _ -> todo (Some expr.pos)

    and convert_pattern pat : Pattern.t = match pat.pterm with
        | ConstP c -> Const c
        | WildP _ -> Wild
        | VarP _ | TupleP _ | ProxyP _ ->
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

    let convert_export pos name params (body : FExpr.t) =
        let id = Cont.Id.fresh () in
        let parent = Some id in
        let codomain = convert_typ body.typ in
        let state =
            Builder.express builder {pos; cont = parent; typ = state_typ
                ; term = Const (Int 0)} in (* FIXME *)
        let k = FnK {pos = body.pos; domain = convert_typ body.typ
            ; f = fun ~parent: _ ~state: _ ~value ->
                {pos; term = Return (Vector.singleton codomain, Vector.singleton value)} } in
        let env = Env.empty in
        let cont : Cont.t =
            { pos; name; universals = Vector.empty; params
            ; body = convert parent state k env body } in
        Builder.add_cont builder id cont;
        id in

    let main_id = convert_export main_span None Vector.empty main_body in
    Builder.build builder main_id

