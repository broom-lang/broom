open Streaming

open Asserts
type plicity = Util.plicity

module TS = TyperSigs
module AExpr = Ast.Expr
module AStmt = Ast.Stmt
module T = Fc.Type
module FStmt = Fc.Term.Stmt
module FExpr = Fc.Term.Expr
module Coercer = Fc.Term.Coercer
module Env = TypeEnv
type eff = T.t
type 'a typing = 'a TyperSigs.typing
type ctrs = Constraint.queue
module Tx = Transactional
open Tx.Ref

module Make
    (Constraints : TS.CONSTRAINTS)
    (Kinding : TS.KINDING)
= struct

(* # Constants *)

    let const_typ (c : Const.t) = T.Prim (match c with
        | Unit -> Unit
        | Int _ -> Int
        | String _ -> String)

(* # Primops *)

    type op_typ =
        | Primop of Primop.t * T.t Vector.t * T.t Vector.t * T.t * T.t
        | Branchop of Branchop.t * T.t Vector.t * T.t Vector.t * T.t * T.t Vector.t

    let primop_typ : Ast.Primop.t -> op_typ = function
        | Include | Require
        | Do | Let | Module | Interface | Explicitly -> bug None

        | Pair -> (* forall a b . (a, b) -> Pair a b *)
            Primop ( Pair
                , Vector.of_array_unsafe [|T.aType; T.aType|]
                , Vector.of_array_unsafe [|T.Bv {depth = 0; sibli = 0; bkind = T.aType}
                    ; Bv {depth = 0; sibli = 1; bkind = T.aType}|]
                , T.EmptyRow
                , Pair {fst = Bv {depth = 0; sibli = 0; bkind = T.aType}
                    ; snd = Bv {depth = 0; sibli = 1; bkind = T.aType}} )
        | Fst -> (* forall a b . Pair a b -> a *)
            Primop ( Fst
                , Vector.of_array_unsafe [|T.aType; T.aType|]
                , Vector.singleton (T.Pair {fst = Bv {depth = 0; sibli = 0; bkind = T.aType}
                    ; snd = Bv {depth = 0; sibli = 1; bkind = T.aType}})
                , T.EmptyRow
                , Bv {depth = 0; sibli = 0; bkind = T.aType} )
        | Snd -> (* forall a b . Pair a b -> b *)
            Primop ( Snd
                , Vector.of_array_unsafe [|T.aType; T.aType|]
                , Vector.singleton (T.Pair {fst = Bv {depth = 0; sibli = 0; bkind = T.aType}
                    ; snd = Bv {depth = 0; sibli = 1; bkind = T.aType}})
                , T.EmptyRow
                , Bv {depth = 0; sibli = 1; bkind = T.aType} )
        | CellNew -> (* forall a . () -> __cell a *)
            Primop ( CellNew
                , Vector.singleton T.aType, Vector.empty
                , T.EmptyRow
                , App {callee = Prim Cell; arg = Bv {depth = 0; sibli = 0; bkind = T.aType}} )
        | CellInit -> (* forall a . (__cell a, a) -> () *)
            Primop ( CellInit
                , Vector.singleton T.aType
                , Vector.of_list [ T.App {callee = Prim Cell; arg = Bv {depth = 0; sibli = 0; bkind = T.aType}}
                    ; Bv {depth = 0; sibli = 0; bkind = T.aType} ]
                , T.EmptyRow, Prim Unit )
        | CellGet -> (* forall a . __cell a -> a *)
            Primop ( CellGet
                , Vector.singleton T.aType
                , Vector.singleton (T.App {callee = Prim Cell; arg = Bv {depth = 0; sibli = 0; bkind = T.aType}})
                , T.EmptyRow
                , Bv {depth = 0; sibli = 0; bkind = T.aType} )

        | Int ->
            Primop (Int, Vector.empty, Vector.singleton (T.Prim Unit), T.EmptyRow, Proxy (Prim Int))
        | String ->
            Primop (String, Vector.empty, Vector.singleton (T.Prim Unit), T.EmptyRow, Proxy (Prim String))

        | Type ->
            Primop ( Type
                , Vector.empty, Vector.singleton (T.Prim Unit), T.EmptyRow
                , T.Proxy (T.Exists {existentials = Vector1.singleton T.aType
                    ; body = Proxy (Bv {depth = 0; sibli = 0; bkind = T.aType})}) )

        | TypeOf -> (* FIXME: Enforce argument purity *)
            Primop ( TypeOf
                , Vector.singleton T.aType
                , Vector.singleton (T.Bv {depth = 0; sibli = 0; bkind = T.aType})
                , EmptyRow
                , Proxy (Bv {depth = 0; sibli = 0; bkind = T.aType}) )
        | Import ->
            Primop ( Import
                , Vector.singleton T.aType
                , Vector.of_list [T.Proxy (Bv {depth = 0; sibli = 0; bkind = T.aType}); Prim String]
                , EmptyRow
                , Bv {depth = 0; sibli = 0; bkind = T.aType} )
        | GlobalSet ->
            Primop ( GlobalSet
                , Vector.singleton T.aType
                , Vector.of_list [T.Prim String; Bv {depth = 0; sibli = 0; bkind = T.aType}]
                , EmptyRow, Prim Unit )
        | GlobalGet ->
            Primop ( GlobalGet
                , Vector.singleton T.aType
                , Vector.singleton (T.Prim String)
                , EmptyRow, Bv {depth = 0; sibli = 0; bkind = T.aType} )

        | IAdd ->
            Branchop ( IAdd
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Int; Prim Unit] )
        | ISub ->
            Branchop ( ISub
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Int; Prim Unit] )
        | IMul ->
            Branchop ( IMul
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Int; Prim Unit] )
        | IDiv ->
            Branchop ( IDiv
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Int; Prim Unit] )

        | ILt ->
            Branchop ( ILt
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Unit; Prim Unit] )
        | ILe ->
            Branchop ( ILe
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Unit; Prim Unit] )
        | IGt ->
            Branchop ( IGt
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Unit; Prim Unit] )
        | IGe ->
            Branchop ( IGe
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Unit; Prim Unit] )
        | IEq ->
            Branchop ( IEq
                , Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
                , T.EmptyRow, Vector.of_list [T.Prim Unit; Prim Unit] )

(* # Patterns *)

    let bind_pat env (plicity : plicity) pat add_var =
        let rec bind plicity (pat : AExpr.t) =
            match pat.v with
            | Var name -> add_var plicity pat.pos name
            | Ann (pat, _) -> bind plicity pat
            | Tuple _ | Record _ | Wild _ | Const _ -> AExpr.iter_children (bind plicity) pat
            | TupleT _ | RecordT _ | VariantT _ | RowT _ | PiT _ | ImpliT _ | PrimT _ -> ()
            | Fn _ | ImpliFn _ -> Env.report_error env {v = NonPattern pat; pos = pat.pos}
            | Focus _ | Select _ | App _ | PrimApp _ -> todo (Some pat.pos) in

        bind plicity pat

    let rec typeof_bound_pat _ env (_ : plicity) (pat : AExpr.t) : FExpr.pat =
        match pat.v with
        | Var name ->
            (match Env.find_val env name with
            | Some (var, _, _) -> FExpr.pat_at pat.pos var.vtyp (VarP var)
            | None -> bug (Some pat.pos) ~msg: "Env.find_val failed in bound pattern")

        | Const c ->
            let typ = const_typ c in
            FExpr.pat_at pat.pos typ (ConstP c)

        | _ -> todo (Some pat.pos)

    and typeof_pat ctrs env scope_builder add_var (plicity : plicity) (pat : AExpr.t) : FExpr.pat =
        match pat.v with
        | Ann (pat, typ) ->
            let typ = Kinding.check ctrs env (Env.some_type_kind env false) typ in
            (* TODO: let (_, typ) = Env.reabstract env typ in*)
            check_pat ctrs env scope_builder add_var plicity typ pat

        | Tuple pats ->
            let pats = pats |> Vector.map (typeof_pat ctrs env scope_builder add_var plicity) in
            let end_pos = snd pat.pos in
            let pat = pats |> Vector.fold_right (fun (acc : FExpr.pat) (pat : FExpr.pat) ->
                let span = (fst pat.ppos, end_pos) in
                FExpr.pat_at span (Pair {fst = pat.ptyp; snd = acc.ptyp})
                    (PairP {fst = pat; snd = acc})
            ) (FExpr.pat_at (end_pos, end_pos) (Prim Unit) (ConstP Unit)) in
            pat

        | Var name ->
            let var = Env.NonRecScope.Builder.var env scope_builder plicity name in
            add_var pat.pos name var;
            FExpr.pat_at pat.pos var.vtyp (VarP var)

        | Wild name ->
            let typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            FExpr.pat_at pat.pos typ (WildP name)

        | Const c ->
            let typ = const_typ c in
            FExpr.pat_at pat.pos typ (ConstP c)

        | PiT _ | ImpliT _ | TupleT _ | RecordT _ | VariantT _ | RowT _ | PrimT _ ->
            let {TS.typ = carrie; kind = _} = Kinding.elaborate ctrs env pat in
            FExpr.pat_at pat.pos (Proxy carrie) (ProxyP carrie)

        | Fn _ | ImpliFn _ ->
            Env.report_error env {v = NonPattern pat; pos = pat.pos};
            let typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            FExpr.pat_at pat.pos typ (WildP (Name.of_string ""))

        | Focus _ | App _ | PrimApp _ | Select _ | Record _ ->
            todo (Some pat.pos) ~msg: "in check_pat"

    and check_pat ctrs env scope_builder add_var plicity sub (pat : AExpr.t) : FExpr.pat =
        let pat = typeof_pat ctrs env scope_builder add_var plicity pat in
        let super = pat.ptyp in
        match Constraints.subtype ctrs pat.ppos env sub super with
        | Some coerce ->
            let f_expr = Coercer.reify pat.ppos sub coerce in
            FExpr.pat_at pat.ppos super (View (f_expr, pat))
        | None -> pat

(* # Expressions *)

    let rec typeof ctrs env (expr : AExpr.t) : FExpr.t typing = match expr.v with
        | Fn clauses | ImpliFn clauses ->
            let plicity = match expr.v with
                | Fn _ -> Util.Explicit
                | ImpliFn _ -> Implicit
                | _ -> unreachable (Some expr.pos) in
            let domain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let eff = match plicity with
                | Explicit -> T.Uv (Env.uv env false T.aRow)
                | Implicit -> EmptyRow in
            let codomain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let param = FExpr.fresh_var Explicit domain in

            let matchee = FExpr.at expr.pos domain (FExpr.use param) in
            let clauses = clauses
                |> Vector.map (check_clause ctrs env plicity ~domain ~eff ~codomain) in
            let body = FExpr.at expr.pos codomain (FExpr.match' matchee clauses) in

            let universals = Vector.empty in (* FIXME *)
            let typ = T.Pi {universals; domain; eff; codomain} in
            {term = FExpr.at expr.pos typ (FExpr.fn universals param body); eff = EmptyRow}

        | App exprs ->
            let len = Vector.length exprs in
            if len >= 2
            then begin
                let callee = Vector.get exprs 0 in
                let arg =
                    if len = 2
                    then Vector.get exprs 1
                    else {expr with v = AExpr.Tuple (Vector.sub exprs 1 (len - 1))} in
                (* TODO: Effect opening à la Koka *)
                let domain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
                let eff = T.Uv (Env.uv env false T.aRow) in
                let codomain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in

                (* OPTIMIZE: eta-expands implicit and universal callees: *)
                let callee_super = T.Pi {universals = Vector.empty; domain; eff; codomain} in
                let {TS.term = callee; eff = callee_eff} = check ctrs env callee_super callee in
                ignore (Constraints.unify ctrs callee.FExpr.pos env callee_eff eff);

                let {TS.term = arg; eff = arg_eff} = check ctrs env domain arg in
                ignore (Constraints.unify ctrs arg.pos env arg_eff eff);

                (* FIXME: Existential result opening *)
                {term = FExpr.at expr.pos codomain (FExpr.app callee Vector.empty arg); eff}
            end else todo (Some expr.pos) ~msg: "add error message"

        | PrimApp (Explicitly, args) ->
            let len = Vector.length args in
            if len >= 2 then begin
                let callee = Vector.get args 0 in
                let arg =
                    if len = 2
                    then Vector.get args 1
                    else {expr with v = AExpr.Tuple (Vector.sub args 1 (len - 1))} in
                let domain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
                let eff = T.EmptyRow in
                let codomain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in

                (* OPTIMIZE: eta-expands callees: *)
                let callee_super = T.Impli {universals = Vector.empty; domain; codomain} in
                let {TS.term = callee; eff = callee_eff} = check ctrs env callee_super callee in
                ignore (Constraints.unify ctrs callee.FExpr.pos env callee_eff eff);

                let {TS.term = arg; eff = arg_eff} = check ctrs env domain arg in
                ignore (Constraints.unify ctrs arg.pos env arg_eff eff);

                {term = FExpr.at expr.pos codomain (FExpr.app callee Vector.empty arg); eff}
            end else todo (Some expr.pos) ~msg: "add error message"

        | PrimApp ((Include | Require), _) -> todo (Some expr.pos) ~msg: "add error message"

        | PrimApp (Do, args) ->
            if Vector.length args = 1 then begin
                match (Vector.get args 0).v with
                | Record stmts ->
                    let (stmts, body) =
                        let len = Vector.length stmts in
                        if len > 0 then begin
                            match Vector.get stmts (len - 1) with
                            | Expr expr -> (Vector.sub stmts 0 (len - 1), expr)
                            | Def _ -> (stmts, {expr with v = Tuple Vector.empty})
                        end else (stmts, {expr with v = Tuple Vector.empty}) in
                    
                    let eff = T.Uv (Env.uv env false T.aRow) in
                    let (stmts, env) = check_stmts ctrs env eff stmts in
                    let {TS.term = body; eff = body_eff} = typeof ctrs env body in
                    ignore (Constraints.unify ctrs body.pos env body_eff eff);

                    {term = FExpr.at expr.pos body.typ (FExpr.let' stmts body); eff}

                | _ -> todo (Some expr.pos) ~msg: "add error message"
            end else todo (Some expr.pos) ~msg: "add error message"

        | PrimApp (Let, args) ->
            if Vector.length args = 1 then begin
                match (Vector.get args 0).v with
                | Record stmts ->
                    let (defs, body) =
                        let len = Vector.length stmts in
                        if len > 0 then begin
                            match Vector.get stmts (len - 1) with
                            | Expr expr -> (Vector.sub stmts 0 (len - 1), expr)
                            | Def _ -> (stmts, {expr with v = Tuple Vector.empty})
                        end else (stmts, {expr with v = Tuple Vector.empty}) in

                    let (defs, env) = check_rec ctrs env (fun _ _ _ -> ()) defs in
                    let {TS.term = body; eff} = typeof ctrs env body in

                    {term = FExpr.at expr.pos body.typ (FExpr.letrec defs body); eff}

                | _ -> todo (Some expr.pos) ~msg: "add error message"
            end else todo (Some expr.pos) ~msg: "add error message"
        | PrimApp (Module, args) ->
            if Vector.length args = 1 then begin
                match (Vector.get args 0).v with
                | Record defs ->
                    let fields = CCVector.create () in
                    let row = Stdlib.ref T.EmptyRow in
                    let add_var span label ({FExpr.name = _; vtyp; plicity = _} as var) =
                        CCVector.push fields (label, FExpr.at span vtyp (FExpr.use var));
                        Stdlib.(row := With {base = !row; label; field = vtyp}) in
                    let (defs, _) = check_rec ctrs env add_var defs in

                    let typ = Stdlib.(T.Record !row) in
                    let body = FExpr.at expr.pos typ (FExpr.record (Vector.build fields)) in
                    {term = FExpr.at expr.pos typ (FExpr.letrec defs body); eff = EmptyRow}

                | _ -> todo (Some expr.pos) ~msg: "add error message"
            end else todo (Some expr.pos) ~msg: "add error message"

        | PrimApp (Interface, _) -> typeof_proxy ctrs env expr

        | PrimApp (op, args) ->
            let check_iargs universals eff iargs =
                Stream.from (Source.zip_with (fun uv (iarg : AExpr.t) ->
                    let typ = T.Proxy uv in
                    let {TS.term = iarg; eff = arg_eff} = check ctrs env typ iarg in
                    ignore (Constraints.unify ctrs iarg.pos env arg_eff eff);
                    iarg
                ) (Vector.to_source universals) (Vector.to_source iargs))
                |> Stream.drain in

            let check_args domain eff args =
                Stream.from (Source.zip_with (fun typ (arg : AExpr.t) ->
                    let {TS.term = arg; eff = arg_eff} = check ctrs env typ arg in
                    ignore (Constraints.unify ctrs arg.pos env arg_eff eff);
                    arg
                ) (Vector.to_source domain) (Vector.to_source args))
                |> Stream.into (Vector.sink ()) in

            (* TODO: Effect opening à la Koka: *)
            (match primop_typ op with
            | Primop (op, universals, domain, eff, codomain) ->
                let (universals, domain, eff, codomain) =
                    Env.instantiate_primop env universals domain eff codomain in
                let universals = Vector.map (fun uv -> T.Uv uv) universals in
                let typs_arity = Vector.length universals in
                let vals_arity = Vector.length domain in

                let argc = Vector.length args in
                if argc = typs_arity + vals_arity then begin
                    check_iargs universals eff (Vector.sub args 0 typs_arity);
                    let args = check_args domain eff (Vector.sub args typs_arity vals_arity) in
                    {term = FExpr.at expr.pos codomain (FExpr.primapp op universals args); eff}
                end else if argc = vals_arity then begin
                    let args = check_args domain eff args in
                    {term = FExpr.at expr.pos codomain (FExpr.primapp op universals args); eff}
                end else begin
                    Env.report_error env {v = PrimAppArgc {op; expected = vals_arity; actual = argc}
                        ; pos = expr.pos};
                    {term = FExpr.at expr.pos codomain (FExpr.primapp op universals Vector.empty); eff}
                end

            | Branchop (op, universals, domain, eff, codomain) ->
                let check_clauses codomain eff typ (clauses_expr : AExpr.t) = (match clauses_expr.v with
                    | Fn clauses ->
                        if Vector.length clauses = Vector.length codomain then
                            Stream.from (Source.zip (Vector.to_source codomain) (Vector.to_source clauses))
                                |> Stream.map (fun (codomain, {AExpr.params; body}) ->
                                    let scope_builder = Env.NonRecScope.Builder.create () in
                                    let pat = check_pat ctrs env scope_builder (fun _ _ _ -> ())
                                        Explicit codomain params in
                                    let vpat = match pat.pterm with
                                        | VarP var -> Some var
                                        | ConstP Unit -> None
                                        | _ -> failwith "complex PrimBranch pattern" in
                                    let scope = Env.NonRecScope.Builder.build scope_builder pat.ppos pat None in
                                    let env = Env.push_nonrec env scope in

                                    let {TS.term = prim_body; eff = body_eff} = check ctrs env typ body in
                                    ignore (Constraints.unify ctrs body.pos env body_eff eff);

                                    {FExpr.res = vpat; prim_body})
                                |> Stream.into (Vector.sink ())
                        else todo (Some clauses_expr.pos) ~msg: "add error message"

                    | _ -> todo (Some clauses_expr.pos) ~msg: "add error message") in

                let (universals, domain, eff, codomain) =
                    Env.instantiate_branch env universals domain eff codomain in
                let universals = Vector.map (fun uv -> T.Uv uv) universals in
                let typs_arity = Vector.length universals in
                let vals_arity = Vector.length domain in

                let typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in

                let argc = Vector.length args in
                if argc = typs_arity + vals_arity + 1 then begin
                    check_iargs universals eff (Vector.sub args 0 typs_arity);
                    let clauses = Vector.get args (argc - 1) in
                    let args = check_args domain eff (Vector.sub args typs_arity vals_arity) in
                    let clauses = check_clauses codomain eff typ clauses in
                    {term = FExpr.at expr.pos typ (FExpr.primbranch op universals args clauses); eff}
                end else if argc = vals_arity + 1 then begin
                    let clauses = Vector.get args (argc - 1) in
                    let args = check_args domain eff args in
                    let clauses = check_clauses codomain eff typ clauses in
                    {term = FExpr.at expr.pos typ (FExpr.primbranch op universals args clauses); eff}
                end else begin
                    Env.report_error env {v = BranchopArgc {op; expected = vals_arity + 1; actual = argc}
                        ; pos = expr.pos};
                    {term = FExpr.at expr.pos typ (FExpr.primbranch op universals Vector.empty Vector.empty); eff}
                end)

        | Ann (expr, super) ->
            let super = Kinding.check ctrs env (Env.some_type_kind env false) super in
            check ctrs env super expr (* FIXME: handle abstract types, abstract type generation effect *)

        | Tuple exprs ->
            let eff = T.Uv (Env.uv env false T.aRow) in
            let exprs = exprs |> Vector.map (fun expr ->
                let {TS.term = expr; eff = expr_eff} = typeof ctrs env expr in
                ignore (Constraints.unify ctrs expr.pos env expr_eff eff);
                expr) in

            let end_pos = snd expr.pos in
            let term = exprs |> Vector.fold_right (fun (acc : FExpr.t) (expr : FExpr.t) ->
                FExpr.at (fst expr.pos, end_pos) (Pair {fst = expr.typ; snd = acc.typ})
                    (FExpr.pair expr acc)
            ) (FExpr.at expr.pos (Prim Unit) (FExpr.const Unit)) in
            {term; eff}

        | Focus (focusee, index) ->
            let fst_typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let snd_typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let focusee_typ = T.Pair {fst = fst_typ; snd = snd_typ} in
            let {TS.term = focusee; eff} = check ctrs env focusee_typ focusee in

            let rec get focusee = function
                | 0 -> FExpr.at expr.pos fst_typ (FExpr.fst focusee)
                | index ->
                    let focusee = FExpr.at expr.pos snd_typ (FExpr.snd focusee) in
                    get focusee (index - 1) in
            {term = get focusee index; eff}

        | Record stmts ->
            let fields = CCVector.create () in
            let eff = T.Uv (Env.uv env false T.aRow) in
            let typ = T.Record (Vector.fold (fun base -> function
                | AStmt.Def (_, {v = Var label; _}, expr) ->
                    let {TS.term; eff = eff'} = typeof ctrs env expr in
                    CCVector.push fields (label, term);
                    ignore (Constraints.unify ctrs expr.pos env eff' eff);
                    T.With {base; label; field = term.typ}
                | _ -> bug (Some expr.pos) ~msg: "bad record field reached typechecker"
            ) T.EmptyRow stmts) in
            {term = FExpr.at expr.pos typ (FExpr.record (Vector.build fields)); eff }

        | Select (selectee, label) -> (* TODO: lacks-constraint: *)
            let base = T.Uv (Env.uv env false T.aRow) in
            let typ = T.Uv (Env.uv env false T.aType) in
            let selectee_typ = T.Record (With {base; label; field = typ}) in
            let {TS.term = selectee; eff} = check ctrs env selectee_typ selectee in
            {term = FExpr.at expr.pos typ (FExpr.select selectee label); eff}

        | Var name ->
            let span = expr.pos in

            (*let rec find = function
                | Env.Vals kvs :: scopes -> (match Name.Map.find_opt name kvs with
                    | Some var -> FExpr.at span var.vtyp (FExpr.use var)
                    | None -> find scopes)

                | (Row bindings :: scopes') as scopes ->
                    (match Name.Map.find_opt name bindings with
                    | Some (var, binding) ->
                        (match !binding with
                        | WhiteT (lhs, rhs) ->
                            let env = {env with scopes} in
                            binding := GreyT;
                            let {TS.typ = rhs; kind} = Kinding.elaborate ctrs env rhs in
                            let (_, rhs) = Env.reabstract env rhs in
                            ignore (Constraints.subtype ctrs span env rhs lhs);
                            binding := BlackT {typ = rhs; kind}
                        | GreyT -> () (* TODO: really? *)
                        | BlackT _ -> ());
                        FExpr.at span var.vtyp (FExpr.use var)
                    | None -> find scopes')

                | (Rigid _ | Hoisting _) :: scopes -> find scopes

                | [] ->
                    (match Option.bind (Env.namespace env) (Fun.flip Namespace.find_typ name) with
                    | Some {vtyp = typ; plicity = _; name = _} ->
                        let namexpr = FExpr.at span (Prim String)
                            (FExpr.const (String (Name.to_string name))) in
                        FExpr.primapp GlobalGet (Vector.singleton typ) (Vector.singleton namexpr)
                        |> FExpr.at span typ
                    | None ->
                        Env.report_error env ({v = Unbound name; pos = span});
                        (* FIXME: levels: *)
                        let typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
                        FExpr.at span typ (FExpr.use (FExpr.var Explicit name typ))) in*)

            let term =
                match Env.find_val env name with
                | Some (var, binding, env) ->
                    (match !binding with
                    | Env.White {span; pat; expr} -> check_binding ctrs env binding span pat expr
                    | Grey _ | Black _ -> ());
                    FExpr.at span var.vtyp (FExpr.use var)

                | None -> 
                    (match Option.bind (Env.namespace env) (Fun.flip Namespace.find_typ name) with
                    | Some {vtyp = typ; plicity = _; name = _} ->
                        let namexpr = FExpr.at span (Prim String)
                            (FExpr.const (String (Name.to_string name))) in
                        FExpr.primapp GlobalGet (Vector.singleton typ) (Vector.singleton namexpr)
                        |> FExpr.at span typ
                    | None ->
                        Env.report_error env ({v = Unbound name; pos = span});
                        (* FIXME: levels: *)
                        let typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
                        FExpr.at span typ (FExpr.use (FExpr.var Explicit name typ))) in

            {term; eff = EmptyRow}

        | Const c ->
            let typ = const_typ c in
            {term = FExpr.at expr.pos typ (FExpr.const c); eff = EmptyRow}

        | PiT _ | ImpliT _ | TupleT _ | RecordT _ | VariantT _ | RowT _ | PrimT _ ->
            typeof_proxy ctrs env expr

        | Wild _ -> bug (Some expr.pos) ~msg: "_-expression reached typechecker"

    and check ctrs env super expr =
        let {TS.term = expr; eff} = typeof ctrs env expr in
        let coerce = Constraints.subtype ctrs expr.pos env expr.typ super in
        {TS.term = Coercer.apply_opt coerce expr; eff}

    and check_clause ctrs env plicity ~domain ~eff ~codomain {params; body} =
        let module ScopeBuilder = Env.NonRecScope.Builder in

        let scope_builder = ScopeBuilder.create () in
        let pat = check_pat ctrs env scope_builder (fun _ _ _ -> ()) plicity domain params in
        let scope = ScopeBuilder.build scope_builder pat.ppos pat None in
        let env = Env.push_nonrec env scope in

        (* FIXME: abstract type creation, type creation effect: *)
        let {TS.term = body; eff = body_eff} = check ctrs env codomain body in
        ignore (Constraints.unify ctrs body.pos env body_eff eff);
        {pat; body}

    and typeof_proxy ctrs env expr =
        let {TS.typ = carrie; kind = _} = Kinding.elaborate ctrs env expr in
        {TS.term = FExpr.at expr.pos (Proxy carrie) (FExpr.proxy carrie); eff = EmptyRow}

(* # Bindings *)

    and check_binding ctrs env (binding : Env.val_binding Tx.Ref.t) span pat expr =
        binding := Grey {span; pat; expr};
        let pat = typeof_bound_pat ctrs env Explicit pat in
        (* FIXME: sealing, abstract type generation effect: *)
        let {TS.term = expr; eff} = check ctrs env pat.ptyp expr in
        ignore (Constraints.unify ctrs expr.pos env eff T.EmptyRow);
        binding := Black {span; pat; expr = Some expr}

(* # Definitions *)
 
    and check_defs ctrs env defs =
        let module ScopeBuilder = Env.RecScope.Builder in

        (* Push variables: *)
        let scope_builder = ScopeBuilder.create () in
        let bindings = defs |> Vector.map (fun (span, pat, expr) ->
            let binding = ScopeBuilder.binding scope_builder span pat expr in
            bind_pat env Explicit pat (fun plicity _ name ->
                ignore (ScopeBuilder.var env scope_builder binding plicity name)
            );
            binding
        ) in
        let env = Env.push_rec env (ScopeBuilder.build scope_builder) in

        (* Check defs and their effects: *)
        let defs = bindings |> Vector.map (fun binding ->
            match !binding with
            | Env.White {span; pat; expr} ->
                check_binding ctrs env binding span pat expr;
                (match !binding with
                | Black {span; pat; expr = Some expr} -> (span, pat, expr)
                | _ -> unreachable (Some span))
            | Grey {span; _} -> unreachable (Some span)
            | Black {span; pat; expr = Some expr} -> (span, pat, expr)
            | Black {span; pat = _; expr = None} -> bug (Some span)
        ) in

        (defs, env)

(* # Statements *)

    and check_stmt ctrs env eff = function
        | AStmt.Def (span, pat, expr) ->
            let module ScopeBuilder = Env.NonRecScope.Builder in

            let scope_builder = ScopeBuilder.create () in
            let pat = typeof_pat ctrs env scope_builder (fun _ _ _ -> ()) Explicit pat in

            (* FIXME: sealing, abstract type creation effect: *)
            let {TS.term = expr; eff = stmt_eff} = check ctrs env pat.ptyp expr in
            ignore (Constraints.unify ctrs expr.pos env stmt_eff eff);

            let scope = ScopeBuilder.build scope_builder span pat (Some expr) in
            (Env.push_nonrec env scope, FStmt.Def (span, pat, expr))

        | Expr expr ->
            let {TS.term = expr; eff = stmt_eff} = typeof ctrs env expr in
            ignore (Constraints.unify ctrs expr.pos env stmt_eff eff);
            (env, Expr expr)

    and check_stmts ctrs env eff stmts =
        let stmts' = CCVector.create () in
        let env = stmts |> Vector.fold (fun env stmt ->
            let (env, stmt) = check_stmt ctrs env eff stmt in
            CCVector.push stmts' stmt;
            env
        ) env in
        (Vector.build stmts', env)

    and check_rec ctrs env add_var (stmts : AStmt.t Vector.t) =
        let module ScopeBuilder = Env.RecScope.Builder in

        (* Push variables: *)
        let scope_builder = ScopeBuilder.create () in
        let bindings = stmts |> Vector.map (function
            | AStmt.Def (span, pat, expr) ->
                let binding = ScopeBuilder.binding scope_builder span pat expr in
                bind_pat env Explicit pat (fun plicity span name ->
                    let var = ScopeBuilder.var env scope_builder binding plicity name in
                    add_var span name var
                );
                binding
            | Expr expr -> todo (Some expr.pos) ~msg: "add error message"
        ) in
        let env = Env.push_rec env (ScopeBuilder.build scope_builder) in

        (* Check defs and their effects: *)
        let defs = bindings |> Vector.map (fun binding ->
            match !binding with
            | Env.White {span; pat; expr} ->
                let pat = typeof_bound_pat ctrs env Explicit pat in
                let {TS.term = expr; eff} = check ctrs env pat.ptyp expr in
                ignore (Constraints.unify ctrs expr.pos env eff T.EmptyRow);
                (span, pat, expr)
            | Grey {span; _} -> unreachable (Some span)
            | Black {span; pat; expr = Some expr} -> (span, pat, expr)
            | Black {span; pat = _; expr = None} -> bug (Some span)
        ) in

        (defs, env)

(* # Top-level APIs *)

(* ## Programs *)

    let check_program errors ctrs {Ast.Program.span = _; defs; body} =
        let env = Env.with_error_handler Env.empty
            (fun error -> errors := error :: !errors) in

        let (defs, env) = check_defs ctrs env defs in
        let {TS.term = main; eff} = check ctrs env (Prim Unit) body in

        {TS.term = {Fc.Program.type_fns = Env.type_fns env; defs; main}; eff}

(* ## REPL Interactions *)

    let check_interactive_stmt : ctrs -> Env.t -> FStmt.t CCVector.vector -> AStmt.t -> Env.t * eff
    = fun ctrs env stmts' -> function
        | Def (span, pat, expr) ->
            let module ScopeBuilder = Env.NonRecScope.Builder in

            let vars = CCVector.create () in
            let add_var _ _ var = CCVector.push vars var in

            let scope_builder = ScopeBuilder.create () in
            let pat = typeof_pat ctrs env scope_builder add_var Explicit pat in

            (* FIXME: sealing, abstract type creation effect: *)
            let {TS.term = expr; eff} = check ctrs env pat.ptyp expr in

            CCVector.push stmts' (Def (span, pat, expr));
            vars |> CCVector.iter (fun ({FExpr.vtyp = typ; _} as var) ->
                let namexpr = FExpr.at span (Prim String)
                    (FExpr.const (String (Name.to_string var.name))) in
                let global_init = FExpr.at span (Prim Unit)
                    (FExpr.primapp GlobalSet (Vector.singleton typ)
                        (Vector.of_array_unsafe [|namexpr; FExpr.at span typ (FExpr.use var)|])) in
                CCVector.push stmts' (Expr global_init));

            let scope = ScopeBuilder.build scope_builder span pat (Some expr) in
            (Env.push_nonrec env scope, eff)

        | Expr expr ->
            let {TS.term = expr; eff} = typeof ctrs env expr in

            CCVector.push stmts' (Expr expr);

            (env, eff)

    let check_interactive_stmts ns errors ctrs stmts =
        let env = Env.with_error_handler (Env.toplevel ns)
            (fun error -> errors := error :: !errors) in

        let span =
            let (start, _) = AStmt.pos (Vector1.get stmts 0) in
            let (_, stop) = AStmt.pos (Vector1.get stmts (Vector1.length stmts - 1)) in
            (start, stop) in

        let stmts' = CCVector.create () in
        let eff = T.Uv (Env.uv env false T.aRow) in
        let env = Vector1.fold (fun env stmt ->
            let (env, stmt_eff) = check_interactive_stmt ctrs env stmts' stmt in
            ignore (Constraints.unify ctrs span env stmt_eff eff);
            env
        ) env stmts in

        let stmts = Vector.build stmts' in
        let main =
            let (stmts, body) =
                if Vector.length stmts > 0
                then match Vector.get stmts (Vector.length stmts - 1) with
                    | Expr expr -> (Vector.sub stmts 0 (Vector.length stmts - 1), expr)
                    | _ -> (stmts, FExpr.at span (Prim Unit) (FExpr.const Unit))
                else (stmts, FExpr.at span (Prim Unit) (FExpr.const Unit)) in
            FExpr.at span body.typ (FExpr.let' stmts body) in
        ( { TS.term = { Fc.Program.type_fns = Vector.empty (* FIXME *)
                       ; defs = Vector.empty; main }
          ; eff }
        , Env.namespace env |> Option.get )
end

