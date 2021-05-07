open Streaming

open Asserts
type 'a with_pos = 'a Util.with_pos
type plicity = Util.plicity

module TS = TyperSigs
module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module T = Fc.Type
module FStmt = Fc.Term.Stmt
module FExpr = Fc.Term.Expr
module Coercer = Fc.Term.Coercer
module Env = TypeEnv
type eff = T.t
type 'a typing = 'a TyperSigs.typing
type ctrs = Constraint.queue
open Transactional.Ref

module Make
    (Constraints : TS.CONSTRAINTS)
    (Kinding : TS.KINDING)
= struct
    let const_typ (c : Const.t) = T.Prim (match c with
        | Unit -> Unit
        | Int _ -> Int
        | String _ -> String)

    let primop_typ : Primop.t -> T.t Vector.t * T.t Vector.t * T.t * T.t =
        let open Primop in
        function
        | Pair -> (* forall a b . (a, b) -> Pair a b *)
            ( Vector.of_array_unsafe [|T.aType; T.aType|]
            , Vector.of_array_unsafe [|T.Bv {depth = 0; sibli = 0; bkind = T.aType}
                ; Bv {depth = 0; sibli = 1; bkind = T.aType}|]
            , T.EmptyRow
            , Pair {fst = Bv {depth = 0; sibli = 0; bkind = T.aType}
                ; snd = Bv {depth = 0; sibli = 1; bkind = T.aType}} )
        | Fst -> (* forall a b . Pair a b -> a *)
            ( Vector.of_array_unsafe [|T.aType; T.aType|]
            , Vector.singleton (T.Pair {fst = Bv {depth = 0; sibli = 0; bkind = T.aType}
                ; snd = Bv {depth = 0; sibli = 1; bkind = T.aType}})
            , T.EmptyRow
            , Bv {depth = 0; sibli = 0; bkind = T.aType} )
        | Snd -> (* forall a b . Pair a b -> b *)
            ( Vector.of_array_unsafe [|T.aType; T.aType|]
            , Vector.singleton (T.Pair {fst = Bv {depth = 0; sibli = 0; bkind = T.aType}
                ; snd = Bv {depth = 0; sibli = 1; bkind = T.aType}})
            , T.EmptyRow
            , Bv {depth = 0; sibli = 1; bkind = T.aType} )
        | CellNew -> (* forall a . () -> __cell a *)
            ( Vector.singleton T.aType, Vector.empty
            , T.EmptyRow
            , T.App {callee = Prim Cell; arg = Bv {depth = 0; sibli = 0; bkind = T.aType}} )
        | CellInit -> (* forall a . (__cell a, a) -> () *)
            ( Vector.singleton T.aType
            , Vector.of_list [ T.App {callee = Prim Cell; arg = Bv {depth = 0; sibli = 0; bkind = T.aType}}
                ; Bv {depth = 0; sibli = 0; bkind = T.aType} ]
            , T.EmptyRow, Prim Unit )
        | CellGet -> (* forall a . __cell a -> a *)
            ( Vector.singleton T.aType
            , Vector.singleton (T.App {callee = Prim Cell; arg = Bv {depth = 0; sibli = 0; bkind = T.aType}})
            , T.EmptyRow, T.Bv {depth = 0; sibli = 0; bkind = T.aType} )

        | Int -> (Vector.empty, Vector.singleton (T.Prim Unit), T.EmptyRow, T.Proxy (Prim Int))
        | String -> (Vector.empty, Vector.singleton (T.Prim Unit), T.EmptyRow, T.Proxy (Prim String))

        | Type ->
            ( Vector.empty, Vector.singleton (T.Prim Unit), T.EmptyRow
            , T.Proxy (T.Exists {existentials = Vector1.singleton T.aType
                ; body = Proxy (Bv {depth = 0; sibli = 0; bkind = T.aType})}) )

        | TypeOf -> (* FIXME: Enforce argument purity *)
            ( Vector.singleton T.aType
            , Vector.singleton (T.Bv {depth = 0; sibli = 0; bkind = T.aType})
            , EmptyRow, Proxy (Bv {depth = 0; sibli = 0; bkind = T.aType}) )
        | Import ->
            ( Vector.singleton T.aType
            , Vector.of_list [T.Proxy (Bv {depth = 0; sibli = 0; bkind = T.aType}); Prim String]
            , EmptyRow, Bv {depth = 0; sibli = 0; bkind = T.aType} )
        | GlobalSet ->
            ( Vector.singleton T.aType
            , Vector.of_list [T.Prim String; Bv {depth = 0; sibli = 0; bkind = T.aType}]
            , EmptyRow, Prim Unit )
        | GlobalGet ->
            ( Vector.singleton T.aType
            , Vector.singleton (T.Prim String)
            , EmptyRow, Bv {depth = 0; sibli = 0; bkind = T.aType} )

    (*let branchop_typ : Branchop.t -> T.t Vector.t * T.t Vector.t * T.t * T.t Vector.t =
        let open Branchop in
        function
        | IAdd | ISub | IMul | IDiv ->
            ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
            , T.EmptyRow, Vector.of_list [T.Prim Int; Prim Unit] )
        | ILt | ILe | IGt | IGe | IEq ->
            ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
            , T.EmptyRow, Vector.of_list [T.Prim Unit; Prim Unit] )*)

    let rec typeof_pat ctrs is_global is_fwd env (plicity : plicity) (pat : AExpr.t with_pos) =
        match pat.v with
        | Ann (pat, typ) ->
            let typ = Kinding.check ctrs env (Env.some_type_kind env false) typ in
            (* TODO: let (_, typ) = Env.reabstract env typ in*)
            check_pat ctrs is_global is_fwd env plicity typ pat

        | Tuple pats ->
            (match Vector.length pats with
            | 0 -> (FExpr.pat_at pat.pos (Prim Unit) (ConstP Unit), env, Vector.empty)
            | 2 ->
                let (fst_pat, env, fst_vars) =
                    typeof_pat ctrs is_global is_fwd env plicity (Vector.get pats 0) in
                let (snd_pat, env, snd_vars) =
                    typeof_pat ctrs is_global is_fwd env plicity (Vector.get pats 1) in
                ( FExpr.pat_at pat.pos (Pair {fst = fst_pat.ptyp; snd = snd_pat.ptyp})
                    (PairP {fst = fst_pat; snd = snd_pat})
                , env, Vector.append fst_vars snd_vars )
            | _ -> unreachable (Some pat.pos))

        | Proxy carrie ->
            let {TS.typ = carrie; kind = _} = Kinding.elaborate ctrs env {v = carrie; pos = pat.pos} in
            (FExpr.pat_at pat.pos (Proxy carrie) (ProxyP carrie), env, Vector.empty)

        | Var name ->
            let typ = T.Uv (Env.uv env is_fwd (Env.some_type_kind env false)) in
            let var = FExpr.var plicity name typ in
            ( FExpr.pat_at pat.pos typ (VarP var)
            , Env.push_val is_global env var
            , Vector.singleton var )

        | Wild name ->
            let typ = T.Uv (Env.uv env is_fwd (Env.some_type_kind env false)) in
            (FExpr.pat_at pat.pos typ (WildP name), env, Vector.empty)

        | Const c ->
            let typ = const_typ c in
            (FExpr.pat_at pat.pos typ (ConstP c), env, Vector.empty)

        | Fn _ ->
            Env.report_error env {v = NonPattern pat; pos = pat.pos};
            let typ = T.Uv (Env.uv env is_fwd (Env.some_type_kind env false)) in
            (FExpr.pat_at pat.pos typ (WildP (Name.of_string "")), env, Vector.empty)

        | AppSequence _ -> bug (Some pat.pos) ~msg: "typechecker encountered AppSequence pattern"

        | Focus _ | Let _ | App _ | PrimApp _ | PrimBranch _ | Select _ | Record _ ->
            todo (Some pat.pos) ~msg: "in check_pat"

    and check_pat ctrs is_global is_fwd env plicity sub (pat : AExpr.t with_pos) =
        let (pat, env, vars) = typeof_pat ctrs is_global is_fwd env plicity pat in
        let super = pat.ptyp in
        match Constraints.subtype ctrs pat.ppos env sub super with
        | Some coerce ->
            let f_expr = Coercer.reify pat.ppos sub coerce in
            (FExpr.pat_at pat.ppos super (View (f_expr, pat)), env, vars)
        | None -> (pat, env, vars)

    let rec typeof ctrs env (expr : AExpr.t with_pos) : FExpr.t typing = match expr.v with
        | Fn (plicity, clauses) ->
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

        | App (callee, Explicit, arg) ->
            (* TODO: Effect opening à la Koka *)
            (* OPTIMIZE: eta-expands universal callees: *)
            let domain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let eff = T.Uv (Env.uv env false T.aRow) in
            let codomain = T.Uv (Env.uv env false (Env.some_type_kind env false)) in

            let callee_super = T.Pi {universals = Vector.empty; domain; eff; codomain} in
            let {TS.term = callee; eff = callee_eff} = check ctrs env callee_super callee in
            ignore (Constraints.unify ctrs callee.FExpr.pos env callee_eff eff);

            let {TS.term = arg; eff = arg_eff} = check ctrs env domain arg in
            ignore (Constraints.unify ctrs arg.pos env arg_eff eff);

            (* FIXME: Existential result opening *)
            {term = FExpr.at expr.pos codomain (FExpr.app callee Vector.empty arg); eff}

        | PrimApp (op, iargs, args) ->
            let (universals, domain, eff, codomain) = primop_typ op in
            let (universals, domain, eff, codomain) =
                Env.instantiate_primop env universals domain eff codomain in
            let universals = Vector.map (fun uv -> T.Uv uv) universals in

            let expected = Vector.length domain in
            let actual = Vector.length args in
            if actual = expected then begin
                if Vector.length iargs > 0 then begin
                    let expected = Vector.length universals in
                    let actual = Vector.length iargs in
                    if actual = expected
                    then Stream.from (Source.zip_with (fun uv (iarg : AExpr.t with_pos) ->
                            let typ = T.Proxy uv in
                            let {TS.term = iarg; eff = arg_eff} = check ctrs env typ iarg in
                            ignore (Constraints.unify ctrs iarg.pos env arg_eff eff);
                            iarg
                        ) (Vector.to_source universals) (Vector.to_source iargs))
                        |> Stream.drain
                    else Env.report_error env {v = PrimAppIArgc {op; expected; actual}; pos = expr.pos}
                end;
                (* else type arguments are inferred *)

                let args = Stream.from (Source.zip_with (fun typ (arg : AExpr.t with_pos) ->
                        let {TS.term = arg; eff = arg_eff} = check ctrs env typ arg in
                        ignore (Constraints.unify ctrs arg.pos env arg_eff eff);
                        arg
                    ) (Vector.to_source domain) (Vector.to_source args))
                    |> Stream.into (Vector.sink ()) in
                {term = FExpr.at expr.pos codomain (FExpr.primapp op universals args); eff}
            end else begin
                Env.report_error env {v = PrimAppArgc {op; expected; actual}; pos = expr.pos};
                {term = FExpr.at expr.pos codomain (FExpr.primapp op universals Vector.empty); eff}
            end

        | Let (defs, body) ->
            let (defs, env) = check_defs ctrs env (Vector1.to_vector defs) in
            let {TS.term = body; eff} = typeof ctrs env body in
            {term = FExpr.at expr.pos body.typ (FExpr.letrec defs body); eff}

        | Ann (expr, super) ->
            let super = Kinding.check ctrs env (Env.some_type_kind env false) super in
            check ctrs env super expr (* FIXME: handle abstract types, abstract type generation effect *)

        | Tuple exprs ->
            (match Vector.length exprs with
            | 0 -> {term = FExpr.at expr.pos (Prim Unit) (FExpr.const Unit); eff = EmptyRow}
            | 2 ->
                let eff = T.Uv (Env.uv env false T.aRow) in
                let {TS.term = fst; eff = fst_eff} = typeof ctrs env (Vector.get exprs 0) in
                ignore (Constraints.unify ctrs expr.pos env fst_eff eff);
                let {TS.term = snd; eff = snd_eff} = typeof ctrs env (Vector.get exprs 1) in
                ignore (Constraints.unify ctrs expr.pos env snd_eff eff);
                { term = FExpr.at expr.pos (Pair {fst = fst.typ; snd = snd.typ}) (FExpr.pair fst snd)
                ; eff}
            | _ -> unreachable (Some expr.pos))

        | Focus (focusee, index) ->
            let fst_typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let snd_typ = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
            let focusee_typ = T.Pair {fst = fst_typ; snd = snd_typ} in
            let {TS.term = focusee; eff} = check ctrs env focusee_typ focusee in

            (match index with
            | 0 -> {term = FExpr.at expr.pos fst_typ (FExpr.fst focusee); eff}
            | 1 -> {term = FExpr.at expr.pos snd_typ (FExpr.snd focusee); eff}
            | _ -> unreachable (Some expr.pos))

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

        | Proxy carrie ->
            let {TS.typ = carrie; kind = _} = Kinding.elaborate ctrs env {v = carrie; pos = expr.pos} in
            {term = FExpr.at expr.pos (Proxy carrie) (FExpr.proxy carrie); eff = EmptyRow}

        | Var name ->
            let term = Env.find_val (fun env typ ->
                    let {TS.typ; kind} = Kinding.elaborate ctrs env typ in
                    (typ, kind))
                (fun span env sub super -> ignore (Constraints.subtype ctrs span env sub super))
                env expr.pos name in
            {term; eff = EmptyRow}

        | Const c ->
            let typ = const_typ c in
            {term = FExpr.at expr.pos typ (FExpr.const c); eff = EmptyRow}

        | Wild _ -> bug (Some expr.pos) ~msg: "_-expression reached typechecker"
        | AppSequence _ -> bug (Some expr.pos) ~msg: "AppSequence expression reached typechecker"

        | _ -> todo (Some expr.pos)

    and check ctrs env super expr =
        let {TS.term = expr; eff} = typeof ctrs env expr in
        let coerce = Constraints.subtype ctrs expr.pos env expr.typ super in
        {TS.term = Coercer.apply_opt coerce expr; eff}

    and check_clause ctrs env plicity ~domain ~eff ~codomain {params; body} =
        (* OPTIMIZE: Don't make vars vector to be just ignored here: *)
        let (pat, env, _) = check_pat ctrs false false env plicity domain params in
        (* FIXME: abstract type creation, type creation effect: *)
        let {TS.term = body; eff = body_eff} = check ctrs env codomain body in
        ignore (Constraints.unify ctrs body.pos env body_eff eff);
        {pat; body}

    and check_defs ctrs env defs =
        let pats = CCVector.create () in
        let env = Vector.fold (fun env (_, pat, _) ->
            let (pat, env, _) = typeof_pat ctrs false true env Explicit pat in
            CCVector.push pats pat;
            env
        ) env defs in
        let pats = Vector.build pats in
        let defs = Source.zip_with (fun (pat : FExpr.pat) (span, _, expr) ->
                (* FIXME: generate abstract types, abstract type generaiton effect: *)
                let {TS.term = expr; eff} = check ctrs env pat.ptyp expr in
                ignore (Constraints.unify ctrs expr.pos env eff T.EmptyRow);
                (span, pat, expr)
            ) (Vector.to_source pats) (Vector.to_source defs)
            |> Stream.from |> Stream.into (Vector.sink ()) in
        (defs, env)

    let check_program errors ctrs defs main =
        let env = Env.with_error_handler Env.empty
            (fun error -> errors := error :: !errors) in

        let (defs, env) = check_defs ctrs env defs in
        let {TS.term = main; eff} = check ctrs env (Prim Unit) main in

        {TS.term = {Fc.Program.type_fns = Env.type_fns env; defs; main}; eff}

    let check_interactive_stmt : ctrs -> Env.t -> FStmt.t CCVector.vector -> AStmt.t -> Env.t * eff
    = fun ctrs env stmts' -> function
        | Def (span, pat, expr) ->
            let (pat, env', vars) = typeof_pat ctrs true false env Explicit pat in
            let {TS.term = expr; eff} = check ctrs env pat.ptyp expr in
            CCVector.push stmts' (Def (span, pat, expr));
            vars |> Vector.iter (fun ({FExpr.vtyp = typ; _} as var) ->
                let namexpr = FExpr.at span (Prim String)
                    (FExpr.const (String (Name.to_string var.name))) in
                let global_init = FExpr.at span (Prim Unit)
                    (FExpr.primapp GlobalSet (Vector.singleton typ)
                        (Vector.of_array_unsafe [|namexpr; FExpr.at span typ (FExpr.use var)|])) in
                CCVector.push stmts' (Expr global_init));
            (env', eff)

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

