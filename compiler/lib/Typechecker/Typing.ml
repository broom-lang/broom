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

module Make (K : TS.KINDING) (Constraints : TS.CONSTRAINTS) = struct
    let unify = Constraints.unify
    let subtype = Constraints.subtype

    let const_typ (c : Const.t) = T.Prim (match c with
        | Int _ -> Int
        | String _ -> String)

    let rec typeof_pat ctrs is_global is_fwd env (plicity : plicity) (pat : AExpr.t with_pos) =
        match pat.v with
        | Ann (pat, typ) ->
            let kind = T.App {callee = Prim TypeIn; arg = Uv (Env.uv env false T.rep)} in
            let typ = K.check env kind typ in
            (* TODO: let (_, typ) = Env.reabstract env typ in*)
            check_pat ctrs is_global is_fwd env plicity typ pat

        | Tuple pats ->
            let pats' = CCVector.create () in
            let vars = CCVector.create () in
            let env = Vector.fold (fun env pat ->
                let (pat, env, pat_vars) = typeof_pat ctrs is_global is_fwd env plicity pat in
                CCVector.push pats' pat;
                Vector.iter (CCVector.push vars) pat_vars;
                env
            ) env pats in
            let pats = Vector.build pats' in
            let vars = Vector.build vars in
            let typs = Vector.map (fun (pat : FExpr.pat) -> pat.ptyp) pats in
            (FExpr.pat_at pat.pos (Tuple typs) (TupleP pats), env, vars)

        | Var name ->
            let kind = T.App {callee = Prim TypeIn; arg = Uv (Env.uv env false T.rep)} in
            let typ = T.Uv (Env.uv env is_fwd kind) in
            let var = FExpr.var plicity name typ in
            ( FExpr.pat_at pat.pos typ (VarP var)
            , Env.push_val is_global env var
            , Vector.singleton var )

        | Wild name ->
            let kind = T.App {callee = Prim TypeIn; arg = Uv (Env.uv env false T.rep)} in
            let typ = T.Uv (Env.uv env is_fwd kind) in
            (FExpr.pat_at pat.pos typ (WildP name), env, Vector.empty)

        | Const c ->
            let typ = const_typ c in
            (FExpr.pat_at pat.pos typ (ConstP c), env, Vector.empty)

        | _ -> todo (Some pat.pos)

    and check_pat _ _ _ _ _ _ (pat : AExpr.t with_pos) = todo (Some pat.pos)

    let rec typeof ctrs env (expr : AExpr.t with_pos) : FExpr.t typing = match expr.v with
        | Let (defs, body) ->
            let (defs, env) = check_defs ctrs env (Vector1.to_vector defs) in
            let {TS.term = body; eff} = typeof ctrs env body in
            {term = FExpr.at expr.pos body.typ (FExpr.letrec (Vector.to_array defs) body); eff}

        | Ann (expr, super) ->
            let super = K.check env (App {callee = Prim TypeIn; arg = Uv (Env.uv env false T.rep)}) super in
            check ctrs env super expr (* FIXME: handle abstract types, abstract type generation effect *)

        | Tuple exprs ->
            let eff = T.Uv (Env.uv env false T.aRow) in
            let exprs = exprs |> Vector.map (fun expr ->
                let {TS.term; eff = eff'} = typeof ctrs env expr in
                ignore (Constraints.unify ctrs expr.pos env eff' eff);
                term) in
            let typ = T.Tuple (Vector.map (fun {FExpr.typ; _} -> typ) exprs) in
            {term = FExpr.at expr.pos typ (FExpr.tuple (Vector.to_array exprs)); eff}

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
            {term = FExpr.at expr.pos typ (FExpr.record (CCVector.to_array fields)); eff }

        | Select (selectee, label) -> (* TODO: lacks-constraint: *)
            let base = T.Uv (Env.uv env false T.aRow) in
            let typ = T.Uv (Env.uv env false T.aType) in
            let selectee_typ = T.Record (With {base; label; field = typ}) in
            let {TS.term = selectee; eff} = check ctrs env selectee_typ selectee in
            {term = FExpr.at expr.pos typ (FExpr.select selectee label); eff}

        | Proxy carrie ->
            let carrie = K.elaborate env {v = carrie; pos = expr.pos} in
            {term = FExpr.at expr.pos (Proxy carrie) (FExpr.proxy carrie); eff = EmptyRow}

        | Var name -> {term = Env.find_val env expr.pos name; eff = EmptyRow}

        | Const c ->
            let typ = const_typ c in
            {term = FExpr.at expr.pos typ (FExpr.const c); eff = EmptyRow}

        | Wild _ -> bug (Some expr.pos) ~msg: "_-expression reached typechecker"
        | AppSequence _ -> bug (Some expr.pos) ~msg: "AppSequence expression reached typechecker"

        | _ -> todo (Some expr.pos)

    and check ctrs env super expr =
        let {TS.term = expr; eff} = typeof ctrs env expr in
        let coerce = subtype ctrs expr.pos env expr.typ super in
        {TS.term = Coercer.apply_opt coerce expr; eff}

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
        let {TS.term = main; eff} = check ctrs env (T.Tuple Vector.empty) main in

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
                let global_init = FExpr.at span (Tuple Vector.empty)
                    (FExpr.primapp GlobalSet (Vector.singleton typ)
                        (FExpr.at span (Tuple Vector.empty)
                        (FExpr.tuple [|namexpr; FExpr.at span typ (FExpr.use var)|]))) in
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
            ignore (unify ctrs span env stmt_eff eff);
            env
        ) env stmts in

        let stmts = CCVector.to_array stmts' in
        let main =
            let (stmts, body) =
                if Array.length stmts > 0
                then match Array.get stmts (Array.length stmts - 1) with
                    | Expr expr -> (Array.sub stmts 0 (Array.length stmts - 1), expr)
                    | _ -> (stmts, FExpr.at span (Tuple Vector.empty) (FExpr.tuple [||]))
                else (stmts, FExpr.at span (Tuple Vector.empty) (FExpr.tuple [||])) in
            FExpr.at span body.typ (FExpr.let' stmts body) in
        ( { TS.term = { Fc.Program.type_fns = Vector.empty (* FIXME *)
                       ; defs = Vector.empty; main }
          ; eff }
        , Env.namespace env |> Option.get )
end

