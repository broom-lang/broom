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

module Make (Kinding : TS.KINDING) (Constraints : TS.CONSTRAINTS) = struct
    let unify = Constraints.unify
    let subtype = Constraints.subtype

    let const_typ (c : Const.t) = T.Prim (match c with
        | Int _ -> Int
        | String _ -> String)

    let typeof _ env (expr : AExpr.t with_pos) : FExpr.t typing = match expr.v with
        | Var name ->
            let var = Env.find_val env expr.pos name in
            {term = FExpr.at expr.pos var.vtyp (FExpr.use var); eff = EmptyRow}

        | Const c ->
            let typ = const_typ c in
            {term = FExpr.at expr.pos typ (FExpr.const c); eff = EmptyRow}

        | _ -> todo (Some expr.pos)

    let check ctrs env super expr =
        let {TS.term = expr; eff} = typeof ctrs env expr in
        let coerce = subtype ctrs expr.pos env expr.typ super in
        {TS.term = Coercer.apply_opt coerce expr; eff}

    let typeof_pat _ env (plicity : plicity) (pat : AExpr.t with_pos) = match pat.v with
        | Var name ->
            let kind = T.App {callee = Prim TypeIn; arg = Uv (Env.uv env T.rep)} in
            let typ = T.Uv (Env.uv env kind) in
            let var = FExpr.var plicity name typ in
            ( FExpr.pat_at pat.pos typ (VarP var)
            , Env.push_val env var )

        | Const c ->
            let typ = const_typ c in
            (FExpr.pat_at pat.pos typ (ConstP c), env)

        | _ -> todo (Some pat.pos)

    let check_interactive_stmt : ctrs -> Env.t -> AStmt.t -> FStmt.t * Env.t * eff
    = fun ctrs env -> function
        | Def (span, pat, expr) ->
            let (pat, env') = typeof_pat ctrs env Explicit pat in
            let {TS.term = expr; eff} = check ctrs env pat.ptyp expr in
            (Def (span, pat, expr), env', eff)

        | Expr expr ->
            let {TS.term = expr; eff} = typeof ctrs env expr in
            (Expr expr, env, eff)

    let check_interactive_stmts ctrs env stmts =
        let span =
            let (start, _) = AStmt.pos (Vector1.get stmts 0) in
            let (_, stop) = AStmt.pos (Vector1.get stmts (Vector1.length stmts - 1)) in
            (start, stop) in

        let stmts' = CCVector.create () in
        let eff = T.Uv (Env.uv env T.aRow) in
        let env = Vector1.fold (fun env stmt ->
            let (stmt, env, stmt_eff) = check_interactive_stmt ctrs env stmt in
            CCVector.push stmts' stmt;
            ignore (unify ctrs span env stmt_eff eff);
            env
        ) env stmts in

        let stmts = CCVector.to_array stmts' in
        let main =
            let (stmts, body) =
                if Array.length stmts > 0
                then match Array.get stmts (Array.length stmts - 1) with
                    | Expr expr -> (Array.sub stmts 0 (Array.length stmts - 1), expr)
                    | _ -> (stmts, FExpr.at span (Tuple Vector.empty) (FExpr.values [||]))
                else (stmts, FExpr.at span (Tuple Vector.empty) (FExpr.values [||])) in
            FExpr.at span body.typ (FExpr.let' stmts body) in
        ( { TS.term = { Fc.Program.type_fns = Vector.empty (* FIXME *)
                       ; defs = Vector.empty; main }
          ; eff }
        , env )
end

