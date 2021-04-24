open Asserts
type 'a with_pos = 'a Util.with_pos

module TS = TyperSigs
module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module T = Fc.Type
module FStmt = Fc.Term.Stmt
module FExpr = Fc.Term.Expr
module Env = TypeEnv
type eff = T.t
type 'a typing = 'a TyperSigs.typing
type ctrs = Constraint.queue

module Make (Kinding : TyperSigs.KINDING) = struct
    (* OPTIMIZE: First try to unify on the fly: *)
    let unify ctrs span env t t' = Constraint.unify ctrs span env t t'

    let const_typ (c : Const.t) = T.Prim (match c with
        | Int _ -> Int
        | String _ -> String)

    let typeof _ _ (expr : AExpr.t with_pos) : FExpr.t typing = match expr.v with
        | Const c ->
            let typ = const_typ c in
            {term = FExpr.at expr.pos typ (FExpr.const c); eff = EmptyRow}

        | _ -> todo (Some expr.pos)

    let check_interactive_stmt : ctrs -> FStmt.t CCVector.vector -> Env.t -> AStmt.t -> Env.t * eff
    = fun ctrs stmts' env -> function
        | Def (span, _, _) -> todo (Some span)
        | Expr expr ->
            let {TS.term = expr; eff} = typeof ctrs env expr in
            CCVector.push stmts' (Expr expr);
            (env, eff)

    let check_interactive_stmts ctrs env stmts =
        let span =
            let (start, _) = AStmt.pos (Vector1.get stmts 0) in
            let (_, stop) = AStmt.pos (Vector1.get stmts (Vector1.length stmts - 1)) in
            (start, stop) in

        let stmts' = CCVector.create () in
        let eff = T.Uv (Env.uv env T.aRow) in
        ignore (Vector1.fold (fun env stmt ->
            let (env, stmt_eff) = check_interactive_stmt ctrs stmts' env stmt in
            ignore (unify ctrs span env stmt_eff eff);
            env
        ) env stmts);

        let stmts = CCVector.to_array stmts' in
        let main =
            let (stmts, body) =
                if Array.length stmts > 0
                then match Array.get stmts 0 with
                    | Expr expr -> (Array.sub stmts 0 (Array.length stmts - 1), expr)
                    | _ -> (stmts, FExpr.at span (Tuple Vector.empty) (FExpr.values [||]))
                else (stmts, FExpr.at span (Tuple Vector.empty) (FExpr.values [||])) in
            FExpr.at span body.typ (FExpr.let' stmts body) in
        ( { TS.term = { Fc.Program.type_fns = Vector.empty (* FIXME *)
                       ; defs = Vector.empty; main }
          ; eff }
        , env )
end

