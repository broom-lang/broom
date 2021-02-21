(* TODO: Just re- ~typecheck everything? *)

open Asserts

module Type = ComplexFc.Type
module Expr = ComplexFc.Term.Expr
module Stmt = ComplexFc.Term.Stmt
module Coercer = ComplexFc.Types.Coercer
module Program = ComplexFc.Program

let (!) = TxRef.(!)

module Env : sig
    type t

    val empty : t
end = struct
    type t = unit

    let empty = ()
end

let finish_typ _ typ = typ (* TODO *)

let coerce _ _ _ : Type.coercion option = None (* TODO *)

let rec finish_expr env : Expr.t -> Expr.t = fun expr ->
    let expr = match expr.term with
        | Use {name = _; vtyp} ->
            let typ' = finish_typ env expr.typ in
            let expr = {expr with typ = vtyp} in
            (match coerce env vtyp typ' with
            | Some coercion -> Expr.at expr.pos typ' (Expr.cast expr coercion)
            | None -> expr)

        | Fn {t_scope; param; body} ->
            let param : Expr.var = {name = param.name; vtyp = finish_typ env param.vtyp} in
            let body = finish_expr env body in
            {expr with term = Expr.fn t_scope param body}

        | App {callee; universals; arg} ->
            let callee = finish_expr env callee in
            let universals = Vector.map (finish_typ env) universals in
            let arg = finish_expr env arg in
            {expr with term = Expr.app callee universals arg}

        | PrimApp {op; universals; arg} ->
            let universals = Vector.map (finish_typ env) universals in
            let arg = finish_expr env arg in
            {expr with term = Expr.primapp op universals arg}

        | Let {defs; body} ->
            let (defs, env) = finish_stmts env defs in
            let body = finish_expr env body in
            {expr with term = Expr.let' defs body}

        | Match {matchee; clauses} ->
            let matchee = finish_expr env matchee in
            let clauses = Vector.map (finish_clause env) clauses in
            {expr with term = Expr.match' matchee clauses}

        | Cast _ -> unreachable (Some expr.pos) ~msg: "encountered Cast"

        | Convert {coerce; arg} -> Coercer.apply_opt !coerce arg

        | Select {selectee; label} ->
            {expr with term = Expr.select (finish_expr env selectee) label}

        | Tuple exprs ->
            {expr with term = Expr.tuple (Vector.map (finish_expr env) exprs)}

        | Focus {focusee; index} ->
            {expr with term = Expr.focus (finish_expr env focusee) index}

        | Proxy carrie -> {expr with term = Expr.proxy (finish_typ env carrie)}

        | Const _ -> expr

        | _ -> todo (Some expr.pos) in

    {expr with typ = finish_typ env expr.typ} (* OPTIMIZE: `Use` .typ gets finished twice *)

and finish_pat _ pat = pat (* TODO *)

and finish_clause env {pat; body} =
    { pat = finish_pat env pat
    ; body = finish_expr env body }

and finish_decl _ : Stmt.def -> Stmt.def * Env.t = fun (pos, _, _) -> todo (Some pos)

and finish_decls env decls =
    let decls' = CCVector.create () in
    let env = Vector.fold (fun env decl ->
        let (decl, env) = finish_decl env decl in
        CCVector.push decls' decl;
        env
    ) env decls in
    (Vector.build decls', env)

and finish_stmt env : Stmt.t -> Stmt.t * Env.t = function
    | Def decl ->
        let (decl, env) = finish_decl env decl in
        (Def decl, env)
    | Expr expr -> (Expr (finish_expr env expr), env)

and finish_stmts env stmts =
    let stmts' = CCVector.create () in
    let env = Vector1.fold (fun env stmt ->
        let (stmt, env) = finish_stmt env stmt in
        CCVector.push stmts' stmt;
        env
    ) env stmts in
    (Vector.build stmts', env)

let finish : Program.t -> Program.t = fun {type_fns; defs; main} ->
    let (decls, env) = finish_decls Env.empty defs in
    let main = finish_expr env main in
    {type_fns; defs = decls; main}

