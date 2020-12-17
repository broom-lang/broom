open Streaming

type 'a with_pos = 'a Util.with_pos

type typ = Ast.Type.t
module Expr = Ast.Term.Expr
type expr = Expr.t
type pat = Expr.pat
type clause = Expr.clause
module Stmt = Ast.Term.Stmt
type def = Stmt.def
type stmt = Stmt.t

type fixity = Infix | Prefix | Postfix

module Env = struct
    type binding' = Name.t
    type binding = fixity option * binding'

    type t = binding Name.Map.t

    let empty = Name.Map.empty

    let add env name binding = Name.Map.add name binding env

    let find env id = Name.Map.find_opt id env

    let fixity env id = Option.bind (find env id) fst
end

let parse_appseq env exprs =
    let lookahead i =
        Vector.get_opt exprs i
        |> Option.map (fun (expr : expr with_pos) ->
            match expr.v with
            | Var name -> Env.fixity env name
            | _ -> None) in

    let token i =
        Vector.get_opt exprs i
        |> Option.map (fun (expr : expr with_pos) ->
            match expr.v with
            | Var name -> (Env.fixity env name, expr, i + 1)
            | _ -> (None, expr, i + 1)) in

    (* postfix = postfix POSTFIX | NONFIX *)

    (* postfix_tail(arg) = POSTFIX* *)
    let rec postfix_tail (arg : expr with_pos) i : expr with_pos * int =
        match token i with
        | Some (Some Postfix, op, i) ->
            let arg = { Util.pos = (fst arg.pos, snd op.pos)
                      ; v = Expr.App (op, Ior.Right arg) } in
            postfix_tail arg i
        | _ -> (arg, i) in

    (* prefix = PREFIX prefix | postfix *)
    let rec prefix i : expr with_pos * int =
        match token i with
        | Some (Some Prefix, op, i) ->
            let (arg, i) = prefix i in
            ( { pos = (fst op.pos, snd arg.pos)
              ; v = App (op, Ior.Right arg) }
            , i )
        | Some (None, arg, i) -> postfix_tail arg i
        | Some (Some (Infix | Postfix), _, _) -> failwith "unexpected"
        | None -> failwith "unfinished" in

    (* args = prefix* *)
    let args i =
        let args = CCVector.create () in
        let rec loop i =
            match lookahead i with
            | Some (Some Prefix | None) ->
                let (arg, i) = prefix i in
                CCVector.push args arg;
                loop i
            | Some (Some Infix) | None -> (Vector.build args, i)
            | Some (Some Postfix) -> failwith "unexpected" in
        loop i in

    (* app = prefix args *)
    let app i =
        let (callee, i) = prefix i in
        let (args, i) = args i in
        ( (match Vector.length args with
          | 0 -> callee
          | 1 ->
            let arg = Vector.get args 0 in
            let pos = (fst callee.pos, snd arg.pos) in
            {pos; v = App (callee, Ior.Right arg)}
          | len ->
            let pos = (fst callee.pos, snd (Vector.get args (len - 1)).pos) in
            let apos = (fst (Vector.get args 0).pos, snd pos) in
            {pos; v = App (callee, Ior.Right {pos = apos; v = Tuple args})})
        , i ) in

    (* infix = infix INFIX app | app *)
    let rec infix i =
        (* infix_tail(lhs) = (INFIX prefix)* *)
        let rec tail (lhs : expr with_pos) i =
            match token i with
            | Some (Some Infix, op, i) ->
                let (rhs, i) = app i in
                let pos = (fst lhs.pos, snd rhs.pos) in
                let args = Vector.of_array_unsafe [|lhs; rhs|] in
                let lhs : expr with_pos =
                    {pos; v = App (op, Ior.Right {pos; v = Tuple args})} in
                tail lhs i
            | None -> lhs
            | Some ((Some (Prefix | Postfix) | None), _, _) -> failwith "unexpected" in
        let (lhs, i) = app i in
        tail lhs i in

    infix 0

(* OPTIMIZE: Type.map_children (which does not exist yet): *)
let rec expand_typ env (typ : typ with_pos) : typ with_pos = match typ.v with
    | Pi {domain; codomain} ->
        let (domain, env) = match domain with
            | Left idomain ->
                let (idomain, env) = expand_pat env idomain in
                (Ior.Left idomain, env)
            | Right (edomain, eff) ->
                let (edomain, env) = expand_pat env edomain in
                let eff = Option.map (expand_typ env) eff in
                (Right (edomain, eff), env)
            | Both (idomain, (edomain, eff)) ->
                let (idomain, env) = expand_pat env idomain in
                let (edomain, env) = expand_pat env edomain in
                let eff = Option.map (expand_typ env) eff in
                (Both (idomain, (edomain, eff)), env) in
        {typ with v = Pi {domain; codomain = expand_typ env codomain}}
    | Tuple typs ->
        {typ with v = Tuple (Vector.map (expand_typ env) typs)}
    | Record stmts ->
        {typ with v = Record (expand_stmts env stmts)}
    | Row stmts ->
        {typ with v = Row (expand_stmts env stmts)}
    | Path expr ->
        {typ with v = Path ((expand env {typ with v = expr}).v)}
    | Prim _ -> typ

(* OPTIMIZE: Expr.map_children (which does not exist yet): *)
and expand env expr : expr with_pos = match expr.v with
    | Let (defs, body) ->
        let (defs, env) = expand_defs' env (Vector1.to_vector defs) in
        let body = expand env body in
        (match Vector1.of_vector defs with
        | Some defs -> {expr with v = Let (defs, body)}
        | None -> body)
    | Fn clauses ->
        {expr with v = Fn (Vector.map (expand_clause env) clauses)}
    | AppSequence exprs -> expand env (parse_appseq env (Vector1.to_vector exprs))
    | App ({v = Var cname; pos = _} as callee, Ior.Right arg) ->
        (match Env.find env cname with
        | Some (_, cname') ->
            {expr with v = App ({v = Var cname'; pos = callee.pos}
                , Ior.Right (expand env arg))}
        | None -> (match Name.basename cname with
            | Some "let" -> expand_let env expr.pos arg
            | _ -> failwith ("unbound: " ^ Name.to_string cname
                ^ " at " ^ Util.span_to_string expr.pos)))
    | App (callee, args) ->
        {expr with v = App (expand env callee, Ior.map (expand env) args)}
    | PrimApp (op, args) ->
        {expr with v = PrimApp (op, Ior.map (expand env) args)}
    | PrimBranch (op, args, clauses) ->
        {expr with v = PrimBranch (op, Ior.map (expand env) args
            , Vector.map (expand_clause env) clauses)}
    | Ann (expr, typ) ->
        {expr with v = Ann (expand env expr, expand_typ env typ)}
    | Tuple exprs ->
        {expr with v = Tuple (Vector.map (expand env) exprs)}
    | Focus (focusee, index) ->
        {expr with v = Focus (expand env focusee, index)}
    | Record stmts ->
        {expr with v = Record (expand_stmts env stmts)}
    | Select (selectee, label) ->
        {expr with v = Select (expand env selectee, label)}
    | Proxy typ -> {expr with v = Proxy ((expand_typ env {expr with v = typ}).v)}
    | Var name -> (match Env.find env name with
        | Some (_, name') -> {expr with v = Var name'}
        | None -> failwith ("unbound: " ^ Name.to_string name
            ^ " at " ^ Util.span_to_string expr.pos))
    | Wild _ -> failwith "stray `_`"
    | Const _ -> expr

and expand_let env pos (arg : expr with_pos) = match arg.v with
    | Record stmts ->
        let defs = Stream.from (Vector.to_source stmts)
            |> Stream.take_while (function Stmt.Def _ -> true | Expr _ -> false)
            |> Stream.map (function Stmt.Def def -> def | Expr _ -> failwith "unreachable")
            |> Stream.into (Vector.sink ()) in
        if Vector.length defs = Vector.length stmts - 1
        then match Vector.get stmts (Vector.length stmts - 1) with
            | Expr body ->
                let (defs, env) = expand_defs' env defs in
                let body = expand env body in
                (match Vector1.of_vector defs with
                | Some defs -> {pos; v = Let (defs, body)}
                | None -> body)
            | _ -> failwith "dangling stmts in `let`"
        else failwith "TODO"
    | _ -> failwith "non-record `let` arg"

and expand_pat env (pat : pat with_pos) = match pat.v with
    | Tuple pats ->
        let pats' = CCVector.create () in
        let env = Vector.fold (fun env pat ->
            let (pat, env) = expand_pat env pat in
            CCVector.push pats' pat;
            env
        ) env pats in
        ({pat with v = Tuple (Vector.build pats')}, env)
    | Var name ->
        let name' = Name.freshen name in
        ({pat with v = Var name'}, Env.add env name (None, name'))
    | Wild _ | Const _ -> (pat, env)

and expand_clause env ({params; body} : clause) : clause =
    let (params, env) = match params with
        | Left iparam ->
            let (iparam, env) = expand_pat env iparam in
            (Ior.Left iparam, env)
        | Right eparam ->
            let (eparam, env) = expand_pat env eparam in
            (Right eparam, env)
        | Both (iparam, eparam) ->
            let (iparam, env) = expand_pat env iparam in
            let (eparam, env) = expand_pat env eparam in
            (Both (iparam, eparam), env) in
    {params; body = expand env body}

and expand_def_pat env (pos, pat, expr) =
    let (pat, env) = expand_pat env pat in
    ((pos, pat, expr), env)

and expand_def env (pos, pat, expr) = (pos, pat, expand env expr)

and expand_defs' env defs =
    let defs' = CCVector.create () in
    let env = Vector.fold (fun env def ->
        let (def', env) = expand_def_pat env def in
        CCVector.push defs' def';
        env
    ) env defs in
    CCVector.map_in_place (expand_def env) defs';
    (Vector.build defs', env)

and expand_defs env defs = fst (expand_defs' env defs)

and expand_stmt_pat env : stmt -> stmt * Env.t = function
    | Def def ->
        let (def, env) = expand_def_pat env def in
        (Def def, env)
    | Expr _ as stmt -> (stmt, env)

and expand_stmt env : stmt -> stmt = function
    | Def def -> Def (expand_def env def)
    | Expr expr -> Expr (expand env expr)

and expand_stmts env stmts =
    let stmts' = CCVector.create () in
    let env = Vector.fold (fun env stmt ->
        let (stmt', env) = expand_stmt_pat env stmt in
        CCVector.push stmts' stmt';
        env
    ) env stmts in
    CCVector.map_in_place (expand_stmt env) stmts';
    Vector.build stmts'

