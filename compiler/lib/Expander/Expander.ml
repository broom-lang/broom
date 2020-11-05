type 'a with_pos = 'a Util.with_pos

type typ = Ast.Type.t
module Expr = Ast.Term.Expr
type expr = Expr.t
type pat = Expr.pat
type clause = Expr.clause
type def = Ast.Term.Stmt.def
type stmt = Ast.Term.Stmt.t

type fixity = Infix | Prefix | Postfix

module Env = struct
    type t = unit list

    let empty = []

    let fixity env name = None (* FIXME *)
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
        | Some (None, arg, i) -> postfix_tail arg i in

    (* args = prefix* *)
    let args i =
        let args = CCVector.create () in
        let rec loop i =
            match lookahead i with
            | Some (Some Prefix | None) ->
                let (arg, i) = prefix i in
                CCVector.push args arg;
                loop i
            | Some (Some Infix) | None -> (Vector.build args, i) in
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
            {pos; v = App (callee, Ior.Right {pos = apos; v = Values args})})
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
                    {pos; v = App (op, Ior.Right {pos; v = Values args})} in
                tail lhs i
            | None -> lhs in
        let (lhs, i) = app i in
        tail lhs i in

    infix 0

(* OPTIMIZE: Type.map_children (which does not exist yet): *)
let rec expand_typ env (typ : typ with_pos) : typ with_pos = match typ.v with
    | Pi {domain; codomain} ->
        let domain = domain |> Ior.bimap
            (expand env)
            (fun (edomain, eff) ->
                (expand env edomain, Option.map (expand_typ env) eff)) in
        {typ with v = Pi {domain; codomain = expand_typ env codomain}}
    | Values typs ->
        {typ with v = Values (Vector.map (expand_typ env) typs)}
    | Record stmts ->
        {typ with v = Record (expand_stmts env stmts)}
    | Row stmts ->
        {typ with v = Row (expand_stmts env stmts)}
    | Path expr ->
        {typ with v = Path ((expand env {typ with v = expr}).v)}
    | Prim _ -> typ

(* OPTIMIZE: Expr.map_children (which does not exist yet): *)
and expand env expr : expr with_pos =
    let step (expr : expr with_pos) : expr with_pos = match expr.v with
        | Fn clauses ->
            {expr with v = Fn (Vector.map (expand_clause env) clauses)}
        | AppSequence exprs -> expand env (parse_appseq env (Vector1.to_vector exprs))
        | App (callee, args) ->
            {expr with v = App (expand env callee, Ior.map (expand env) args)}
        | PrimApp (op, args) ->
            {expr with v = PrimApp (op, Ior.map (expand env) args)}
        | Ann (expr, typ) ->
            {expr with v = Ann (expand env expr, expand_typ env typ)}
        | Values exprs ->
            {expr with v = Values (Vector.map (expand env) exprs)}
        | Focus (focusee, index) ->
            {expr with v = Focus (expand env focusee, index)}
        | Record stmts ->
            {expr with v = Record (expand_stmts env stmts)}
        | Select (selectee, label) ->
            {expr with v = Select (expand env selectee, label)}
        | Proxy typ -> {expr with v = Proxy ((expand_typ env {expr with v = typ}).v)}
        | Var _ | Const _ -> expr in
    step expr

and expand_clause env ({params; body} : clause) : clause =
    {params = Ior.map (expand env) params; body = expand env body}

and expand_def env (pos, pat, expr) =
    ((pos, expand env pat, expand env expr), env)

and expand_defs env defs =
    let defs' = CCVector.create () in
    let _ = Vector.fold (fun env def ->
        let (def', env) = expand_def env def in
        CCVector.push defs' def';
        env
    ) env defs in
    Vector.build defs'

and expand_stmt env : stmt -> stmt * Env.t = function
    | Def def ->
        let (def, env) = expand_def env def in
        (Def def, env)
    | Expr expr -> (Expr (expand env expr), env)

and expand_stmts env stmts =
    let stmts' = CCVector.create () in
    let _ = Vector.fold (fun env stmt ->
        let (stmt', env) = expand_stmt env stmt in
        CCVector.push stmts' stmt';
        env
    ) env stmts in
    Vector.build stmts'

