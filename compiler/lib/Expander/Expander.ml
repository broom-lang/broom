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
type broompath = string list

type fixity = Infix | Prefix | Postfix

module Make (StringHashtbl : Hashtbl.S with type key = string) = struct

module Env : sig
    type value =
        | Var of expr with_pos
        | BroomPath of string list
        | RequireCache of Name.t StringHashtbl.t

    val add : Name.t -> value -> unit
    val find : Name.t -> value option
end = struct
    type value =
        | Var of expr with_pos
        | BroomPath of string list
        | RequireCache of Name.t StringHashtbl.t

    let the = Name.Hashtbl.create 0

    let add binding v = Name.Hashtbl.add the binding v
    let find binding = Name.Hashtbl.find_opt the binding
end

(* OPTIMIZE: distribute to scopes, like Racket: *)
module Bindings = struct
    type binding' = Name.t
    type binding = fixity option * binding'

    type t = binding Name.Map.t

    let empty path =
        let path_name = Name.of_string "__BROOMPATH" in
        let path_binding = Name.fresh () in
        let rqc_name = Name.of_string "__requireCache" in
        let rqc_binding = Name.fresh () in
        Env.add path_binding (BroomPath path);
        Env.add rqc_binding (RequireCache (StringHashtbl.create 0));
        Name.Map.empty
        |> Name.Map.add path_name (None, path_binding)
        |> Name.Map.add rqc_name (None, rqc_binding)

    let add env name binding = Name.Map.add name binding env

    let find env id = match Name.Map.find_opt id env with
        | Some binding -> binding
        | None -> (None, id)

    let fixity env id = fst (find env id)
end

let parse_appseq env exprs =
    let lookahead i =
        Vector.get_opt exprs i
        |> Option.map (fun (expr : expr with_pos) ->
            match expr.v with
            | Var name -> Bindings.fixity env name
            | _ -> None) in

    let token i =
        Vector.get_opt exprs i
        |> Option.map (fun (expr : expr with_pos) ->
            match expr.v with
            | Var name -> (Bindings.fixity env name, expr, i + 1)
            | _ -> (None, expr, i + 1)) in

    (* postfix = postfix POSTFIX | NONFIX *)

    (* postfix_tail(arg) = POSTFIX* *)
    let rec postfix_tail (arg : expr with_pos) i : expr with_pos * int =
        match token i with
        | Some (Some Postfix, op, i) ->
            let arg = { Util.pos = (fst arg.pos, snd op.pos)
                      ; v = Expr.App (op, Explicit, arg) } in
            postfix_tail arg i
        | _ -> (arg, i) in

    (* prefix = PREFIX prefix | postfix *)
    let rec prefix i : expr with_pos * int =
        match token i with
        | Some (Some Prefix, op, i) ->
            let (arg, i) = prefix i in
            ( { pos = (fst op.pos, snd arg.pos)
              ; v = App (op, Explicit, arg) }
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
            {pos; v = App (callee, Explicit, arg)}
          | len ->
            let pos = (fst callee.pos, snd (Vector.get args (len - 1)).pos) in
            let apos = (fst (Vector.get args 0).pos, snd pos) in
            {pos; v = App (callee, Explicit, {pos = apos; v = Tuple args})})
        , i ) in

    (* infix = infix INFIX app | app *)
    let infix i =
        (* infix_tail(lhs) = (INFIX prefix)* *)
        let rec tail (lhs : expr with_pos) i =
            match token i with
            | Some (Some Infix, op, i) ->
                let (rhs, i) = app i in
                let pos = (fst lhs.pos, snd rhs.pos) in
                let args = Vector.of_array_unsafe [|lhs; rhs|] in
                let lhs : expr with_pos =
                    {pos; v = App (op, Explicit, {pos; v = Tuple args})} in
                tail lhs i
            | None -> lhs
            | Some ((Some (Prefix | Postfix) | None), _, _) -> failwith "unexpected" in
        let (lhs, i) = app i in
        tail lhs i in

    let _ = (Infix, Prefix, Postfix) in (* HACK: silence warning *)
    infix 0

(* OPTIMIZE: Type.map_children (which does not exist yet): *)
let rec expand_typ define_toplevel env (typ : typ with_pos) : typ with_pos =
    match typ.v with
    | Pi {domain; eff; codomain} ->
        let (domain, env) = expand_pat define_toplevel ignore env domain in
        let eff = Option.map (expand_typ define_toplevel env) eff in
        {typ with v = Pi {domain; eff; codomain = expand_typ define_toplevel env codomain}}
    | Impli {domain; codomain} ->
        let (domain, env) = expand_pat define_toplevel ignore env domain in
        {typ with v = Impli {domain; codomain = expand_typ define_toplevel env codomain}}
    | Tuple typs ->
        {typ with v = Tuple (Vector.map (expand_typ define_toplevel env) typs)}
    | Record stmts ->
        {typ with v = Record (expand_stmts define_toplevel ignore env stmts)} (* TODO: don't ignore? *)
    | Row stmts ->
        {typ with v = Row (expand_stmts define_toplevel ignore env stmts)} (* TODO: don't ignore? *)
    | Path expr ->
        {typ with v = Path ((expand define_toplevel env {typ with v = expr}).v)}
    | Prim _ -> typ

(* OPTIMIZE: Expr.map_children (which does not exist yet): *)
and expand define_toplevel env expr : expr with_pos = match expr.v with
    | Let (defs, body) ->
        let (defs, env) = expand_defs' define_toplevel env (Vector1.to_vector defs) in
        let body = expand define_toplevel env body in
        (match Vector1.of_vector defs with
        | Some defs -> {expr with v = Let (defs, body)}
        | None -> body)
    | Fn (plicity, clauses) ->
        {expr with v = Fn (plicity, Vector.map (expand_clause define_toplevel env) clauses)}
    | AppSequence exprs ->
        expand define_toplevel env (parse_appseq env (Vector1.to_vector exprs))
    | App ({v = Var cname; pos = _}, Explicit, arg) ->
        (match Env.find (snd (Bindings.find env cname)) with
        | Some (Var id) ->
            {expr with v = App (id, Explicit, (expand define_toplevel env arg))}
        | Some _ -> failwith "TODO"
        | None -> (match Name.basename cname with
            | Some "let" -> expand_let define_toplevel env expr.pos arg
            | Some "include" -> expand_include env arg
            | Some "require" -> expand_require define_toplevel env expr.pos arg
            | _ -> failwith ("unbound: " ^ Name.to_string cname
                ^ " at " ^ Util.span_to_string expr.pos)))
    | App (callee, plicity, args) ->
        {expr with v = App (expand define_toplevel env callee
            , plicity, expand define_toplevel env args)}
    | PrimApp (op, iargs, args) ->
        {expr with v = PrimApp (op, Option.map (expand define_toplevel env) iargs
            , expand define_toplevel env args)}
    | PrimBranch (op, iargs, args, clauses) ->
        {expr with v = PrimBranch (op, Option.map (expand define_toplevel env) iargs
            , expand define_toplevel env args
            , Vector.map (expand_clause define_toplevel env) clauses)}
    | Ann (expr, typ) ->
        {expr with v = Ann (expand define_toplevel env expr
            , expand_typ define_toplevel env typ)}
    | Tuple exprs ->
        {expr with v = Tuple (Vector.map (expand define_toplevel env) exprs)}
    | Focus (focusee, index) ->
        {expr with v = Focus (expand define_toplevel env focusee, index)}
    | Record stmts ->
        (* TODO: Field punning (tricky because the naive translation `letrec x = x in {x = x}` makes no sense) *)
        let vars = CCVector.create () in
        let stmts = expand_stmts define_toplevel (CCVector.push vars) env stmts in
        let defs = stmts |> Vector.map (function
            | Stmt.Def def -> def
            | Expr _ -> failwith "non-def stmt in Record") in
        let body : expr with_pos = {expr with v = Record (Vector.build vars)} in
        (match Vector1.of_vector defs with
        | Some defs -> {expr with v = Let (defs, body)}
        | None -> body)

    | Select (selectee, label) ->
        {expr with v = Select (expand define_toplevel env selectee, label)}
    | Proxy typ ->
        {expr with v = Proxy ((expand_typ define_toplevel env {expr with v = typ}).v)}
    | Var name -> (match Env.find (snd (Bindings.find env name)) with
        | Some (Var id) -> id
        | Some _ -> failwith "TODO"
        | None -> failwith ("unbound: " ^ Name.to_string name
            ^ " at " ^ Util.span_to_string expr.pos))
    | Wild _ -> failwith "stray `_`"
    | Const _ -> expr

and expand_let define_toplevel env pos (arg : expr with_pos) = match arg.v with
    | Record stmts ->
        let defs = Stream.from (Vector.to_source stmts)
            |> Stream.take_while (function Stmt.Def _ -> true | Expr _ -> false)
            |> Stream.map (function Stmt.Def def -> def | Expr _ -> failwith "unreachable")
            |> Stream.into (Vector.sink ()) in
        if Vector.length defs = Vector.length stmts - 1
        then match Vector.get stmts (Vector.length stmts - 1) with
            | Expr body ->
                let (defs, env) = expand_defs' define_toplevel env defs in
                let body = expand define_toplevel env body in
                (match Vector1.of_vector defs with
                | Some defs -> {pos; v = Let (defs, body)}
                | None -> body)
            | _ -> failwith "dangling stmts in `let`"
        else failwith "TODO"
    | _ -> failwith "non-record `let` arg"

and expand_include env (arg : expr with_pos) = match arg.v with
    | Const (String filename) -> (* FIXME: error handling: *)
        let path = match Env.find (snd (Bindings.find env (Name.of_string "__BROOMPATH"))) with
            | Some (BroomPath path) -> path
            | Some _ -> failwith "compiler bug: __BROOMPATH has wrong type"
            | None -> failwith "compiler bug: __BROOMPATH unbound" in
        let filename = path |> List.find_map (fun dir ->
            let filename = Filename.concat dir filename ^ ".brm" in
            if Sys.file_exists filename
            then Some filename
            else None) in
        let input = open_in (Option.get filename) in
        Fun.protect (fun () ->
            input
            |> Sedlexing.Utf8.from_channel
            |> SedlexMenhir.create_lexbuf
            |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.modul
        ) ~finally: (fun () -> close_in input)
    | _ -> failwith "non-string-literal `include` arg"

(* TODO: canonicalize (?) filename: *)
and expand_require define_toplevel env pos (arg : expr with_pos) = match arg.v with
    | Const (String filename) ->
        let name = 
            match Env.find (snd (Bindings.find env (Name.of_string "__requireCache"))) with
            | Some (RequireCache requireds) -> (match StringHashtbl.find_opt requireds filename with
                | Some name -> name
                | None ->
                    let name = Name.fresh () in
                    StringHashtbl.add requireds filename name;
                    let var : pat with_pos = {pos; v = Var name} in
                    let incl : expr with_pos = {pos; v = Var (Name.of_string "include")} in
                    let load = expand define_toplevel env {pos; v = App (incl, Explicit, arg)} in
                    let def : def = (pos, var, load) in
                    define_toplevel def;
                    name)
            | Some _ -> failwith "compiler bug: __requireCache has wrong type"
            | None -> failwith "compiler bug: __requireCache is unbound" in
        {pos; v = Var name}
    | _ -> failwith "non-string-literal `include` arg"

and expand_pat define_toplevel report_def env (pat : pat with_pos) =
    match pat.v with
    | Tuple pats ->
        let pats' = CCVector.create () in
        let env = Vector.fold (fun env pat ->
            let (pat, env) = expand_pat define_toplevel report_def env pat in
            CCVector.push pats' pat;
            env
        ) env pats in
        ({pat with v = Tuple (Vector.build pats')}, env)
    | Focus (focusee, label) ->
        let (focusee, env) = expand_pat define_toplevel report_def env focusee in
        ({pat with v = Focus (focusee, label)}, env)
    | Proxy typ ->
        ({pat with v = Proxy ((expand_typ define_toplevel env {pat with v = typ}).v)}, env)
    | Var name ->
        let name' = Name.freshen name in
        let id' = {pat with v = Expr.Var name'} in
        report_def (Stmt.Def (pat.pos, pat, id'));
        Env.add name' (Var id');
        ({pat with v = Var name'}, Bindings.add env name (None, name'))
    | Wild _ | Const _ -> (pat, env)
    | _ -> failwith "TODO"

and expand_clause define_toplevel env ({params; body} : clause) : clause =
    let (params, env) = expand_pat define_toplevel ignore env params in
    {params; body = expand define_toplevel env body}

and expand_def_pat define_toplevel report_def env (pos, pat, expr) =
    let (pat, env) = expand_pat define_toplevel report_def env pat in
    ((pos, pat, expr), env)

and expand_def define_toplevel env (pos, pat, expr) =
    (pos, pat, expand define_toplevel env expr)

and expand_defs' define_toplevel env defs =
    let defs' = CCVector.create () in
    let env = Vector.fold (fun env def ->
        let (def', env) = expand_def_pat define_toplevel ignore env def in
        CCVector.push defs' def';
        env
    ) env defs in
    CCVector.map_in_place (expand_def define_toplevel env) defs';
    (Vector.build defs', env)

and expand_stmt_pat define_toplevel report_def env : stmt -> stmt * Bindings.t = function
    | Def def ->
        let (def, env) = expand_def_pat define_toplevel report_def env def in
        (Def def, env)
    | Expr _ as stmt -> (stmt, env)

and expand_stmt define_toplevel env : stmt -> stmt = function
    | Def def -> Def (expand_def define_toplevel env def)
    | Expr expr -> Expr (expand define_toplevel env expr)

and expand_stmts' define_toplevel report_def env stmts =
    let stmts' = CCVector.create () in
    let env = Vector.fold (fun env stmt ->
        let (stmt', env) = expand_stmt_pat define_toplevel report_def env stmt in
        CCVector.push stmts' stmt';
        env
    ) env stmts in
    CCVector.map_in_place (expand_stmt define_toplevel env) stmts';
    (Vector.build stmts', env)

and expand_stmts define_toplevel report_def env stmts =
    fst (expand_stmts' define_toplevel report_def env stmts)

let expand_program env defs entry =
    let defs' = CCVector.create () in
    let env = Vector.fold (fun env def ->
        let (def', env) = expand_def_pat (CCVector.push defs') ignore env def in
        CCVector.push defs' def';
        env
    ) env defs in
    let defs = defs' and defs' = CCVector.create () in
    defs |> CCVector.iter (fun def ->
        CCVector.push defs' (expand_def (CCVector.push defs') env def)
    );
    let entry = expand (CCVector.push defs') env entry in
    (Vector.build defs', entry)

let expand_interactive_stmt env stmt =
    let defs = CCVector.create () in
    let define_toplevel = CCVector.push defs in
    let (stmt, env) = expand_stmt_pat define_toplevel ignore env stmt in
    let stmt = expand_stmt define_toplevel env stmt in
    let stmts = CCVector.map (fun def -> Stmt.Def def) defs in
    CCVector.push stmts stmt;
    (env, Option.get (Vector1.of_vector (Vector.build stmts)))

end

