open Asserts

open Ast
type expr = Expr.t
type clause = Expr.clause
type def = Stmt.def
type stmt = Stmt.t
type broompath = string list

module Make (StringHashtbl : Hashtbl.S with type key = string) = struct

type fixity = Infix | Prefix | Postfix

(* # Environment (Name -> Value) *)

module Env : sig
    type value =
        | Var of expr
        | BroomPath of string list
        | RequireCache of Name.t StringHashtbl.t

    val add : Name.t -> value -> unit
    val find : Name.t -> value option
end = struct
    type value =
        | Var of expr
        | BroomPath of string list
        | RequireCache of Name.t StringHashtbl.t

    let the = Name.Hashtbl.create 0

    let add binding v = Name.Hashtbl.add the binding v
    let find binding = Name.Hashtbl.find_opt the binding
end

(* # Bindings (Name + Scopes -> Alphatized Name) *)

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

(* # Application Parsing (e.g. Infix Operators) *)

let parse_appseq env exprs =
    let lookahead i =
        Vector.get_opt exprs i
        |> Option.map (fun (expr : expr) ->
            match expr.v with
            | Var name -> Bindings.fixity env name
            | _ -> None) in

    let token i =
        Vector.get_opt exprs i
        |> Option.map (fun (expr : expr) ->
            match expr.v with
            | Var name -> (Bindings.fixity env name, expr, i + 1)
            | _ -> (None, expr, i + 1)) in

    (* postfix = postfix POSTFIX | NONFIX *)

    (* postfix_tail(arg) = POSTFIX* *)
    let rec postfix_tail (arg : expr) i : expr * int =
        match token i with
        | Some (Some Postfix, op, i) ->
            let arg = { Util.pos = (fst arg.pos, snd op.pos)
                ; v = Expr.App (Vector.of_array_unsafe [|op; arg|]) } in
            postfix_tail arg i
        | _ -> (arg, i) in

    (* prefix = PREFIX prefix | postfix *)
    let rec prefix i : expr * int =
        match token i with
        | Some (Some Prefix, op, i) ->
            let (arg, i) = prefix i in
            ( { pos = (fst op.pos, snd arg.pos)
                ; v = App (Vector.of_array_unsafe [|op; arg|]) }
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
            {pos; v = App (Vector.of_array_unsafe [|callee; arg|])}
          | len ->
            let pos = (fst callee.pos, snd (Vector.get args (len - 1)).pos) in
            let apos = (fst (Vector.get args 0).pos, snd pos) in
            {pos; v = App (Vector.of_array_unsafe [|callee; {pos = apos; v = Tuple args}|])})
        , i ) in

    (* infix = infix INFIX app | app *)
    let infix i =
        (* infix_tail(lhs) = (INFIX prefix)* *)
        let rec tail (lhs : expr) i =
            match token i with
            | Some (Some Infix, op, i) ->
                let (rhs, i) = app i in
                let pos = (fst lhs.pos, snd rhs.pos) in
                let args = Vector.of_array_unsafe [|lhs; rhs|] in
                let lhs : expr =
                    {pos; v = App (Vector.of_array_unsafe [|op; {pos; v = Tuple args}|])} in
                tail lhs i
            | None -> lhs
            | Some ((Some (Prefix | Postfix) | None), _, _) -> failwith "unexpected" in
        let (lhs, i) = app i in
        tail lhs i in

    let _ = (Infix, Prefix, Postfix) in (* HACK: silence warning *)
    infix 0

(* # Expressions *)

(* OPTIMIZE: Expr.map_children (which does not exist yet): *)
let rec expand define_toplevel env (expr : expr) : expr = match expr.v with
    (*| Let (defs, body) ->
        let (defs, env) = expand_defs' define_toplevel env (Vector1.to_vector defs) in
        let body = expand define_toplevel env body in
        (match Vector1.of_vector defs with
        | Some defs -> {expr with v = Let (defs, body)}
        | None -> body)*)
    | Fn clauses ->
        {expr with v = Fn (Vector.map (expand_clause define_toplevel env) clauses)}
    | ImpliFn clauses ->
        {expr with v = ImpliFn (Vector.map (expand_clause define_toplevel env) clauses)}

    | App exprs -> expand define_toplevel env (parse_appseq env exprs)
    (*| App ({v = Var cname; pos = _}, Explicit, arg) ->
        (match Env.find (snd (Bindings.find env cname)) with
        | Some (Var id) ->
            {expr with v = App (id, Explicit, (expand define_toplevel env arg))}
        | Some _ -> todo (Some expr.pos)
        | None -> (match Name.basename cname with
            | Some "let" -> expand_let define_toplevel env expr.pos arg
            | Some "include" -> expand_include env arg
            | Some "require" -> expand_require define_toplevel env expr.pos arg
            | _ -> failwith ("unbound: " ^ Name.to_string cname
                ^ " at " ^ Util.span_to_string expr.pos)))
    | App (callee, plicity, args) ->
        {expr with v = App (expand define_toplevel env callee
            , plicity, expand define_toplevel env args)}*)
    | PrimApp (Include, args) -> expand_include env args
    | PrimApp (Require, args) -> expand_require define_toplevel env expr.pos args
    | PrimApp (op, args) ->
        let args = Vector.map (expand define_toplevel env) args in
        {expr with v = PrimApp (op, args)}
    (*| PrimBranch (op, iargs, args, clauses) ->
        {expr with v = PrimBranch (op, Vector.map (expand define_toplevel env) iargs
            , Vector.map (expand define_toplevel env) args
            , Vector.map (expand_clause define_toplevel env) clauses)}*)

    | PiT {domain; eff; codomain} ->
        let (domain, env) = expand_pat define_toplevel ignore env domain in
        let eff = Option.map (expand define_toplevel env) eff in
        let codomain = expand define_toplevel env codomain in
        {expr with v = PiT {domain; eff; codomain}}
    | ImpliT {domain; codomain} ->
        let (domain, env) = expand_pat define_toplevel ignore env domain in
        let codomain = expand define_toplevel env codomain in
        {expr with v = ImpliT {domain; codomain}}

    | Ann (expr, typ) ->
        let expr = expand define_toplevel env expr in
        let typ = expand define_toplevel env typ in
        {expr with v = Ann (expr, typ)}

    | Tuple exprs ->
        {expr with v = Tuple (Vector.map (expand define_toplevel env) exprs)}
        (*let end_pos = snd expr.pos in
        exprs |> Vector.fold_right (fun acc expr ->
            { Util.v = Expr.Tuple (Vector.of_array_unsafe [|expr; acc|])
            ; pos = (fst expr.pos, end_pos) }
        ) {v = Tuple Vector.empty; pos = (end_pos, end_pos)}*)

    | Focus (focusee, index) ->
        let focusee = expand define_toplevel env focusee in
        {expr with v = Focus (focusee, index)}
        (*let span = expr.pos in
        let rec get focusee = function
            | 0 -> {Util.v = Expr.Focus (focusee, 0); pos = span}
            | index ->
                let focusee = {Util.v = Expr.Focus (focusee, 1); pos = span} in
                get focusee (index - 1) in
        get (expand define_toplevel env focusee) index*)

    | TupleT typs ->
        {expr with v = Tuple (Vector.map (expand define_toplevel env) typs)}
        (*let end_pos = snd typ.pos in
        typs |> Vector.fold_right (fun acc (typ : expr) ->
            { Util.v = TupleT (Vector.of_array_unsafe [|typ; acc|])
            ; pos = (fst typ.pos, end_pos)}
        ) {v = TupleT Vector.empty; pos = (end_pos, end_pos)}*)

    | Record stmts ->
        (* TODO: Field punning (tricky because the naive translation `letrec x = x in {x = x}` makes no sense) *)
        let vars = CCVector.create () in
        let stmts = expand_stmts define_toplevel (CCVector.push vars) env stmts in
        {expr with v = Record stmts}
        (*let defs = stmts |> Vector.map (function
            | Stmt.Def (span, pat, expr) -> (span, pat, expr)
            | Expr _ -> failwith "non-def stmt in Record") in
        let body : expr = {expr with v = Record (Vector.build vars)} in
        (match Vector1.of_vector defs with
        | Some defs -> {expr with v = Let (defs, body)}
        | None -> body)*)

    | Select (selectee, label) ->
        {expr with v = Select (expand define_toplevel env selectee, label)}

    | RecordT decls | VariantT decls | RowT decls ->
        let vars = CCVector.create () in
        let decls = expand_decls define_toplevel (CCVector.push vars) env decls in
        {expr with v = match expr.v with
            | RecordT _ -> RecordT decls
            | VariantT _ -> VariantT decls
            | RowT _ -> RowT decls
            | _ -> unreachable (Some expr.pos)}
        (*let body : expr = match typ.v with
            | RecordT _ -> {typ with v = RecordT (Vector.build vars)}
            | VariantT _ -> {typ with v = VariantT (Vector.build vars)}
            | RowT _ -> {typ with v = RowT (Vector.build vars)}
            | _ -> unreachable (Some typ.pos) in
        (match Vector1.of_vector decls with
        | Some decls -> {typ with v = Declare (decls, body)}
        | None -> body)*)

    (*| Declare (decls, body) ->
        let (decls, env) = expand_decls' define_toplevel ignore env (Vector1.to_vector decls) in
        let body = expand_typ define_toplevel env body in
        (match Vector1.of_vector decls with
        | Some decls -> {typ with v = Declare (decls, body)}
        | None -> body)*)

    | Var name -> (match Env.find (snd (Bindings.find env name)) with
        | Some (Var id) -> id
        | Some _ -> todo (Some expr.pos)
        | None -> failwith ("unbound: " ^ Name.to_string name
            ^ " at " ^ Util.span_to_string expr.pos))

    | Const _ | PrimT _ -> expr

    | Wild _ -> failwith "stray `_`"


(* # Special Forms *)

(*and expand_let define_toplevel env pos (arg : expr) = match arg.v with
    | Record stmts ->
        let defs = Stream.from (Vector.to_source stmts)
            |> Stream.take_while (function Stmt.Def _ -> true | Expr _ -> false)
            |> Stream.map (function
                | Stmt.Def (span, pat, expr) -> (span, pat, expr)
                | Expr expr -> unreachable (Some expr.pos))
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
        else todo (Some pos)
    | _ -> failwith "non-record `let` arg"*)

and expand_include env args =
    match Vector.length args with
    | 1 ->
        let arg = Vector.get args 0 in
        (match arg.v with
        | Const (String filename) -> (* FIXME: error handling: *)
            let path = match Env.find (snd (Bindings.find env (Name.of_string "__BROOMPATH"))) with
                | Some (BroomPath path) -> path
                | Some _ -> bug (Some arg.pos) ~msg: "__BROOMPATH has wrong type"
                | None -> bug (Some arg.pos) ~msg: "__BROOMPATH unbound" in
            let filename = path |> List.find_map (fun dir ->
                let filename = Filename.concat dir filename ^ ".brm" in
                if Sys.file_exists filename
                then Some filename
                else None) in
            let filename = Option.get filename in
            let input = open_in filename in
            Fun.protect (fun () ->
                input
                |> Sedlexing.Utf8.from_channel
                |> SedlexMenhir.create_lexbuf filename
                |> SedlexMenhir.sedlex_with_menhir Lexer.token Parser.modul
            ) ~finally: (fun () -> close_in input)
        | _ -> failwith "non-string-literal `include` arg")
    | _ -> todo None

(* TODO: canonicalize (?) filename: *)
and expand_require define_toplevel env pos args =
    match Vector.length args with
    | 1 ->
        let arg = Vector.get args 0 in
        (match arg.v with
        | Const (String filename) ->
            let name = 
                match Env.find (snd (Bindings.find env (Name.of_string "__requireCache"))) with
                | Some (RequireCache requireds) -> (match StringHashtbl.find_opt requireds filename with
                    | Some name -> name
                    | None ->
                        let name = Name.fresh () in
                        StringHashtbl.add requireds filename name;
                        let var : expr = {pos; v = Var name} in
                        let incl : expr = {pos; v = Var (Name.of_string "include")} in
                        let load = expand define_toplevel env {pos
                            ; v = App (Vector.of_array_unsafe [|incl; arg|])} in
                        let def : def = (pos, var, load) in
                        define_toplevel def;
                        name)
                | Some _ -> bug (Some pos) ~msg: "__requireCache has wrong type"
                | None -> bug (Some pos) ~msg: "__requireCache is unbound" in
            {Util.pos; v = Expr.Var name}
        | _ -> failwith "non-string-literal `include` arg")
    | _ -> todo None

(* # Patterns *)

and expand_pat define_toplevel report_def env (pat : expr) =
    match pat.v with
    | Ann (pat, typ) ->
        let (pat, env) = expand_pat define_toplevel report_def env pat in
        let typ = expand define_toplevel env typ in
        ({pat with v = Ann (pat, typ)}, env)

    | Tuple pats ->
        let pats' = CCVector.create () in
        let env = Vector.fold (fun env pat ->
            let (pat, env) = expand_pat define_toplevel report_def env pat in
            CCVector.push pats' pat;
            env
        ) env pats in
        let pats = Vector.build pats' in (* OPTIMIZE *)

        let end_pos = snd pat.pos in
        ( pats |> Vector.fold_right (fun acc pat ->
              { Util.v = Expr.Tuple (Vector.of_array_unsafe [|pat; acc|])
              ; pos = (fst pat.pos, end_pos) }
          ) {v = Tuple Vector.empty; pos = (end_pos, end_pos)}
        , env )

    | Focus (focusee, label) ->
        let (focusee, env) = expand_pat define_toplevel report_def env focusee in
        ({pat with v = Focus (focusee, label)}, env)

    | Var name ->
        let name' = Name.freshen name in
        let id' = {pat with v = Expr.Var name'} in
        report_def (Stmt.Def (pat.pos, pat, id'));
        Env.add name' (Var id');
        ({pat with v = Var name'}, Bindings.add env name (None, name'))

    | Wild _ | Const _ -> (pat, env)

    | _ -> todo (Some pat.pos)

(* # Clauses *)

and expand_clause define_toplevel env ({params; body} : clause) : clause =
    let (params, env) = expand_pat define_toplevel ignore env params in
    {params; body = expand define_toplevel env body}

(* # Definitions *)

and expand_def_pat define_toplevel report_def env pos pat expr =
    let (pat, env) = expand_pat define_toplevel report_def env pat in
    ((pos, pat, expr), env)

and expand_def define_toplevel env pos pat expr =
    (pos, pat, expand define_toplevel env expr)

(*and expand_defs' define_toplevel env defs =
    let defs' = CCVector.create () in
    let env = Vector.fold (fun env (span, pat, expr) ->
        let (def', env) = expand_def_pat define_toplevel ignore env span pat expr in
        CCVector.push defs' def';
        env
    ) env defs in
    defs' |> CCVector.map_in_place (fun (span, pat, expr) ->
        expand_def define_toplevel env span pat expr);
    (Vector.build defs', env)*)

(* # Statements *)

and expand_stmt_pat define_toplevel report_def env : stmt -> stmt * Bindings.t = function
    | Def (span, pat, expr) ->
        let ((span, pat, expr), env) = expand_def_pat define_toplevel report_def env span pat expr in
        (Def (span, pat, expr), env)

    | Expr _ as stmt -> (stmt, env)

and expand_stmt define_toplevel env : stmt -> stmt = function
    | Def (span, pat, expr) ->
        let (span, pat, expr) = expand_def define_toplevel env span pat expr in
        Def (span, pat, expr)

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

(* # Declarations *)

and expand_decl_pat define_toplevel report_def env = function
    | Decl.Def (span, pat, expr) ->
        let report_def = function
            | Stmt.Def (span, pat, expr) -> report_def (Decl.Def (span, pat, expr))
            | stmt -> unreachable (Some (Stmt.pos stmt)) in
        let ((span, pat, expr), env) = expand_def_pat define_toplevel report_def env span pat expr in
        (Decl.Def (span, pat, expr), env)

    | Decl (pos, pat, typ) ->
        let report_def = function
            | Stmt.Def (pos, pat, expr) ->
                let expr = {expr with v = Expr.PrimApp (TypeOf, Vector.singleton expr)} in
                report_def (Decl.Decl (pos, pat, expr))
            | stmt -> unreachable (Some (Stmt.pos stmt)) in
        let (pat, env) = expand_pat define_toplevel report_def env pat in
        (Decl (pos, pat, typ), env)

    | Type _ as decl -> (decl, env)

and expand_decl define_toplevel env = function
    | Decl.Def (span, pat, expr) ->
        let (span, pat, expr) = expand_def define_toplevel env span pat expr in
        Decl.Def (span, pat, expr)

    | Decl (span, pat, typ) ->
        let (span, pat, typ) = expand_def define_toplevel env span pat typ in
        Decl (span, pat, typ)

    | Type typ -> Type (expand define_toplevel env typ)

and expand_decls' define_toplevel report_def env decls =
    let decls' = CCVector.create () in
    let env = Vector.fold (fun env decl ->
        let (decl', env) = expand_decl_pat define_toplevel report_def env decl in
        CCVector.push decls' decl';
        env
    ) env decls in
    CCVector.map_in_place (expand_decl define_toplevel env) decls';
    (Vector.build decls', env)

and expand_decls define_toplevel report_def env decls =
    fst (expand_decls' define_toplevel report_def env decls)

(* # Top-level Expansion API *)

let expand_program env {Ast.Program.span; defs; body} =
    let defs' = CCVector.create () in
    let env = Vector.fold (fun env (span, pat, expr) ->
        let (def', env) = expand_def_pat (CCVector.push defs') ignore env span pat expr in
        CCVector.push defs' def';
        env
    ) env defs in
    let defs = defs' and defs' = CCVector.create () in
    defs |> CCVector.iter (fun (span, pat, expr) ->
        CCVector.push defs' (expand_def (CCVector.push defs') env span pat expr)
    );
    let body = expand (CCVector.push defs') env body in
    {Ast.Program.span; defs = Vector.build defs'; body}

(* TODO: Use Namespace: *)
let expand_interactive_stmt env stmt =
    let defs = CCVector.create () in
    let define_toplevel = CCVector.push defs in
    let (stmt, env) = expand_stmt_pat define_toplevel ignore env stmt in
    let stmt = expand_stmt define_toplevel env stmt in
    let stmts = CCVector.map (fun (span, pat, expr) -> Stmt.Def (span, pat, expr)) defs in
    CCVector.push stmts stmt;
    (env, Option.get (Vector1.of_vector (Vector.build stmts)))

end

