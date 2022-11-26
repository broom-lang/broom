open Streaming
open Asserts

module Builder = Cfg.Program.Builder
module Params = Cps.Cont.Id.Hashtbl

(* TODO: Get rid of remaining tuples (e.g. primop results, also non-state ones. *)

type params = (int, Cps.Expr.Id.t) Hashtbl.t Params.t

let is_param : Cps.Expr.t' -> bool = function
    | Param _ -> true
    | _ -> false

let find_params program =
    let params = Params.create 0 in
    let add_param label index id = match Params.find_opt params label with
        | Some label_params -> Hashtbl.add label_params index id
        | None ->
            let label_params = Hashtbl.create 0 in
            Hashtbl.add label_params index id;
            Params.add params label label_params in
    Cps.Program.exprs program
    |> Stream.filter (fun (_, (expr : Cps.Expr.t)) -> is_param expr.term)
    |> Stream.into (Sink.each (fun (id, (expr : Cps.Expr.t)) ->
        match expr.term with
        | Cps.Expr.Param {label; index} -> add_param label index id
        | _ -> unreachable (Some expr.pos)));
    params

let get_param (params : params) label index =
    let label_params = Params.find_opt params label in
    Option.bind label_params (fun label_params ->
        Hashtbl.find_opt label_params index)

let schedule_program program params =
    let module Renamings = Cps.Expr.Id.Hashtbl in
    let module VisitedSet = Cps.Expr.Id.HashSet in
    let main = match Stream.from (Cps.Program.exports program) |> Stream.into Sink.list with
        | [main] -> main
        | _ -> todo None ~msg: "multiple exports" in

    let get_param = get_param params in

    let builder = Builder.create (Cps.Program.type_fns program) main in

    let renamings = Renamings.create 0 in
    let add_renamings = Renamings.add renamings in
    let add_renaming id id' = add_renamings id (Vector.singleton id') in
    let rename id i =
        Renamings.find_opt renamings id |> Option.map (Fun.flip Vector.get i) in

    let visiteds = VisitedSet.create 0 in
    let is_visited = VisitedSet.mem visiteds in
    let set_visited = VisitedSet.insert visiteds in

    let rec emit_use id =
        let rec emit_expr id ({Cps.Expr.pos; cont = parent; typ; term} as expr) =
            match parent with
            | Some parent -> (match term with
                | Param {label; index} -> Builder.add_param builder label index id; id
                (*| Focus {focusee; index} ->
                    (* dont' `rename` via recursion, that always uses 0 as index: *)
                    let focusee = emit_use' focusee in
                    let id' = rename focusee index |> Option.get in
                    add_renaming id id';
                    id'*)
                | PrimApp {op; universals; args} when not (Primop.is_pure op) ->
                    emit_cont parent;
                    Cps.Expr.iter_labels' emit_cont term;
                    let args = Vector.map emit_use args in
                    let state = Vector.get args 0 in
                    let term = Cps.Expr.PrimApp {op; universals
                        ; args = Vector.sub args 1 (Vector.length args - 1)} in
                    let defs = match typ with
                        | Pair {fst = _; snd} ->
                            (match snd with
                            | Prim Unit -> Vector.singleton state
                            | _ -> Vector.of_list [state; id])
                        | _ -> bug (Some pos) ~msg: "invalid impure primop" in
                    add_renamings id defs;
                    Builder.define builder parent {Cfg.Stmt.pos; typ
                        ; term = (Vector.sub defs 1 (Vector.length defs - 1), term)};
                    id
                | _ ->
                    emit_cont parent;
                    Cps.Expr.iter_labels emit_cont expr;
                    let term = Cps.Expr.map_uses' emit_use term in
                    Builder.define builder parent {Cfg.Stmt.pos; typ; term = (Vector.singleton id, term)};
                    id)
            | None -> bug (Some pos) ~msg: "unparented expr in ScheduleData"

        and emit_use' id =
            if is_visited id
            then id
            else begin
                set_visited id;
                emit_expr id (Cps.Program.expr program id)
            end in

        match rename id 0 with
        | Some id' -> id'
        | None -> emit_use' id

    and emit_transfer ({pos; term} : Cps.Transfer.t) : Cfg.Transfer.t =
        let term : Cfg.Transfer.t' = match term with
            | Goto {universals; callee; args} ->
                emit_cont callee;
                Goto {universals; callee; args = Vector.map emit_use args}

            | Jump {universals; callee; args} ->
                Jump {universals; callee = emit_use callee
                    ; args = Vector.map emit_use args}

            | Return (universals, args) ->
                Return (universals, Option.map emit_use args)

            | Match {matchee; state; clauses} ->
                let matchee = emit_use matchee in
                let state = emit_use state in
                Vector.iter (emit_clause state) clauses;
                Match {matchee; clauses}

            | PrimApp {op; universals; state; args; clauses} ->
                let state = emit_use state in
                let args = Vector.map emit_use args in
                Vector.iter (emit_clause state) clauses;
                PrimApp {op; universals; args; clauses} in
        {pos; term}

    and emit_clause state' {pat = _; dest = label} =
        if Builder.cont_mem builder label 
        then ()
        else begin
            let ({params; body; _} as cont) : Cps.Cont.t = Cps.Program.cont program label in
            Builder.add_cont builder label {cont with
                params = Vector.sub params 1 (Vector.length params - 1)};
            Option.iter (fun state -> add_renaming state state') (get_param label 0);
            let transfer = emit_transfer body in
            Builder.set_transfer builder label transfer
        end

    and emit_cont label =
        if Builder.cont_mem builder label
        then ()
        else begin
            let ({body; _} as cont) : Cps.Cont.t = Cps.Program.cont program label in
            Builder.add_cont builder label cont;
            let transfer = emit_transfer body in
            Builder.set_transfer builder label transfer
        end in

    Source.each emit_cont (Cps.Program.exports program);
    Builder.build builder

(* # All Together Now *)

let schedule program = schedule_program program (find_params program)

