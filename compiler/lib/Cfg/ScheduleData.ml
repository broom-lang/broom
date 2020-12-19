open Streaming
module Builder = Cfg.Program.Builder
module Params = Cps.Cont.Id.Hashtbl

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
        | _ -> failwith "unreachable"));
    params

let get_param (params : params) label index =
    let label_params = Params.find_opt params label in
    Option.bind label_params (fun label_params ->
        Hashtbl.find_opt label_params index)

let schedule program =
    let module Renamings = Cps.Expr.Id.Hashtbl in
    let module VisitedSet = Cps.Expr.Id.HashSet in
    let main = match Stream.from (Cps.Program.exports program) |> Stream.into Sink.list with
        | [main] -> main
        | _ -> failwith "FIXME: multiple exports" in

    let params = find_params program in
    let get_param = get_param params in

    let builder = Builder.create (Cps.Program.type_fns program) main in

    let renamings = Renamings.create 0 in
    let add_renaming = Renamings.add renamings in
    let rename id = Renamings.find_opt renamings id in

    let visiteds = VisitedSet.create 0 in
    let is_visited = VisitedSet.mem visiteds in
    let set_visited = VisitedSet.insert visiteds in

    (* TODO: Remove PrimApp-ordering state edges, emit `Expr` stmts when necessary. *)
    let rec emit_expr id =
        match rename id with
        | Some id -> id
        | None ->
            if is_visited id
            then ()
            else begin
                set_visited id;
                let {Cps.Expr.pos; cont = parent; typ; term} as expr = Cps.Program.expr program id in
                match parent with
                | Some parent ->
                    emit_cont parent;
                    Cps.Expr.iter_labels emit_cont expr;
                    let term = Cps.Expr.map_uses emit_expr term in
                    Builder.define builder parent {Cfg.Stmt.pos; typ; term = Def (id, term)}
                | None -> failwith "compiler bug: unparented expr in ScheduleData"
            end;
            id

    and emit_transfer ({pos; term} : Cps.Transfer.t) : Cfg.Transfer.t =
        let term : Cfg.Transfer.t' = match term with
            | Goto {universals; callee; args} ->
                emit_cont callee;
                Goto {universals; callee; args = Vector.map emit_expr args}

            | Jump {universals; callee; args} ->
                Jump {universals; callee = emit_expr callee
                    ; args = Vector.map emit_expr args}

            | Return (universals, args) ->
                Return (universals, Vector.map emit_expr args)

            | Match {matchee; state; clauses} ->
                let matchee = emit_expr matchee in
                let state = emit_expr state in
                Vector.iter (emit_clause state) clauses;
                Match {matchee; clauses}

            | PrimApp {op; universals; state; args; clauses} ->
                let state = emit_expr state in
                let args = Vector.map emit_expr args in
                Vector.iter (emit_clause state) clauses;
                PrimApp {op; universals; args; clauses} in
        {pos; term}

    and emit_clause state' {pat = _; dest = label} =
        if Builder.cont_mem builder label 
        then ()
        else begin
            let ({params; body; _} as cont) : Cps.Cont.t = Cps.Program.cont program label in
            (* FIXME: Need to shift Params so that `$1 # 1` -> `$1 # 0` etc.
                But that will become irrelevant if `Cfg` is switched to named params instead. *)
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

