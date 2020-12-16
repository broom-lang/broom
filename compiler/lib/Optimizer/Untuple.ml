open Streaming

open Cps
module Transient = Program.Transient
module Builder = Program.Builder
module Params = Cont.Id.Hashtbl

(* FIXME: convert type annotations *)
(* TODO: Handle other 0/multi-register types (via kind levity) *)

type params = (int, (Expr.Id.t * Expr.t)) Hashtbl.t Params.t

let is_param : Expr.t' -> bool = function
    | Param _ -> true
    | _ -> false

let find_params program : params =
    let params = Params.create 0 in
    let add_param label index id expr = match Params.find_opt params label with
        | Some label_params -> Hashtbl.add label_params index (id, expr)
        | None ->
            let label_params = Hashtbl.create 0 in
            Hashtbl.add label_params index (id, expr);
            Params.add params label label_params in

    Program.exprs program
    |> Stream.filter (fun (_, (expr : Expr.t)) -> is_param expr.term)
    |> Stream.each (fun (id, (expr : Expr.t)) ->
        match expr.term with
        | Expr.Param {label; index} -> add_param label index id expr
        | _ -> failwith "unreachable");
    params

let get_param (params : params) label index =
    Option.bind (Params.find_opt params label)
        (fun label_params -> Hashtbl.find_opt label_params index)

(* TODO: Expand primop results similarly (?): *)
let expand_all_params program =
    let all_params = find_params program in
    let program' = Transient.from program in

    let expand_cont (label, {Cont.pos; name; universals; params; body}) =
        let params' = CCVector.create () in

        let rec expand_sub_param index id = function
            | Type.Tuple typs as typ ->
                let elems = Vector.map (fun _ -> Expr.Id.fresh ()) typs in
                let index = Stream.from (Source.zip
                        (Vector.to_source elems) (Vector.to_source typs))
                    |> Stream.fold (fun index (id, typ) ->
                        expand_sub_param index id typ
                    ) index in
                Transient.add_expr program' id {pos; typ; cont = Some label
                    ; term = Tuple elems};
                index
            | typ ->
                CCVector.push params' typ;
                Transient.add_expr program' id {pos; typ; cont = Some label
                    ; term = Param {label; index}};
                index + 1 in

        let expand_param index' index typ =
            match get_param all_params label index with
            | Some (id, _ (* TODO(?): expr *)) -> (match typ with
                | Type.Tuple _ -> expand_sub_param index' id typ
                | _ when index' = index -> (* fast path *)
                    CCVector.push params' typ;
                    index' + 1
                | _ -> expand_sub_param index' id typ)
            | None -> expand_sub_param index' (Expr.Id.fresh ()) typ in

        Stream.from (Vector.to_source params)
        |> Stream.indexed
        |> Stream.fold (fun index' (index, typ) -> expand_param index' index typ) 0
        |> ignore;

        {Cont.pos; name; universals; params = Vector.build params'; body}
        |> Transient.add_cont program' label in

    Stream.each expand_cont (Program.conts program);
    Transient.persist program'

let untuple program =
    let program = expand_all_params program in

    let builder = Builder.create (Program.type_fns program) in
    let visited_exprs = Expr.Id.Hashtbl.create 0 in
    let visited_conts = Cont.Id.HashSet.create 0 in

    let rec optimize_use use =
        match Expr.Id.Hashtbl.find_opt visited_exprs use with
        | Some use -> use
        | None ->
            Expr.Id.Hashtbl.add visited_exprs use use;
            let expr = Program.expr program use in
            let use' = match expr.term with
                | PrimApp {op; universals; args} ->
                    {expr with term = PrimApp {op; universals; args = optimize_args args}}
                    |> Builder.express builder
                | Tuple _ | Focus _
                | Record _ | With _ | Where _ | Select _ | Proxy _
                | Label _ | Param _ | Const _ ->
                    Expr.iter_labels optimize_label expr;
                    Expr.map_uses optimize_use expr
                    |> Builder.express builder in
            Expr.Id.Hashtbl.add visited_exprs use use';
            use'

    and optimize_args args =
        let rec optimize_arg arg =
            let expr = Builder.expr builder arg in
            match expr.typ with
            | Tuple typs ->
                Stream.from (Vector.to_source typs)
                |> Stream.indexed
                |> Stream.flat_map (fun (index, typ) ->
                    let arg = Builder.express builder {typ
                        ; pos = expr.pos; cont = expr.cont
                        ; term = Focus {focusee = arg; index}} in
                    optimize_arg arg)
            | _ -> Stream.single arg in

        Stream.from (Vector.to_source args)
        |> Stream.flat_map (fun arg -> optimize_arg (optimize_use arg))
        |> Stream.into (Vector.sink ())

    and optimize_transfer (transfer : Transfer.t) =
        let optimize_clause {Transfer.pat = _; dest} = optimize_label dest in

        match transfer.term with
        | Jump {callee; universals; args} ->
            let callee = optimize_use callee in
            {transfer with term = Jump {callee; universals; args = optimize_args args}}
        | Goto {callee; universals; args} ->
            optimize_label callee;
            {transfer with term = Goto {callee; universals; args = optimize_args args}}
        | Match _ ->
            Transfer.iter_labels optimize_label transfer;
            Transfer.map_uses optimize_use transfer
        | PrimApp {op; universals; args; state; clauses} ->
            Vector.iter optimize_clause clauses;
            {transfer with term = PrimApp {op; universals; args = optimize_args args
                ; state = optimize_use state; clauses}}
        | Return (universals, args) ->
            {transfer with term = Return (universals, optimize_args args)}

    and optimize_label label =
        let optimize_cont {Cont.pos; name; universals; params; body} =
            let body = optimize_transfer body in
            Builder.add_cont builder label
                {pos; name; universals; params; body} in

        if Cont.Id.HashSet.mem visited_conts label
        then ()
        else begin
            Cont.Id.HashSet.insert visited_conts label;
            optimize_cont (Program.cont program label)
        end in

    Stream.from (Program.exports program)
    |> Stream.each optimize_label;

    Builder.build builder (Program.main program)

