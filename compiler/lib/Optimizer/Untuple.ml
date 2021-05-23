open Streaming
open Asserts

open Cps
module Transient = Program.Transient
module Builder = Program.Builder

(* FIXME: convert type annotations *)
(* TODO: Handle other 0/multi-register types (via kind levity) *)

module Params = struct
    module ContParams = Cont.Id.Hashtbl

    (* Sparse; can not contain unused/expressionless params: *)
    module ParamsByIndex = Hashtbl.Make (struct
        include Int
        let hash = Hashtbl.hash
    end)

    type t = (Expr.Id.t * Expr.t) ParamsByIndex.t ContParams.t

    let create = ContParams.create

    let add params label index id expr =
        let label_params = match ContParams.find_opt params label with
            | Some label_params -> label_params
            | None ->
                let label_params = ParamsByIndex.create 0 in
                ContParams.add params label label_params;
                label_params in
        ParamsByIndex.add label_params index (id, expr)

    let get params label index =
        let (let*) = Option.bind in
        let* label_params = ContParams.find_opt params label in
        ParamsByIndex.find_opt label_params index
end

(* # Analysis *)

let is_param (expr : Expr.t) = match expr.term with
    | Param _ -> true
    | _ -> false

let gather_program_params program : Params.t =
    let params = Params.create 0 in

    Program.exprs program
    |> Stream.filter (fun (_, expr) -> is_param expr)
    |> Stream.each (fun (id, (expr : Expr.t)) -> match expr.term with
        | Expr.Param {label; index} -> Params.add params label index id expr
        | _ -> Asserts.unreachable None);

    params

(* # Transformation *)

(* TODO: Expand primop results similarly (?): *)
(* Replace (possibly nested) tuple params with separate params that are
 * tupled explicitly inside the cont. *)
let expand_program_params program all_params =
    let program' = Transient.from program in

    let expand_cont (label, {Cont.pos; name; universals; params; body}): unit =
        let params' = CCVector.create () in

        let expand_param index' (index, typ) : int =
            let rec expand_sub_param index (id : Expr.Id.t option) (typ : Type.t) : int =
                let (term, index') = match typ with
                    | Pair {fst = fst_typ; snd = snd_typ} ->
                        let fst_id = Expr.Id.fresh () in
                        let index = expand_sub_param index (Option.map (Fun.const fst_id) id) fst_typ in
                        let snd_id = Expr.Id.fresh () in
                        let index = expand_sub_param index (Option.map (Fun.const snd_id) id) snd_typ in
                        ( Expr.PrimApp {op = Pair
                            ; universals = Vector.of_array_unsafe [|fst_typ; snd_typ|]
                            ; args = Vector.of_array_unsafe [|fst_id; snd_id|]}
                        , index )

                    | typ ->
                        CCVector.push params' typ;
                        (Param {label; index}, index + 1) in
                id |> Option.iter (fun id ->
                    Transient.add_expr program' id {pos; typ; cont = Some label; term});
                index' in

            match Params.get all_params label index with
            | Some (id, _ (* TODO(?): expr *)) -> (match typ with
                | Type.Pair _ -> expand_sub_param index' (Some id) typ
                | _ when index' = index -> (* fast path *)
                    CCVector.push params' typ;
                    index' + 1
                | _ -> expand_sub_param index' (Some id) typ)
            | None -> expand_sub_param index' None typ in

        let _ = Stream.from (Vector.to_source params)
            |> Stream.indexed
            |> Stream.fold expand_param 0 in
        {Cont.pos; name; universals; params = Vector.build params'; body}
        |> Transient.add_cont program' label in

    Stream.each expand_cont (Program.conts program);
    Transient.persist program'

(* Destructure (possibly nested) tuple args and pass the elements separately. *)
let untuple_args program =
    let builder = Builder.create (Program.type_fns program) in
    let visited_exprs = Expr.Id.Hashtbl.create 0 in
    let visited_conts = Cont.Id.HashSet.create 0 in

    let rec optimize_arg arg =
        let expr = Builder.expr builder arg in
        match expr.typ with
        | Pair {fst = fst_typ; snd = snd_typ} ->
            let fst = Builder.express builder {typ = fst_typ
                ; pos = expr.pos; cont = expr.cont
                ; term = PrimApp {op = Fst; universals = Vector.singleton fst_typ
                    ; args = Vector.singleton arg}}
                |> optimize_arg in
            let snd = Builder.express builder {typ = snd_typ
                ; pos = expr.pos; cont = expr.cont
                ; term = PrimApp {op = Snd; universals = Vector.singleton snd_typ
                    ; args = Vector.singleton arg}}
                |> optimize_arg in
            Stream.concat fst snd

        | _ -> Stream.single arg in

    let rec optimize_args args =
        Stream.from (Vector.to_source args)
        |> Stream.flat_map (fun arg -> optimize_arg (optimize_use arg))
        |> Stream.into (Vector.sink ())

    and optimize_use use : Expr.Id.t =
        let optimize_expr (expr : Expr.t) = match expr.term with
            | PrimApp {op; universals; args} ->
                Builder.express builder {expr
                    with term = PrimApp {op; universals; args = optimize_args args}}
            | Record _ | With _ | Where _ | Select _ | Proxy _
            | Label _ | Param _ | Cast _ | Pack _ | Unpack _ | Const _ ->
                Expr.iter_labels optimize_label expr;
                Builder.express builder (Expr.map_uses optimize_use expr) in

        match Expr.Id.Hashtbl.find_opt visited_exprs use with
        | Some use' -> use'
        | None ->
            let use' = optimize_expr (Program.expr program use) in
            Expr.Id.Hashtbl.add visited_exprs use use';
            use'

    and optimize_label label : unit =
        let optimize_transfer ({Transfer.term; pos = _} as transfer) =
            let optimize_clause {Transfer.pat = _; dest} = optimize_label dest in

            match term with
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
            | Return (universals, args) -> (match args with
                | Some arg ->
                    let args = Stream.into (Vector.sink ()) (optimize_arg arg) in
                    {transfer with term =
                        match Vector.length args with
                        | 0 -> Transfer.Return (None, None)
                        | 1 -> Return (universals, Some (Vector.get args 0))
                        | _ -> unreachable (Some transfer.pos)}
                | None -> transfer) in

        let optimize_cont {Cont.pos; name; universals; params; body} =
            let body = optimize_transfer body in
            Builder.add_cont builder label
                {pos; name; universals; params; body} in

        if not (Cont.Id.HashSet.mem visited_conts label) then begin
            Cont.Id.HashSet.insert visited_conts label;
            optimize_cont (Program.cont program label)
        end in

    Stream.each optimize_label (Stream.from (Program.exports program));
    Builder.build builder (Program.main program)

(* # All Together Now *)

let untuple program =
    gather_program_params program
    |> expand_program_params program
    |> untuple_args

