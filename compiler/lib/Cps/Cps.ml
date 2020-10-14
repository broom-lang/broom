module S = CpsSigs

type span = Util.span

module Type = struct
    type param = Fc.Type.binding

    type t =
        | Prim of Prim.t

    let param_to_doc = Fc.Type.binding_to_doc (TxRef.log ()) (* HACK *)

    let to_doc = function
        | Prim p -> Prim.to_doc p
end

module ContId = Id.Make ()

module Expr = struct
    type cont_id = ContId.t
    module Type = Type

    module Id = Id.Make ()

    type t' =
        | Const of Const.t

    type t =
        { pos : span
        ; cont : cont_id option
        ; typ : Type.t
        ; term : t' }

    let id_to_doc id = PPrint.(percent ^^ Id.to_doc id)

    let to_doc (expr : t) = match expr.term with
        | Const c -> Const.to_doc c

    let def_to_doc id expr =
        let open PPrint in
        infix 4 1 equals (infix 4 1 colon (id_to_doc id) (Type.to_doc expr.typ))
            (to_doc expr)
end

module Transfer = struct
    module Type = Type
    type expr_id = Expr.Id.t

    type t' =
        | Return of Type.t Vector.t * expr_id Vector.t

    type t = {pos : span; term : t'}

    let to_doc (transfer : t) =
        let open PPrint in
        match transfer.term with
        | Return (universals, args) ->
            string "return"
            ^/^ surround_separate_map 4 0 langle (angles empty) rangle
                (comma ^^ break 1) Type.to_doc (Vector.to_list universals)
            ^/^ surround_separate_map 4 0 lparen (parens empty) rparen
                (comma ^^ break 1) Expr.id_to_doc (Vector.to_list args)
end

module Cont = struct
    module Type = Type
    module Transfer = Transfer

    module Id = ContId

    type t =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : Type.t Vector.t
        ; body : Transfer.t }

    let id_to_doc id = PPrint.(dollar ^^ Id.to_doc id)

    let to_doc {pos = _; name; universals; params; body} ~exprs_doc =
        let open PPrint in
        string "fn" ^^ blank 1
        ^^ Option.fold ~some: Name.to_doc ~none: empty name ^^ blank 1
        ^^ surround_separate_map 4 0 (angles empty)
            langle (comma ^^ break 1) rangle
            Type.param_to_doc (Vector.to_list universals)
        ^^ blank 1 ^^ surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            Type.to_doc (Vector.to_list params)
        ^^ blank 1 ^^ surround 4 1 lbrace rbrace
            (exprs_doc ^^ semi ^^ hardline ^^ Transfer.to_doc body)

    let def_to_doc id cont ~exprs_doc =
        PPrint.(infix 4 1 equals (id_to_doc id) (to_doc cont ~exprs_doc))
end

module Program = struct
    module Type = Type
    module Expr = Expr
    module Cont = Cont

    module Exprs = Expr.Id.HashMap
    module Conts = Cont.Id.HashMap

    type t =
        { type_fns : Type.param Vector.t
        ; exprs : Expr.t Exprs.t
        ; conts : Cont.t Conts.t
        ; main : Cont.Id.t }

    type builder =
        { type_fns : Type.param Vector.t
        ; mutable exprs : Expr.t Exprs.t
        ; mutable conts : Cont.t Conts.t
        ; transient : CCHashTrie.Transient.t }

    let to_doc {type_fns; exprs; conts; main} =
        let open PPrint in
        let cont_exprs = Cont.Id.Hashtbl.create (Conts.cardinal conts) in
        Exprs.iter ~f: (fun id (expr : Expr.t) -> match expr.cont with
            | Some cont_id ->
                Cont.Id.Hashtbl.replace cont_exprs cont_id 
                    (Cont.Id.Hashtbl.find_opt cont_exprs cont_id
                    |> Option.value ~default: []
                    |> (fun kvs -> (id, expr) :: kvs))
            | None -> ()
        ) exprs;
        let cont_exprs_doc id =
            separate_map (twice hardline) (fun (id, expr) ->
                Expr.def_to_doc id expr ^^ semi
            ) (Cont.Id.Hashtbl.find_opt cont_exprs id |> Option.value ~default: []) in

        separate_map (twice hardline) (fun typedef ->
            string "type" ^^ blank 1 ^^ Type.param_to_doc typedef ^^ semi
        ) (Vector.to_list type_fns) ^^ twice (twice hardline)
        ^^ separate_map (twice hardline) (fun (id, expr) ->
            Expr.def_to_doc id expr ^^ semi
        ) (Exprs.to_list exprs (* orphan defs *)
            |> List.filter (fun (_, (expr : Expr.t)) -> Option.is_none expr.cont))
        ^^ twice (twice hardline)
        ^^ separate_map (twice hardline) (fun (id, cont) ->
            Cont.def_to_doc id cont ~exprs_doc: (cont_exprs_doc id)
        ) (Conts.to_list conts (* non-main conts *)
            |> List.filter (fun (id, _) -> not (Cont.Id.equal id main)))
        ^^ twice hardline ^^ Cont.def_to_doc main (Conts.get_exn main conts)
            ~exprs_doc: (cont_exprs_doc main)

    module Builder = struct
        let create type_fns =
            { type_fns
            ; exprs = Exprs.empty
            ; conts = Conts.empty
            ; transient = CCHashTrie.Transient.create () }

        let express (builder : builder) expr =
            let id = Expr.Id.fresh () in
            builder.exprs <- Exprs.add_mut ~id: builder.transient id expr builder.exprs;
            id

        let add_cont (builder : builder) id k =
            builder.conts <- Conts.add_mut ~id: builder.transient id k builder.conts

        let build {type_fns; exprs; transient; conts} main =
            CCHashTrie.Transient.freeze transient;
            {type_fns; exprs; conts; main}

        type t = builder
    end
end

