module S = CpsSigs

type span = Util.span

module Type = struct
    type kind = Fc.Type.kind
    type param = Fc.Type.binding

    type t =
        | Values of t Vector.t
        | PromotedValues of t Vector.t
        | PromotedArray of t Vector.t
        | Pi of {universals : kind Vector.t; domain : t Vector.t}
        | EmptyRow
        | Prim of Prim.t

    let log = TxRef.log () (* HACK *)
    let kind_to_doc = Fc.Type.kind_to_doc log
    let param_to_doc = Fc.Type.binding_to_doc log

    let rec to_doc typ =
        let open PPrint in
        match typ with
        | Values typs -> surround_separate_map 4 0 (parens colon)
            (lparen ^^ colon) (comma ^^ break 1) rparen
            to_doc (Vector.to_list typs)

        | PromotedValues typs -> surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            to_doc (Vector.to_list typs)

        | PromotedArray typs -> surround_separate_map 4 0 (brackets empty)
            lbracket (comma ^^ break 1) rbracket
            to_doc (Vector.to_list typs)

        | Pi {universals; domain} ->
            prefix 4 1 (string "fn")
                (surround_separate_map 4 0 empty
                    langle (comma ^^ break 1) (rangle ^^ break 1)
                    kind_to_doc (Vector.to_list universals)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    to_doc (Vector.to_list domain))

        | EmptyRow -> parens bar
        | Prim p -> string "__" ^^ Prim.to_doc p
end

module ContId = struct
    include Id.Make ()

    let to_doc id = PPrint.(dollar ^^ to_doc id)
end

module Expr = struct
    type cont_id = ContId.t
    module Type = Type

    module Id = struct
        include Id.Make ()

        let to_doc id = PPrint.(percent ^^ to_doc id)
    end

    type t' =
        | Values of Id.t Vector.t
        | Focus of {focusee : Id.t; index : int}
        | Label of cont_id
        | Param of {label : cont_id; index : int}
        | Const of Const.t

    type t =
        { pos : span
        ; cont : cont_id option
        ; typ : Type.t
        ; term : t' }

    let to_doc (expr : t) =
        let open PPrint in
        match expr.term with
        | Values values ->
            surround_separate_map 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                Id.to_doc (Vector.to_list values)

        | Focus {focusee; index} ->
            infix 4 1 dot (Id.to_doc focusee) (string (Int.to_string index))
        | Label label -> ContId.to_doc label
        | Param {label; index} ->
            infix 4 1 sharp (ContId.to_doc label) (string (Int.to_string index))
        | Const c -> Const.to_doc c

    let def_to_doc id expr =
        let open PPrint in
        infix 4 1 equals (infix 4 1 colon (Id.to_doc id) (Type.to_doc expr.typ))
            (to_doc expr)
end

module Transfer = struct
    module Type = Type
    type expr_id = Expr.Id.t
    type cont_id = ContId.t

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Return of Type.t Vector.t * expr_id Vector.t

    type t = {pos : span; term : t'}

    let args_to_doc universals args =
        let open PPrint in
        surround_separate_map 4 0 empty
            langle (comma ^^ break 1) (rangle ^^ blank 1)
            Type.to_doc (Vector.to_list universals)
        ^^ surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            Expr.Id.to_doc (Vector.to_list args)

    let to_doc (transfer : t) =
        let open PPrint in
        match transfer.term with
        | Goto {universals; callee; args} ->
            prefix 4 1 (string "goto" ^^ blank 1 ^^ ContId.to_doc callee)
                (args_to_doc universals args)

        | Jump {universals; callee; args} ->
            prefix 4 1 (string "jump" ^^ blank 1 ^^ Expr.Id.to_doc callee)
                (args_to_doc universals args)

        | Return (universals, args) ->
            prefix 4 1 (string "return") (args_to_doc universals args)
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

    let to_doc {pos = _; name; universals; params; body} ~exprs_doc =
        let open PPrint in
        string "function" ^^ blank 1
        ^^ Option.fold ~some: (fun name -> Name.to_doc name ^^ blank 1)
            ~none: empty name
        ^^ surround_separate_map 4 0 empty
            langle (comma ^^ break 1) (rangle ^^ blank 1)
            Type.param_to_doc (Vector.to_list universals)
        ^^ surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            Type.to_doc (Vector.to_list params)
        ^^ blank 1 ^^ surround 4 1
            lbrace (exprs_doc ^^ semi ^^ hardline ^^ Transfer.to_doc body) rbrace

    let def_to_doc id cont ~exprs_doc =
        PPrint.(Id.to_doc id ^^ blank 1 ^^ equals ^^ blank 1 ^^ to_doc cont ~exprs_doc)
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
            separate_map (semi ^^ hardline) (fun (id, expr) -> Expr.def_to_doc id expr)
                (Cont.Id.Hashtbl.find_opt cont_exprs id |> Option.value ~default: []) in

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

