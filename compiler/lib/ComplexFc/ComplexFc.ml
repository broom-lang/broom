module rec Types : ComplexFcSigs.TYPES = GraphType.Make (Term)

and Term : ComplexFcSigs.TERM
    with type Expr.typ = Types.Typ.t
    with type Expr.coercion = Types.Typ.coercion
    with type Expr.t_scope = Types.Uv.Scope.t
= ComplexFcTerm.Make (Types)

(* HACK: These constants are 'unsafe' for OCaml recursive modules,
 * so we have to add them here: *)
module Type = struct
    include Types.Typ

    (* __typeIn [__boxed] *)
    let aType = App (Prim TypeIn, PromotedArray (Vector.singleton (Prim Boxed)))
    let aKind = aType

    (* __rowOf (__typeIn [__boxed]) *)
    let aRow = App (Prim RowOf, aType)

    (* __array __singleRep *)
    let rep = App (Prim Array, Prim SingleRep)
end

module Program = struct
    module Type = Type
    module Term = Term

    type t =
        { type_fns : Term.Expr.typedef Vector.t
        ; defs : Term.Stmt.def Vector.t
        ; main : Term.Expr.t }

    let type_fn_to_doc (name, kind) =
        let open PPrint in
        infix 4 1 equals (string "type" ^^ blank 1 ^^ Name.to_doc name)
            (Type.to_doc kind)

    let to_doc {type_fns; defs; main} =
        let open PPrint in
        separate_map (twice hardline) type_fn_to_doc (Vector.to_list type_fns)
        ^/^ separate_map (twice hardline) (fun def -> Term.Stmt.def_to_doc def ^^ semi)
            (Vector.to_list defs)
        ^^ twice (twice hardline) ^^ Term.Expr.to_doc main
end

