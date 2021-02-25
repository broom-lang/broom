module Type = FcType.Type
module Uv = FcType.Uv

module Term = FcTerm.Make(Type)

module Program = struct
    module Type = Type
    module Term = Term

    type t =
        { type_fns : Type.binding Vector.t
        ; defs : Term.Stmt.def Vector.t
        ; main : Term.Expr.t }

    let type_fn_to_doc s (name, kind) =
        let open PPrint in
        infix 4 1 equals (string "type" ^^ blank 1 ^^ Name.to_doc name)
            (Type.to_doc s kind)

    let to_doc s {type_fns; defs; main} =
        let open PPrint in
        separate_map (twice hardline) (type_fn_to_doc s) (Vector.to_list type_fns)
        ^/^ separate_map (twice hardline) (fun def -> Term.Stmt.def_to_doc s def ^^ semi)
            (Vector.to_list defs)
        ^^ twice (twice hardline) ^^ Term.Expr.to_doc s main
end

