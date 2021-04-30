module Tx = Transactional

module type TYPE = sig
    (* The level of a type variable is the number of skolem-binding scopes in the
       typing environment at its creation site. Kind of like syntactic closures, but
       type inference is (scoping-wise) much simpler than hygienic macroexpansion so
       the required information can be compressed to this one small integer. *)
    type level = int

    type t =
        | Uv of uv
        | Ov of ov
        | Bv of bv
        | Exists of {existentials : kind Vector1.t; body : t}
        | Pi of {universals : kind Vector.t; domain : t; eff : t; codomain : t}
        | Impli of {universals : kind Vector.t; domain : t; codomain : t}
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Tuple of t Vector.t
        | PromotedTuple of t Vector.t
        | PromotedArray of t Vector.t
        | Proxy of t
        | Fn of {param : kind; body : t}
        | App of {callee : t; arg : t}
        | Prim of Prim.t

    and uv = uvv Tx.Ref.t

    and uvv =
        | Unassigned of bool * Name.t * kind * level
        | Assigned of typ

    and ov = {name : Name.t; kind : kind; level : level}

    and bv = {depth : int; sibli : int; bkind : kind}

    and def = Name.t * kind

    and coercion =
        | Refl of t
        | Symm of coercion
        | Trans of coercion * coercion
        | Comp of coercion * coercion Vector1.t
        | Axiom of kind Vector.t * t * t
        | AUse of Name.t
        | ExistsCo of kind Vector1.t * coercion
        | Inst of coercion * t Vector1.t
        | PiCo of {universals : kind Vector.t
            ; domain : coercion; codomain : coercion}
        | RecordCo of coercion
        | WithCo of {base : coercion; label : Name.t; field : coercion}
        | TupleCo of coercion Vector.t
        | PromotedTupleCo of coercion Vector.t
        | PromotedArrayCo of coercion Vector.t
        | ProxyCo of coercion
        | Patchable of coercion Tx.Ref.t

    and typ = t

    and kind = t

    val kind_to_doc : kind -> PPrint.document
    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document
    val coercion_to_doc : coercion -> PPrint.document

    val map_coercion_children : (coercion -> coercion) -> coercion -> coercion
end

