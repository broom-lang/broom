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
        | Pair of {fst : t; snd : t}
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
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

    and 'typ coercion =
        | Refl of 'typ
        | Symm of 'typ coercion
        | Trans of 'typ coercion * 'typ coercion
        | Comp of 'typ coercion * 'typ coercion Vector1.t
        | Axiom of kind Vector.t * 'typ * 'typ
        | AUse of Name.t
        | ExistsCo of kind Vector1.t * 'typ coercion
        | Inst of 'typ coercion * 'typ Vector1.t
        | PiCo of {universals : kind Vector.t
            ; domain : 'typ coercion; codomain : 'typ coercion}
        | PairCo of 'typ coercion * 'typ coercion
        | RecordCo of 'typ coercion
        | WithCo of {base : 'typ coercion; label : Name.t; field : 'typ coercion}
        | ProxyCo of 'typ coercion
        | Patchable of 'typ coercion Tx.Ref.t

    and typ = t

    and kind = t

    val kind_to_doc : kind -> PPrint.document
    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document
    val coercion_to_doc' : ('typ -> PPrint.document) -> 'typ coercion -> PPrint.document
    val coercion_to_doc : t coercion -> PPrint.document

    val close : int Name.Map.t -> t -> t
    val expose : t Vector.t -> t -> t

    val map_coercion_children : ('typ coercion -> 'typ coercion) -> 'typ coercion -> 'typ coercion

    val ov_eq : ov -> ov -> bool
end

