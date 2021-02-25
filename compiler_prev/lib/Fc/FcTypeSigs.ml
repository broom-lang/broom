module type TYPE = sig
    type uv
    type subst

    (* The level of a type variable is the number of skolem-binding scopes in the
       typing environment at its creation site. Kind of like syntactic closures, but
       type inference is (scoping-wise) much simpler than hygienic macroexpansion so
       the required information can be compressed to this one small integer. *)
    type level = int

    type bv = {depth : int; sibli : int; kind : kind}

    and binding = Name.t * kind

    and ov = binding * level

    and t =
        | Exists of kind Vector1.t * t
        | PromotedArray of t Vector.t
        | PromotedTuple of t Vector.t
        | Tuple of t Vector.t
        | Pi of {universals : kind Vector.t; domain : t; eff : t; codomain : t}
        | Impli of {universals : kind Vector.t; domain : t; codomain : t}
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of t
        | Fn of kind * t
        | App of t * t
        | Bv of bv
        | Ov of ov
        | Uv of uv
        | Prim of Prim.t

    and template = TupleL of int

    and 'a field = {label : string; typ : 'a}

    and 'typ coercion =
        | ExistsCo of kind Vector1.t * 'typ coercion
        | Refl of 'typ
        | Symm of 'typ coercion
        | Trans of 'typ coercion * 'typ coercion
        | Comp of 'typ coercion * 'typ coercion Vector1.t
        | Inst of 'typ coercion * 'typ Vector1.t
        | AUse of Name.t
        | Axiom of kind Vector.t * 'typ * 'typ
        | PiCo of {universals : kind Vector.t
            ; domain : 'typ coercion; codomain : 'typ coercion}
        | PromotedArrayCo of 'typ coercion Vector.t
        | PromotedTupleCo of 'typ coercion Vector.t
        | TupleCo of 'typ coercion Vector.t
        | RecordCo of 'typ coercion
        | WithCo of {base : 'typ coercion; label : Name.t; field : 'typ coercion}
        | ProxyCo of 'typ coercion
        | Patchable of 'typ coercion TxRef.rref

    and typ = t

    and kind = t

    val kind_to_doc : subst -> kind -> PPrint.document
    val binding_to_doc : subst -> binding -> PPrint.document
    val bv_to_doc : bv -> PPrint.document
    val universal_to_doc : subst -> kind Vector.t -> PPrint.document -> PPrint.document
    val to_doc : subst -> t -> PPrint.document
    val coercion_to_doc' : (subst -> 'typ -> PPrint.document) -> subst -> 'typ coercion
        -> PPrint.document
    val coercion_to_doc : subst -> typ coercion -> PPrint.document
    val template_to_doc : subst -> template -> PPrint.document
end

module type UV = sig
    type kind
    type typ
    type level

    type subst = TxRef.log
    
    type t

    type v =
        | Unassigned of int * kind * level
        | Assigned of typ

    val new_subst : unit -> subst
   
    val make : subst -> kind -> level -> t
    val get : subst -> t -> v
    val set : subst -> t -> v -> unit
end

