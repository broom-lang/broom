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
        | PromotedValues of t Vector.t
        | Values of t Vector.t
        | Pi of {universals : kind Vector.t; domain : (t, edomain) Ior.t; codomain : t}
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

    and edomain = {edomain : t; eff : t}

    and template =
        | PiL of template
        | WithL of {base : template; label : Name.t; field : template}
        | ProxyL of t
        | Hole

    and 'a field = {label : string; typ : 'a}

    and coercion =
        | Refl of typ
        | Symm of coercion
        | Trans of coercion * coercion
        | Comp of coercion * coercion Vector1.t
        | Inst of coercion * typ Vector1.t
        | AUse of Name.t
        | PromotedArrayCo of coercion Vector.t
        | PromotedValuesCo of coercion Vector.t
        | ValuesCo of coercion Vector.t
        | RecordCo of coercion
        | WithCo of {base : coercion; label : Name.t; field : coercion}
        | ProxyCo of coercion
        | Patchable of coercion TxRef.rref

    and typ = t

    and kind = t

    val kind_to_doc : subst -> kind -> PPrint.document
    val binding_to_doc : subst -> binding -> PPrint.document
    val universal_to_doc : subst -> kind Vector.t -> PPrint.document -> PPrint.document
    val to_doc : subst -> t -> PPrint.document
    val coercion_to_doc : subst -> coercion -> PPrint.document
    val template_to_doc : subst -> template -> PPrint.document

    val freshen : binding -> binding
    val sibling : subst -> kind -> uv -> uv
end

module type UV = sig
    type kind
    type typ
    type level

    type subst = TxRef.log
    
    type t

    type v =
        | Unassigned of Name.t * kind * level
        | Assigned of typ

    val new_subst : unit -> subst
   
    val make : subst -> v -> t
    val get : subst -> t -> v
    val set : subst -> t -> v -> unit
end

