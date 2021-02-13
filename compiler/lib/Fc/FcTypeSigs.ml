type subst = TxRef.Subst.t
type 'a txref = 'a TxRef.t

module type UV = sig
    type typ
    type kind
    type ov

    type t =
        { name : Name.t
        ; quant : quantifier
        ; binder : binder txref
        ; bindees : t Vector.t txref
        ; level : int txref
        ; bound : bound txref }

    and quantifier = ForAll | Exists

    and bound =
        | Bot of kind
        | Flex of typ
        | Rigid of typ

    and binder =
        | Scope of scope
        | Type of t

    and scope =
        | Local of {level : int; parent : scope
            ; bindees : t Vector.t txref; ovs : ov Vector.t txref}
        | Global of t Vector.t txref

    and uv = t

    val hash : t -> int
    val equal : t -> t -> bool

    module Binder : sig
        type t = binder

        val level : t -> int
    end

    module Scope : sig
        type t = scope

        val level : t -> int
    end

    val fresh : quantifier -> binder -> kind -> t
    val is_locked : t -> bool
    val rebind : t -> binder -> unit
    val graft_mono : t -> typ -> unit
    val map_bound : (typ -> typ) -> t -> t

    module Hashtbl : CCHashtbl.S with type key = t
    module HashSet : CCHashSet.S with type elt = t
end

module type OV = sig
    type kind
    type scope

    type t = {name : Name.t; binder : scope; kind : kind}
end

module type TYPE = sig
    type uv
    type bound
    type binder
    type scope
    type ov

    type t =
        | Uv of uv
        | Ov of ov
        | Pi of {domain : t; eff : t; codomain : t} (* -! -> *)
        | Impli of {domain : t; codomain : t} (* => *)
        | Fn of {param : kind; body : t} (* type lambda *)
        | App of t * t
        | Record of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of t
        | Tuple of t Vector.t
        | PromotedTuple of t Vector.t
        | PromotedArray of t Vector.t
        | Prim of Prim.t

    and kind = t

    and coercion = Refl of t

(*
    and template = TupleL of int

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
*)

    val kind_to_doc : kind -> PPrint.document
    (*val universal_to_doc : kind Vector.t -> PPrint.document -> PPrint.document*)
    val to_doc : t -> PPrint.document
(*    val coercion_to_doc' : ('typ -> PPrint.document) -> 'typ coercion -> PPrint.document*)
    val coercion_to_doc : coercion -> PPrint.document
    (*val template_to_doc : template -> PPrint.document*)

    val fix : binder -> (uv -> t) -> t

    val iter : (t -> unit) -> t -> unit
    val map_children : (t -> t) -> t -> t
    val postwalk_rebinding : (t -> t) -> t -> t

    val force : t -> t
    val forall_scope_ovs : binder: scope -> scope -> t -> t
    val instantiate : scope -> t -> t

    type typ = t

    module Hashtbl : CCHashtbl.S with type key = t
end

