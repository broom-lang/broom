type subst = TxRef.Subst.t
type 'a txref = 'a TxRef.t

module type TYPE = sig
    type quantifier = ForAll | Exists

    type t =
        | Uv of {quant : quantifier; name : Name.t; bound : bound txref}
        | Ov of {binder : scope; name : Name.t; kind : t}
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

    and bound = private
        | Bot of {binder : binder; kind : kind}
        | Flex of {level : int; bindees : bound TxRef.Set.t; binder : binder; typ : t}
        | Rigid of {level : int; bindees : bound TxRef.Set.t; binder : binder; typ : t}

    and binder =
        | Scope of scope
        | Type of bound txref

    and scope =
        | Local of {level : int; bindees : bound TxRef.Set.t txref; parent : scope}
        | Global of bound TxRef.Set.t txref

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

    val fresh : binder -> kind -> t
    val fix : binder -> (bound txref -> t) -> t

    val iter : (t -> unit) -> t -> unit
    val map_children : (t -> t) -> t -> t
    val postwalk_rebinding : (t -> t) -> t -> t

    val force : t -> t
    val forall_scope_ovs : binder: scope -> scope -> t -> t
    val instantiate : scope -> t -> t

    type typ = t

    module Bound : sig
        type t = bound

        val fresh : binder -> kind -> t txref

        val bindees : t -> bound TxRef.Set.t
        val binder : t -> binder
        val is_locked : t -> bool

        val rebind : t txref -> binder -> unit
        val graft_mono : t txref -> typ -> unit
        val set_level : t txref -> int -> unit

        module Hashtbl : CCHashtbl.S with type key = t txref
    end

    module Binder : sig
        type t = binder

        val level : t -> int
    end

    module Scope : sig
        type t = scope

        val level : t -> int
    end

    module Hashtbl : CCHashtbl.S with type key = t
end

