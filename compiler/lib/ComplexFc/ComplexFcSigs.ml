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
        | Local of {level : int; bindees : t Vector.t txref; ovs : ov Vector.t txref}
        | Global of {bindees : t Vector.t txref; ovs : ov Vector.t txref}

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
        val ovs : t -> ov Vector.t
        val fresh_ov : t -> kind -> ov
        val exit : t -> t -> unit
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

    val equal : t -> t -> bool
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

    val ov_tied : int -> t -> bool

    val force : t -> t
    val forall_scope_ovs : binder: scope -> scope -> t -> t
    val exists_scope_ovs : binder: scope -> scope -> t -> t
    val instantiate : scope -> t -> t

    type typ = t

    module Hashtbl : CCHashtbl.S with type key = t
end

module type TYPES = sig
    module rec Typ : (TYPE
        with type uv = Uv.t
        with type bound = Uv.bound
        with type binder = Uv.binder
        with type scope = Uv.scope
        with type ov = Ov.t)

    and Uv : (UV
        with type typ = Typ.t
        with type kind = Typ.kind
        with type ov = Ov.t)

    and Ov : OV
        with type kind = Typ.kind
        with type scope = Uv.scope
end

module type EXPR = sig
    type typ
    type coercion
    type t_scope
    type def
    type stmt

    and var = {name : Name.t; vtyp : typ}

    and typedef = Name.t * typ

    and t =
        { term : t'
        ; mutable parent : t option
        ; typ : typ
        ; pos : Util.span }

    and t' = private
        | Tuple of t array
        | Focus of {mutable focusee : t; index : int}

        | Fn of {t_scope : t_scope; param : var; mutable body : t}
        | App of {mutable callee : t; universals : typ Vector.t; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : typ Vector.t; mutable arg : t}
        | PrimBranch of {op : Branchop.t; universals : typ Vector.t; mutable arg : t
            ; clauses : prim_clause Vector.t}

        | Let of {defs : stmt Array1.t; mutable body : t}
        | Letrec of {defs : def Array1.t; mutable body : t}
        (*| LetType of {typedefs : typedef Vector1.t; mutable body : t}*)
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        (*| Axiom of { axioms : (Name.t * Type.kind Vector.t * typ * typ) Vector1.t
            ; mutable body : t }*)
        | Cast of {mutable castee : t; coercion : coercion}

        (*| Pack of {existentials : typ Vector1.t; mutable impl : t}
        | Unpack of { existentials : typedef Vector1.t; var : var; mutable value : t
            ; mutable body : t }*)

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}

        | Proxy of typ
        | Const of Const.t

        | Use of var

        | Patchable of t TxRef.t

    and clause = {pat : pat; mutable body : t}
    and prim_clause = {res : var option; prim_body : t}

    and pat = {pterm: pat'; ptyp : typ; ppos : Util.span}
    and pat' =
        | TupleP of pat Vector.t
        | ProxyP of typ
        | ConstP of Const.t
        | VarP of var
        | WildP of Name.t

    val var_to_doc : var -> PPrint.document
    val to_doc : t -> PPrint.document
    val pat_to_doc : pat -> PPrint.document

    val var : Name.t -> typ -> var
    val fresh_var : typ -> var

    val at : Util.span -> typ -> t' -> t

    val tuple : t Array.t -> t'
    val focus : t -> int -> t'
    val fn : t_scope -> var -> t -> t'
    val app : t -> typ Vector.t -> t -> t'
    val primapp : Primop.t -> typ Vector.t -> t -> t'
    val primbranch : Branchop.t -> typ Vector.t -> t -> prim_clause Vector.t -> t'
    val let' : stmt Array.t -> t -> t'
    val letrec : def Array.t -> t -> t'
    (*val axiom : (Name.t * Type.kind Vector.t * typ * typ) Vector.t -> t -> t'*)
    val match' : t -> clause Vector.t -> t'
    val cast : t -> coercion -> t'
    (*val pack : typ Vector.t -> t -> t'
    val unpack : typedef Vector1.t -> var -> t -> t -> t'*)
    val record : (Name.t * t) array -> t'
    val where : t -> (Name.t * t) array -> t'
    val select : t -> Name.t -> t'
    val proxy : typ -> t'
    val const : Const.t -> t'
    val use : var -> t'
    val patchable : t TxRef.t -> t'

    val map_children : (t -> t) -> t -> t

    module Var : Set.OrderedType with type t = var
    module VarSet : Set.S with type elt = var
end

module type STMT = sig
    type expr
    type var

    type def = Util.span * var * expr

    type t
        = Def of def
        | Expr of expr

    val def_to_doc : def -> PPrint.document
    val to_doc : t -> PPrint.document

    val rhs : t -> expr
end

module type TERM = sig
    module rec Expr : (EXPR
        with type def = Stmt.def
        with type stmt = Stmt.t)

    and Stmt : (STMT
        with type expr = Expr.t
        with type var = Expr.var)
end

module type PROGRAM = sig
    module Type : TYPE
    module Term : TERM

    type t =
        { type_fns : Term.Expr.typedef Vector.t
        ; defs : Term.Stmt.def Vector.t
        ; main : Term.Expr.t }

    val to_doc : t -> PPrint.document
end

