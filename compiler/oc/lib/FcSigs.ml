type 'a with_pos = 'a Util.with_pos

module type TYPE = sig
    type uv
    type subst

    type kind
        = ArrowK of kind Vector1.t * kind
        | TypeK

    type bv = {depth : int; sibli : int}

    (* The level of a type variable is the number of skolem-binding scopes in the
       typing environment at its creation site. Kind of like syntactic closures, but
       type inference is (scoping-wise) much simpler than hygienic macroexpansion so
       the required information can be compressed to this one small integer. *)
    type level = int

    type binding = Name.t * kind

    type ov = binding * level

    and abs = Exists of kind Vector.t * locator * t

    and t =
        | Pi of kind Vector.t * (locator * t) Vector.t * t * abs
        | Record of t field Vector.t
        | Type of abs
        | Fn of t
        | App of t * t Vector1.t
        | Bv of bv
        | Use of binding
        | Ov of ov
        | Uv of uv
        | Prim of Prim.t

    and locator =
        | PiL of locator
        | RecordL of locator field Vector.t
        | TypeL of t
        | Hole

    and 'a field = {label : string; typ : 'a}

    and coercion =
        | Refl of typ
        | Symm of coercion
        | Trans of coercion * coercion
        | Comp of coercion * coercion Vector1.t
        | Inst of coercion * typ Vector1.t
        | AUse of Name.t
        | TypeCo of coercion
        | Patchable of coercion ref

    and typ = t
    and template = locator

    val kind_to_doc : kind -> PPrint.document
    val binding_to_doc : binding -> PPrint.document
    val abs_to_doc : subst -> abs -> PPrint.document
    val universal_to_doc : kind Vector.t -> PPrint.document -> PPrint.document
    val to_doc : subst -> t -> PPrint.document
    val coercion_to_doc : subst -> coercion -> PPrint.document
    val locator_to_doc : subst -> locator -> PPrint.document

    val to_abs : t -> abs

    val freshen : binding -> binding
    val sibling : subst ref -> uv -> uv

    val expose_abs : subst ref -> t Vector.t -> abs -> abs
    val expose : subst ref -> t Vector.t -> t -> t
    val expose_locator : subst ref -> t Vector.t -> locator -> locator

    val close_abs : subst ref -> int Name.Map.t -> abs -> abs
    val close : subst ref -> int Name.Map.t -> t -> t
    val close_locator : subst ref -> int Name.Map.t -> locator -> locator
end

module type UV = sig
    type typ
    type level

    type subst
    
    type t

    type v =
        | Unassigned of Name.t * level
        | Assigned of typ

    val new_subst : unit -> subst
   
    val make : subst -> v -> subst * t
    val make_r : subst ref -> v -> t
    val get : subst -> t -> subst * v
    val getr : subst ref -> t -> v
    val set : subst -> t -> v -> subst
    val setr : subst ref -> t -> v -> unit
end

module type EXPR = sig
    module Type : TYPE

    type def
    type stmt

    type lvalue = {name : Name.t; typ : Type.t}

    type t
        = Fn of Type.binding Vector.t * lvalue Vector.t * t with_pos
        | App of t with_pos * Type.t Vector.t * t with_pos Vector.t
        | Let of def * t with_pos
        | Letrec of def Vector1.t * t with_pos
        | LetType of Type.binding Vector1.t * t with_pos
        | Match of t with_pos Vector.t * clause Vector.t
        | Axiom of (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t * t with_pos
        | Cast of t with_pos * Type.coercion
        | Pack of Type.t Vector1.t * t with_pos
        | Unpack of Type.binding Vector1.t * lvalue * t with_pos * t with_pos
        | Record of field Vector.t
        | Select of t with_pos * string
        | Proxy of Type.abs 
        | Use of Name.t
        | Const of Const.t
        | Patchable of t with_pos ref

    and clause = {pats : lvalue Vector.t; body : t with_pos}

    and field = {label : string; expr : t with_pos}

    val lvalue_to_doc : Type.subst -> lvalue -> PPrint.document
    val to_doc : Type.subst -> t with_pos -> PPrint.document

    (* TODO: Add more of these: *)
    val letrec : def Vector.t -> t with_pos -> t
end

module type STMT = sig
    module Type : TYPE

    type lvalue
    type expr

    type def = Util.span * lvalue * expr with_pos

    type t
        = Def of def
        | Expr of expr with_pos

    val def_to_doc : Type.subst -> def -> PPrint.document
    val to_doc : Type.subst -> t -> PPrint.document
end

module type TERM = sig
    module Type : TYPE

    module rec Expr : (EXPR
        with module Type = Type
        with type def = Stmt.def
        with type stmt = Stmt.t)

    and Stmt : (STMT
        with module Type = Type
        with type expr = Expr.t
        with type lvalue = Expr.lvalue)
end

