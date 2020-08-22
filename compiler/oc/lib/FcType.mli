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

module Uv : UnionFind.STORE

type uvv =
    | Unassigned of Name.t * level
    | Assigned of typ

and uv = uvv Uv.rref

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
val abs_to_doc : uvv Uv.store -> abs -> PPrint.document
val universal_to_doc : kind Vector.t -> PPrint.document -> PPrint.document
val to_doc : uvv Uv.store -> t -> PPrint.document
val coercion_to_doc : uvv Uv.store -> coercion -> PPrint.document
val locator_to_doc : uvv Uv.store -> locator -> PPrint.document

val to_abs : t -> abs

val freshen : binding -> binding
val sibling : uvv Uv.store ref -> uv -> uv

val expose_abs : uvv Uv.store ref -> t Vector.t -> abs -> abs
val expose : uvv Uv.store ref -> t Vector.t -> t -> t
val expose_locator : uvv Uv.store ref -> t Vector.t -> locator -> locator

val close_abs : uvv Uv.store ref -> int Name.Map.t -> abs -> abs
val close : uvv Uv.store ref -> int Name.Map.t -> t -> t
val close_locator : uvv Uv.store ref -> int Name.Map.t -> locator -> locator

