module Tx = Transactional
module Type = FcType.Type

type simple =
    | Subtype of {span : Util.span; env : TypeEnv.t
        ; sub : Type.t; super : Type.t
        ; coerce : Coercer.t option Tx.Ref.t}
    | Unify of {span : Util.span; env : TypeEnv.t
        ; ltyp : Type.t; rtyp : Type.t
        ; coercion : Type.coercion Tx.Ref.t}

type t =
    | Implies of Type.level * (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t
        * simple Tx.Queue.t
    | Simples of simple Tx.Queue.t

