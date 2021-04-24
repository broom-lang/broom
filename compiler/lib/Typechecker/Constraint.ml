module Tx = Transactional
module Type = FcType.Type
module Coercer = Fc.Term.Coercer

type simple =
    | Subtype of {span : Util.span; env : TypeEnv.t
        ; sub : Type.t; super : Type.t
        ; coerce : Coercer.t option Tx.Ref.t}
    | Unify of {span : Util.span; env : TypeEnv.t
        ; ltyp : Type.t; rtyp : Type.t
        ; coercion : Type.coercion Tx.Ref.t}

type queue = simple Tx.Queue.t

type t =
    | Implies of Type.level * (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t * queue
    | Simples of queue

let unify ctrs span env ltyp rtyp =
    let coercion = Tx.Ref.ref (Type.Refl rtyp) in
    Tx.Queue.push ctrs (Unify {span; env; ltyp; rtyp; coercion});
    coercion

let subtype ctrs span env sub super =
    let coerce = Tx.Ref.ref None in
    Tx.Queue.push ctrs (Subtype {span; env; sub; super; coerce});
    coerce

