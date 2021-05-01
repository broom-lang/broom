module Tx = Transactional
module T = Fc.Type
module Env = TypeEnv
module Coercer = Fc.Term.Coercer

type simple =
    | Subtype of {span : Util.span; env : Env.t
        ; sub : T.t; super : T.t
        ; coerce : Coercer.t Tx.Ref.t}
    | Unify of {span : Util.span; env : Env.t
        ; ltyp : T.t; rtyp : T.t
        ; coercion : T.t T.coercion Tx.Ref.t}

type queue = simple Tx.Queue.t

type t =
    | Implies of T.level * (Name.t * T.kind Vector.t * T.t * T.t) Vector1.t * queue
    | Simples of queue

