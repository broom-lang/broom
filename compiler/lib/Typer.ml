module TypeError = TypeError

module Env = Env

module rec E : TyperSigs.KINDING = Kinding.Make(T)(M)
and T : TyperSigs.TYPING = Typing.Make(E)(M)
and M : TyperSigs.MATCHING = Matching.Make(E)

type 'a typing = 'a TyperSigs.typing

let check_stmt = T.check_stmt

