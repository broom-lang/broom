module TypeError = TypeError

module MakeEnv = Env.Make

module rec Env : TyperSigs.ENV = MakeEnv(T)
and E : TyperSigs.KINDING with type env = Env.t = Kinding.Make(Env)(T)(M)
and T : TyperSigs.TYPING with type env = Env.t  = Typing.Make(Env)(E)(M)
and M : TyperSigs.MATCHING with type env = Env.t  = Matching.Make(Env)(E)

type 'a typing = 'a TyperSigs.typing

let check_stmt = T.check_stmt

