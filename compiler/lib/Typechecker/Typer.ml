module TypeError = TypeError

module MakeEnv = Env.Make

type env = Env.env

module rec Env : TyperSigs.ENV with type t = env = MakeEnv(T)(E)(M)
and E : TyperSigs.KINDING with type env = Env.t = Kinding.Make(Env)(T)(M)
and T : TyperSigs.TYPING with type env = Env.t = Typing.Make(Env)(E)(M)
and M : TyperSigs.MATCHING with type env = Env.t = Matching.Make(Env)(E)

type 'a typing = 'a TyperSigs.typing

let check_program env defs main =
    try
        let (defs, env') = T.check_defs env defs in
        let {TyperSigs.term = main; eff = _} = T.check env' (Fc.Type.Tuple Vector.empty) main in
        Ok {Fc.Program.type_fns = Env.type_fns env; defs; main}
    with TypeError.TypeError (pos, err) -> Error (pos, err)

let check_interactive_stmts env stmt =
    try Ok (T.check_interactive_stmts env stmt)
    with TypeError.TypeError (pos, err) -> Error (pos, err)

