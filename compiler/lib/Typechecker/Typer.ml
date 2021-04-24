module Sigs = TyperSigs
module Env = TypeEnv
module MakeKinding = Kinding.Make
module MakeTyping = Typing.Make

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a Sigs.typing

module Error = TypeError

module rec Kinding : Sigs.KINDING = MakeKinding(Typing)
and Typing : Sigs.TYPING = MakeTyping(Kinding)

let check_interactive_stmts env stmt =
    let open Transactional.Ref in
    let ctrs = Transactional.Queue.create () in
    let errors = ref [] in
    let env = Env.with_error_handler env (fun error -> errors := error :: !errors) in
    let res = Typing.check_interactive_stmts ctrs env stmt in
    match !errors with
    | [] -> Ok res
    | errors -> Error (List.rev errors)

