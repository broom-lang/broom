module Sigs = TyperSigs
module Env = TypeEnv
module MakeKinding = Kinding.Make
module MakeTyping = Typing.Make
module MakeConstraints = Constraints.Make

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a Sigs.typing

module Error = TypeError

module rec Kinding : Sigs.KINDING = MakeKinding (Typing) (Constraints)
and Typing : Sigs.TYPING = MakeTyping (Kinding) (Constraints)
and Constraints : Sigs.CONSTRAINTS = MakeConstraints (Kinding)

let check_interactive_stmts env stmt =
    let open Transactional.Ref in
    let ctrs = Transactional.Queue.create () in
    let errors = ref [] in
    let env = Env.with_error_handler env (fun error -> errors := error :: !errors) in

    let (typing, env) = Typing.check_interactive_stmts ctrs env stmt in
    Constraints.solve ctrs;

    match !errors with
    | [] ->
        let program = ApplyCoercions.apply_coercions typing.term in
        Ok ({typing with term = program}, env)
    | errors -> Error (List.rev errors)

