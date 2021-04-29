module Sigs = TyperSigs
module Env = TypeEnv
module MakeKinding = Kinding.Make
module MakeTyping = Typing.Make
module MakeConstraints = Constraints.Make
module Tx = Transactional
open Tx.Ref

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a Sigs.typing

module Error = TypeError

module rec Kinding : Sigs.KINDING = MakeKinding (Typing) (Constraints)
and Typing : Sigs.TYPING = MakeTyping (Kinding) (Constraints)
and Constraints : Sigs.CONSTRAINTS = MakeConstraints (Kinding)

let check_interactive_stmts ns stmt =
    let errors = ref [] in
    let ctrs = Tx.Queue.create () in

    let (typing, ns) = Typing.check_interactive_stmts ns errors ctrs stmt in
    Constraints.solve ctrs;

    match !errors with
    | [] ->
        let program = ApplyCoercions.apply_coercions typing.term in
        Ok ({typing with term = program}, ns)
    | errors -> Error (List.rev errors)

