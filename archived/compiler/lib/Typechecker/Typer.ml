module Sigs = TyperSigs
module T = Fc.Type
module MakeConstraints = Constraints.Make
module MakeKinding = Kinding.Make
module MakeTyping = Typing.Make
module Tx = Transactional
open Tx.Ref

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a Sigs.typing

module Error = TypeError

module rec Constraints : Sigs.CONSTRAINTS = MakeConstraints (Kinding)
and Kinding : Sigs.KINDING = MakeKinding (Constraints) (Typing)
and Typing : Sigs.TYPING = MakeTyping (Constraints) (Kinding)

let check_program program =
    let errors = ref [] in
    let ctrs = Tx.Queue.create () in

    let typing = Typing.check_program errors ctrs program in
    Constraints.solve ctrs;

    match !errors with
    | [] ->
        let program = ApplyCoercions.apply_coercions typing.term in
        Ok {typing with term = program}
    | errors -> Error (List.rev errors)

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

