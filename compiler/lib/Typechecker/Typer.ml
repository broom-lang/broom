module Sigs = TyperSigs
module MakeKinding = Kinding.Make
module MakeTyping = Typing.Make

module rec Kinding : Sigs.KINDING = MakeKinding(Typing)
and Typing : Sigs.TYPING = MakeTyping(Kinding)

