open Asserts
module AType = Ast.Type

type 'a with_pos = 'a Util.with_pos

module Make (Typing : TyperSigs.TYPING) = struct
    let elaborate _ (typ : AType.t with_pos) = todo (Some typ.pos)
end

