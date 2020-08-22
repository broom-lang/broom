module Make (C : TyperSigs.TYPING) (M : TyperSigs.MATCHING) : TyperSigs.ELABORATION = struct

module AType = Ast.Type

type 'a with_pos = 'a Util.with_pos

let elaborate env (typ : AType.t with_pos) = match typ.v with
    | Record decls ->
        if Vector.length decls = 0
        then Fc.Type.to_abs (Record (Vector.empty ()))
        else failwith "TODO: nonempty signature"

let eval _ = failwith "TODO"

end

