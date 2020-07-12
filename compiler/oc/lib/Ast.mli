type 'a with_pos = 'a Util.with_pos

module rec Term : (AstSigs.TERM with type typ = Type.t and type pat = Pattern.t)

and Pattern : (AstSigs.PATTERN with type typ = Type.t)

and Type : (AstSigs.TYPE with type expr = Term.expr and type pat = Pattern.t and type eff = Effect.t)

and Effect : sig
    type t = Pure | Impure

    val to_doc : t -> PPrint.document
    val arrow : t -> PPrint.document
end

