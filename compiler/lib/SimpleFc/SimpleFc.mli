module rec Expr : (SimpleFcSigs.EXPR
    with type decl = Stmt.decl
    with type stmt = Stmt.t)

and Stmt : SimpleFcSigs.STMT
    with type expr = Expr.t

module Program : sig
    type kind = SyntacticType.kind

    type t =
        { type_fns : (Name.t * kind) Vector.t
        ; decls : Stmt.decl Vector.t
        ; main : Expr.t }

    val to_doc : t -> PPrint.document
end

