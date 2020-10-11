module E = Fc.Term.Expr

module Make (IntHashtbl : Hashtbl.S with type key = int) : sig
    type error = AccessUninitialized of Util.span * E.var * E.var

    val error_to_doc : error -> PPrint.document

    val convert : Fc.Term.Stmt.t Vector.t -> (Fc.Term.Stmt.t Vector.t, error CCVector.ro_vector) Result.t
end

