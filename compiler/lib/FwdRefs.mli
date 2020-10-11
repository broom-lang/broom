module E = Fc.Term.Expr

module Make (IntHashtbl : Hashtbl.S with type key = int) (IntHashSet : CCHashSet.S with type elt = int) : sig
    type error = AccessUninitialized of Util.span * E.var * E.var

    val convert : Fc.Term.Stmt.t Vector.t -> (Fc.Term.Stmt.t Vector.t, error CCVector.ro_vector) Result.t
end

