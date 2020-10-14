module E = Fc.Term.Expr

module Make (IntHashtbl : Hashtbl.S with type key = int) : sig
    type error = AccessUninitialized of Util.span * E.var * E.var

    val error_to_doc : error -> PPrint.document

    val convert : Fc.Program.t -> (Fc.Program.t, error CCVector.ro_vector) Result.t
end

