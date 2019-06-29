structure FAstEval :> sig
    structure Value: sig
        datatype t = Int of int

        val toString: t -> string
    end

    type toplevel = Value.t NameHashTable.hash_table
    type runtime_error = unit

    val newToplevel: unit -> toplevel
    val interpret: toplevel -> FixedFAst.Term.stmt -> (runtime_error, Value.t) Either.t
end = struct
    structure FTerm = FixedFAst.Term
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt

    structure Value = struct
        datatype t = Int of int

        val toString =
            fn Int n => Int.toString n
    end

    type toplevel = Value.t NameHashTable.hash_table

    type runtime_error = unit

    datatype env = Toplevel of toplevel

    val constValue =
        fn Const.Int n => Value.Int n

    fun eval env cont =
        fn Const (_, c) => continue cont (constValue c)

    and exec env cont =
        fn Expr expr => eval env cont expr

    and continue cont value =
        case cont
        of [] => value

    fun newToplevel () = NameHashTable.mkTable (0, Subscript)

    fun interpret toplevel = Either.Right o exec (Toplevel toplevel) []
end

