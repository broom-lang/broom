signature BINDINGS = sig
    type typ
    type value
end

functor Scope (Bindings: BINDINGS) :> sig
    type t

    val new: t option -> t

    val setVal: t -> Name.t -> Bindings.value -> unit
    val setType: t -> Name.t -> Bindings.typ -> unit
    val setModule: t -> Name.t -> t -> unit

    val findVal: t -> Name.t -> Bindings.value option
    val findType: t -> Name.t -> Bindings.typ option
    val findModule: t -> Name.t -> t option

    val dominates: t -> t -> bool
    val isAncestor: t -> t -> bool
end = struct
    type typ = Bindings.typ
    type value = Bindings.value

    (* TODO: Add an expression variant that doesn't have .types or .modules. *)
    datatype t = Scope of { parent: t option
                          , values: value NameHashTable.hash_table
                          , types: typ NameHashTable.hash_table
                          , modules: t NameHashTable.hash_table }

    fun new parent = Scope { parent
                           , values = NameHashTable.mkTable (0, Subscript)
                           , types = NameHashTable.mkTable (0, Subscript)
                           , modules = NameHashTable.mkTable (0, Subscript) }

    fun setVal scope name vb = raise Fail "unimplemented"
    fun setType scope name vb = raise Fail "unimplemented"
    fun setModule scope name vb = raise Fail "unimplemented"

    fun findVal (Scope {values, ...}) name = NameHashTable.find values name
    fun findType (Scope {types, ...}) name = NameHashTable.find types name
    fun findModule (Scope {modules, ...}) name = NameHashTable.find modules name

    fun dominates dom scope = MLton.eq (dom, scope) orelse isAncestor dom scope

    and isAncestor elder =
        fn Scope {parent = SOME parent, ...} => dominates elder parent
         | Scope {parent = NONE, ...} => false
end

