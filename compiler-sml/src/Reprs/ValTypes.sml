structure ValTypes :> sig
    type 't env

    val new: unit -> 't env
    val find: 't env -> Name.t -> 't option
    val insert: 't env -> Name.t -> 't -> unit
    val remove: 't env -> Name.t -> unit
end = struct
    type 't env = 't NameHashTable.hash_table

    fun new () = NameHashTable.mkTable (0, Subscript)

    val find = NameHashTable.find

    fun insert env name t = NameHashTable.insert env (name, t)

    fun remove env name = (NameHashTable.remove env name; ())
end
