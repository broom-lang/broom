signature REGISTERIZER = sig
    structure Env : REGISTER_ENV
    structure Abi : ABI
        where type RegIsa.loc = Env.Location.t
        where type RegIsa.Program.Builder.builder = Env.Abi.RegIsa.Program.Builder.builder

    val stmtHints : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Label.t -> Env.Hints.t -> Abi.Isa.Stmt.t -> Env.Hints.t
    val transferHints : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Label.t -> Env.Hints.t -> Abi.Isa.Transfer.t -> Env.Hints.t

    val stmt : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Abi.RegIsa.Program.Builder.builder -> Label.t -> Env.t -> Env.Hints.t -> Abi.Isa.Stmt.t -> Env.t
    val transfer : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Abi.RegIsa.Program.Builder.builder -> Label.t -> Env.t -> Env.Hints.t -> Abi.Isa.Transfer.t -> Env.t
end

