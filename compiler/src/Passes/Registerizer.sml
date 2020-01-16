signature REGISTERIZER = sig
    structure Abi : ABI
    structure Env : REGISTER_ENV
        where type Abi.RegIsa.Program.Builder.builder = Abi.RegIsa.Program.Builder.builder

    val stmtHints : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Label.t -> Env.Hints.t -> Abi.Isa.Stmt.t -> Env.Hints.t
    val transferHints : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Label.t -> Env.Hints.t -> Abi.Isa.Transfer.t -> Env.Hints.t

    val stmt : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Abi.RegIsa.Program.Builder.builder -> Label.t -> Env.t -> Env.Hints.t -> Abi.Isa.Stmt.t -> Env.t
    val transfer : Abi.CallingConvention.internal Label.HashTable.hash_table
        -> Abi.RegIsa.Program.Builder.builder -> Label.t -> Env.t -> Env.Hints.t -> Abi.Isa.Transfer.t -> Env.t
end

