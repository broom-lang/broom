signature INSERT_LOGUES = sig
    structure RegIsa : ISA

    val insert : {program : RegIsa.Program.t, maxSlotCount : int} -> RegIsa.Program.t
end

functor InsertLoguesFn (Args : sig
    structure RegIsa : ISA
    val prologue : Word32.word -> RegIsa.Stmt.t vector
    val epilogue : Word32.word -> RegIsa.Stmt.t vector
end) :> INSERT_LOGUES
    where type RegIsa.loc = Args.RegIsa.loc
    where type RegIsa.Stmt.t = Args.RegIsa.Stmt.t
    where type RegIsa.transfer = Args.RegIsa.Transfer.t
= struct
    structure RegIsa = Args.RegIsa
    structure Transfer = RegIsa.Transfer
    structure Instrs = RegIsa.Instrs

    fun insert {program = {globals, conts, main}, maxSlotCount} =
        let val frameSize = Word32.fromInt (maxSlotCount * Instrs.registerSize)
            val prologue = Args.prologue frameSize
            val epilogue = Args.epilogue frameSize

            fun insertContLogues {name, cconv, params, stmts, transfer} =
                let val stmts =
                        if Option.isSome cconv
                        then Vector.concat [prologue, stmts]
                        else stmts
                    val stmts =
                        if Transfer.isReturn transfer
                        then Vector.concat [stmts, epilogue]
                        else stmts
                in {name, cconv, params, stmts, transfer}
                end
        in {globals, conts = Label.HashMap.map insertContLogues conts, main}
        end
end

