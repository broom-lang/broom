(* TODO: Change name since also inserts Broom_frameLength *)

signature INSERT_LOGUES = sig
    structure RegIsa : ISA

    val insert : {program : RegIsa.Program.t, maxSlotCount : int} -> RegIsa.Program.t
end

functor InsertLoguesFn (Args : sig
    structure RegIsa : ISA
    val prologue : Pos.span -> LargeWord.word -> RegIsa.Stmt.t vector
    val epilogue : Pos.span -> LargeWord.word -> RegIsa.Stmt.t vector
end) :> INSERT_LOGUES
    where type RegIsa.loc = Args.RegIsa.loc
    where type RegIsa.Stmt.t = Args.RegIsa.Stmt.t
    where type RegIsa.transfer = Args.RegIsa.Transfer.oper
= struct
    structure RegIsa = Args.RegIsa
    structure Global = RegIsa.Global
    structure Transfer = RegIsa.Transfer
    structure Instrs = RegIsa.Instrs

    val frameSizeName = Name.fromString "Broom_frameLength" (* TODO: DRY *)

    fun insert {program = {globals, conts, main}, maxSlotCount} =
        let val frameSize = LargeWord.fromInt (maxSlotCount * Instrs.registerSize)
            fun prologue pos = Args.prologue pos frameSize
            fun epilogue pos = Args.epilogue pos frameSize

            fun insertContLogues {pos, name, cconv, params, stmts, transfer} =
                let val stmts =
                        if Option.isSome cconv
                        then Vector.concat [prologue pos , stmts]
                        else stmts
                    val stmts =
                        if Transfer.isReturn transfer
                        then Vector.concat [stmts, epilogue pos]
                        else stmts
                in {pos, name, cconv, params, stmts, transfer}
                end
        in { globals = Name.HashMap.insert globals (frameSizeName, Global.UInt (LargeWord.fromInt maxSlotCount))
           , conts = Label.HashMap.map insertContLogues conts, main }
        end
end

