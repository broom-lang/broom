structure GasX64SysVAbiEmit :> sig
    val emit : TextIO.outstream -> X64SeqIsa.Program.t -> unit
end = struct
    structure Register = X64Register
    structure Oper = X64RegInstructions.Oper
    structure Stmt = X64SeqIsa.RegIsa.Stmt
    structure Transfer = X64RegInstructions.Transfer

    fun convertLabel label = ".L" ^ Label.toString label

    fun convertReg reg = "%" ^ Register.toString reg

    fun emit outstream =
        let fun line s = TextIO.output (outstream, s ^ "\n")

            val emitExpr =
                fn (SOME target, Oper.MOV src) =>
                    line ("\tmovq\t" ^ convertReg src ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOAD src) =>
                    line ("\tmovq\t(" ^ convertReg src ^ "), " ^ convertReg target)
                 | (SOME target, Oper.LOADc n) => (* FIXME?: Word printing, ugh: *)
                    line ("\tmovq\t$" ^ Int.toString (Word32.toInt n) ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOADl label) =>
                    line ("\tleaq\t" ^ convertLabel label ^ "(%rip), " ^ convertReg target)
                 | (NONE, Oper.STORE (dest, src)) =>
                    line ("\tmovq\t" ^ convertReg src ^ ", (" ^ convertReg dest ^ ")")
                 | (SOME _, Oper.CALLd (sym, _)) =>
                    line ("\tcall\t" ^ sym ^ "@PLT")

            val emitStmt =
                fn Stmt.Def (target, expr) => emitExpr (SOME target, expr)
                 | Stmt.Eff expr => emitExpr (NONE, expr)
                 | Stmt.Param _ => raise Fail "unreachable"

            val emitTransfer =
                fn Transfer.JMP (dest, _) => line ("\tjmp\t" ^ convertLabel dest)
                 | Transfer.JMPi (dest, _) => line ("\tjmp\t*" ^ convertReg dest)

            fun emitCont (label, {name, argc = _, stmts, transfer}) =
                ( line (convertLabel label ^ ":")
                ; Vector.app emitStmt stmts
                ; emitTransfer transfer )
        in line "\t.text"
         ; line "\t.globl\tmain"
         ; line "\t.type\tmain, @function"
         ; line "main:"
         ; Vector.app emitCont
        end
end

