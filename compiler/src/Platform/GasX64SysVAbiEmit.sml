structure X64SeqIsa = SeqIsaFn(X64SysVAbi.RegIsa)

structure GasX64SysVAbiEmit :> sig
    val emit : TextIO.outstream -> X64SeqIsa.Program.t -> unit
end = struct
    structure Register = X64Register
    structure Oper = X64RegInstructions.Oper
    structure Stmt = X64SeqIsa.RegIsa.Stmt
    structure Transfer = X64RegInstructions.Transfer

    datatype cond = datatype X64JumpCondition.t

    fun convertLabel label = ".L" ^ Label.toString label

    fun convertReg reg = "%" ^ Register.toString reg

    fun convertMem {base, index, disp} =
        (if disp = 0
         then ""
         else Int.toString disp)
        ^ (case (base, index)
           of (SOME base, SOME (scale, index)) =>
               "(" ^ convertReg base ^ ", " ^ convertReg index ^ ", " ^ Word.toString scale ^ ")"
            | (SOME base, NONE) => "(" ^ convertReg base ^ ")"
            | (NONE, SOME (0w1, index)) => "(" ^ convertReg index ^ ")"
            | (NONE, SOME (scale, index)) =>
               "(" ^ convertReg index ^ ", " ^ Word.toString scale ^ ")"
            | (NONE, NONE) => "")

    fun emit outstream =
        let fun line s = TextIO.output (outstream, s ^ "\n")

            val emitExpr =
                fn (SOME target, Oper.MOV src) =>
                    line ("\tmovq\t" ^ convertReg src ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOAD src) =>
                    line ("\tmovq\t" ^ convertMem src ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOADc n) => (* FIXME?: Word printing, ugh: *)
                    line ("\tmovq\t$" ^ Int.toString (Word32.toInt n) ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOADl label) =>
                    line ("\tleaq\t" ^ convertLabel label ^ "(%rip), " ^ convertReg target)
                 | (NONE, Oper.STORE (dest, src)) =>
                    line ("\tmovq\t" ^ convertReg src ^ ", " ^ convertMem dest)
                 | (NONE, Oper.PUSH src) => line ("\tpushq\t" ^ convertReg src)
                 | (NONE, Oper.CMP (v, c)) =>
                    line ("\tcmp\t$" ^ Int.toString (Word32.toInt c) ^ ", " ^ convertReg v)
                 | (NONE, Oper.LEAVE) => line "\tleave"
                 | (SOME _, Oper.ADD (a, b)) =>
                    line ("\taddq\t" ^ convertReg b ^ ", " ^ convertReg a)
                 | (SOME target, Oper.SUBc (_, n)) =>
                    line ("\tsubq\t$" ^ Int.toString (Word32.toInt n) ^ ", " ^ convertReg target)
                 | (SOME _, Oper.CALLd (sym, _)) =>
                    line ("\tcall\t" ^ sym ^ "@PLT")

            val emitStmt =
                fn Stmt.Def (target, expr) => emitExpr (SOME target, expr)
                 | Stmt.Eff expr => emitExpr (NONE, expr)

            val emitTransfer =
                fn Transfer.JMP (dest, _) => line ("\tjmp\t" ^ convertLabel dest)
                 | Transfer.JMPi (dest, _) => line ("\tjmp\t*" ^ convertReg dest)
                 | Transfer.Jcc (Neq, _, dest') => line ("\tjne\t" ^ convertLabel dest')
                 | Transfer.Jcc (Overflow, _, dest') => line ("\tjo\t" ^ convertLabel dest')
                 | Transfer.RET _ => line "\tret\t"

            fun emitCont (label, {name, cconv = _, params = _, stmts, transfer}) =
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

