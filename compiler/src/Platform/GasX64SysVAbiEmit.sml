structure X64SeqIsa = SeqIsaFn(X64SysVAbi.RegIsa)

structure GasX64SysVAbiEmit :> sig
    val emit : TextIO.outstream -> {program : X64SeqIsa.Program.t, maxSlotCount : int} -> unit
end = struct
    structure Register = X64Register
    structure Global = X64SeqIsa.RegIsa.Global
    structure Oper = X64RegInstructions.Oper
    structure Stmt = X64SeqIsa.RegIsa.Stmt
    structure Transfer = X64RegInstructions.Transfer

    datatype cond = datatype X64JumpCondition.t

    fun convertLabel label = ".L" ^ Label.toString label

    val convertGlobal = Name.toString

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

    fun emit outstream {program = {globals, conts}, maxSlotCount} =
        let fun line s = TextIO.output (outstream, s ^ "\n")

            fun emitFieldLayout {offset = SOME offset, layout = SOME layout} =
                ( line ("\t.quad\t" ^ LargeWord.fmt StringCvt.DEC offset)
                ; line ("\t.quad\t" ^ convertGlobal layout) )

            fun emitGlobal (name, global) =
                let val name = convertGlobal name
                in case global
                   of Global.UInt n =>
                       ( line "\t.align 8"
                       ; line ("\t.type\t" ^ name ^ ", @object")
                       ; line (name ^ ":")
                       ; line ("\t.quad\t" ^ LargeWord.fmt StringCvt.DEC n) )
                    | Global.Layout {size = SOME size, align = SOME align, inlineable, isArray, fields} =>
                       ( line "\t.align 8"
                       ; line ("\t.type\t" ^ name ^ ", @object")
                       ; line (name ^ ":")
                       ; line ("\t.quad\t" ^ LargeWord.fmt StringCvt.DEC size)
                       ; line ("\t.quad\t" ^ Word.fmt StringCvt.DEC align)
                       ; line ("\t.byte\t" ^ (if inlineable then "1" else "0"))
                       ; line ("\t.byte\t" ^ (if isArray then "1" else "0"))
                       ; line "\t.zero\t6"
                       ; line ("\t.quad\t" ^ Int.toString (Vector.length fields))
                       ; Vector.app emitFieldLayout fields )
                    | Global.SlotMap slots =>
                       ( line ("\t.type\t" ^ name ^ ", @object")
                       ; line (name ^ ":")
                       ; let val bytes = TwobitMap.bytes slots
                             val pad = maxSlotCount - Word8Vector.length bytes * 4
                             val bytes = if pad > 0
                                         then Word8Vector.concat [ bytes
                                                                 , Word8Vector.tabulate (pad, Fn.constantly 0w0) ]
                                         else bytes
                         in Word8Vector.app (fn b => line ("\t.byte\t" ^ Word8.fmt StringCvt.DEC b)) bytes
                         end )
                end

            val emitExpr =
                fn (SOME target, Oper.MOV src) =>
                    line ("\tmovq\t" ^ convertReg src ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOAD src) =>
                    line ("\tmovq\t" ^ convertMem src ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOADc n) => (* FIXME?: Word printing, ugh: *)
                    line ("\tmovq\t$" ^ Int.toString (Word32.toInt n) ^ ", " ^ convertReg target)
                 | (SOME target, Oper.LOADl label) =>
                    line ("\tleaq\t" ^ convertLabel label ^ "(%rip), " ^ convertReg target)
                 | (SOME target, Oper.LOADg name) =>
                    line ("\tleaq\t" ^ convertGlobal name ^ "(%rip), " ^ convertReg target)
                 | (SOME target, Oper.LOADgv name) =>
                    line ("\tmovq\t" ^ convertGlobal name ^ "(%rip), " ^ convertReg target)
                 | (NONE, Oper.STORE (dest, src)) =>
                    line ("\tmovq\t" ^ convertReg src ^ ", " ^ convertMem dest)
                 | (NONE, Oper.PUSH src) => line ("\tpushq\t" ^ convertReg src)
                 | (NONE, Oper.CMP (v, c)) =>
                    line ("\tcmp\t$" ^ Int.toString (Word32.toInt c) ^ ", " ^ convertReg v)
                 | (NONE, Oper.LEAVE) => line "\tleave"
                 | (SOME _, Oper.ADD (a, b)) =>
                    line ("\taddq\t" ^ convertReg b ^ ", " ^ convertReg a)
                 | (SOME _, Oper.SUB (a, b)) =>
                    line ("\tsubq\t" ^ convertReg b ^ ", " ^ convertReg a)
                 | (SOME target, Oper.SUBc (_, n)) =>
                    line ("\tsubq\t$" ^ LargeWord.fmt StringCvt.DEC n ^ ", " ^ convertReg target)
                 | (SOME _, Oper.IMUL (a, b)) =>
                    line ("\timulq\t" ^ convertReg b ^ ", " ^ convertReg a)
                 | (SOME _, Oper.CALL (sym, _)) => line ("\tcall\t" ^ sym)
                 | (SOME _, Oper.CALLd (sym, _)) =>
                    line ("\tcall\t" ^ sym ^ "@PLT")

            val emitStmt =
                fn Stmt.Def (target, _, expr) => emitExpr (SOME target, expr)
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
         ; Vector.app emitCont conts

         ; line "\t.data"
         ; Name.HashMap.appi emitGlobal globals
        end
end

