structure X64SeqIsa = SeqIsaFn(X64SysVAbi.RegIsa)

structure GasX64SysVAbiEmit :> sig
    val emit : TextIO.outstream -> {program : X64SeqIsa.Program.t, maxSlotCount : int, sourcemap : Pos.sourcemap} -> unit
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

    fun emit outstream {program = {globals, conts}, maxSlotCount, sourcemap} =
        let fun line s = TextIO.output (outstream, s ^ "\n")

            val fileIndices = String.HashTable.mkTable (0, Subscript)
            fun fileIndex filename =
                case String.HashTable.find fileIndices filename
                of SOME i => i
                 | NONE =>
                    let val i = String.HashTable.numItems fileIndices + 1
                    in String.HashTable.insert fileIndices (filename, i)
                     ; i
                    end

            fun emitFilename (pos : Pos.sourceloc option) (pos' : Pos.sourceloc) =
                let val changed =
                        case pos
                        of SOME pos => #fileName pos' <> #fileName pos
                         | NONE => true
                in  if changed
                    then line ( "\t.file " ^ Int.toString (fileIndex (getOpt (#fileName pos', "<stdin>")))
                              ^ " \"" ^ getOpt (#fileName pos', "<stdin>") ^ "\"" )
                    else ()
                end

            fun emitLoc (pos : Pos.sourceloc option) (pos' : Pos.sourceloc) =
                let val changed =
                        case pos
                        of SOME pos => pos' <> pos
                         | NONE => true
                in  if changed
                    then line ( "\t.loc " ^ Int.toString (fileIndex (getOpt (#fileName pos', "<stdin>"))) ^ " "
                              ^ Int.toString (#lineNo pos') ^ " " ^ Int.toString (#colNo pos') )
                    else ()
                 ;  SOME pos'
                end

            fun emitPos (pos : Pos.sourceloc option) (pos' : Pos.span) =
                let val pos' = Pos.sourceLoc sourcemap (#1 pos')
                in emitFilename pos pos'
                 ; emitLoc pos pos'
                end

            fun emitFieldLayout {offset = SOME offset, layout = SOME layout} =
                ( line ("\t.quad\t" ^ LargeWord.fmt StringCvt.DEC offset)
                ; line ("\t.quad\t" ^ convertGlobal layout) )

            fun emitGlobal (name, global) =
                let val name = convertGlobal name
                in if String.isPrefix "Broom_" name
                   then line ("\t.globl\t" ^ name)
                   else ()
                 ; case global
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
                       ; line ("\t.word\t" ^ Word.fmt StringCvt.DEC align)
                       ; line ("\t.byte\t" ^ (if inlineable then "1" else "0"))
                       ; line ("\t.byte\t" ^ (if isArray then "1" else "0"))
                       ; line "\t.zero\t4"
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

            fun emitStmt (stmt, pos) =
                let val (pos', target, expr) =
                        case stmt
                        of Stmt.Def (pos, target, _, expr) => (pos, SOME target, expr)
                         | Stmt.Eff (pos, expr) => (pos, NONE, expr)
                    val pos = emitPos pos pos'
                in emitExpr (target, expr)
                 ; pos
                end

            fun emitTransfer pos {pos = pos', oper} =
                let val pos = emitPos pos pos'
                in  case oper
                    of Transfer.JMP (dest, _) => line ("\tjmp\t" ^ convertLabel dest)
                     | Transfer.JMPi (dest, _) => line ("\tjmp\t*" ^ convertReg dest)
                     | Transfer.Jcc (Neq, _, dest') => line ("\tjne\t" ^ convertLabel dest')
                     | Transfer.Jcc (Overflow, _, dest') => line ("\tjo\t" ^ convertLabel dest')
                     | Transfer.RET _ => line "\tret\t"
                 ; pos
                end

            fun emitCont ((label, {pos = pos', name, cconv = _, params = _, stmts, transfer}), pos) =
                let val pos = emitPos pos pos'
                    do line (convertLabel label ^ ":")
                    val pos = Vector.foldl emitStmt pos stmts
                in emitTransfer pos transfer
                end
        in line "\t.text"
         ; line "\t.globl\tmain"
         ; line "\t.type\tmain, @function"
         ; line "main:"
         ; Vector.foldl emitCont NONE conts

         ; line "\t.data"
         ; Name.HashMap.appi emitGlobal globals
        end
end

