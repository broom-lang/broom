functor X64InstructionsFn (Register : REGISTER) :> sig
    type def = Register.t

    type mem = def

    structure Oper : sig
        datatype t
            = LOAD of mem          (* MOV r64 m64 *)
            | LOADc of Word32.word (* MOV r64 imm64 *)
            | LOADl of Label.t     (* LEA the label *)
            | STORE of mem * def   (* MOV m64 r64 *)
            | ADD of def * def
            | SUB of def * def
            | IMUL of def * def
            | IDIV of def * def
            | CALL of Label.t * def vector (* relative/absolute (foreign) CALL *)
            | CALLd of string * def vector (* dynamically linked (foreign) CALL *)
            | CALLi of def * def vector    (* indirect (foreign) CALL *)

        val toDoc : t -> PPrint.t
    end

    structure Transfer : sig
        datatype pred = Eq

        datatype t
            = JMP of Label.t * def vector (* relative/absolute JMP *)
            | JMPi of def * def vector    (* indirect JMP through register *)
            | Jcc of pred * Label.t * Label.t

        val toDoc : t -> PPrint.t
    end
end = struct
    type def = Register.t

    val text = PPrint.text
    val space = PPrint.space
    val comma = PPrint.comma
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val parens = PPrint.parens
    val punctuate = PPrint.punctuate

    type mem = def

    structure Oper = struct
        datatype t
            = LOAD of mem          (* MOV r64 m64 *)
            | LOADc of Word32.word (* MOV r64 imm64 *)
            | LOADl of Label.t     (* LEA the label *)
            | STORE of mem * def   (* MOV m64 r64 *)
            | ADD of def * def
            | SUB of def * def
            | IMUL of def * def
            | IDIV of def * def
            | CALL of Label.t * def vector (* relative/absolute (foreign) CALL *)
            | CALLd of string * def vector (* dynamically linked (foreign) CALL *)
            | CALLi of def * def vector    (* indirect (foreign) CALL *)

        val toDoc =
            fn LOAD mem => text "mov" <+> parens (Register.toDoc mem)
             | LOADc n => text "mov" <+> text (Word32.toString n)
             | LOADl label => text "lea" <+> Label.toDoc label
             | STORE (target, src) =>
                text "mov" <+> parens (Register.toDoc target) <+> Register.toDoc src
             | CALLd (callee, args) =>
                text "call" <+> text (callee ^ "@PLT")
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
    end

    structure Transfer = struct
        datatype pred = Eq

        datatype t
            = JMP of Label.t * def vector (* relative/absolute JMP *)
            | JMPi of def * def vector    (* indirect JMP through register *)
            | Jcc of pred * Label.t * Label.t

        val toDoc =
            fn JMP (label, args) =>
                text "jmp" <+> Label.toDoc label
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
             | JMPi (def, args) =>
                text "jmp" <+> Register.toDoc def
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
    end
end

structure X64Instructions = X64InstructionsFn(CpsId)

structure X64Isa = IsaFn(struct
    structure Register = CpsId
    structure Instrs = X64Instructions
end)

