functor X64InstructionsFn (Register : REGISTER) :> sig
    type def = Register.t

    val registerSize : int

    type mem =
        { base : def option
        , index : (Word.word * def) option
        , disp : int }

    structure Oper : sig
        type def = def
        
        datatype t
            = MOV of def
            | LOAD of mem          (* MOV r64 m64 *)
            | LOADc of Word32.word (* MOV r64 imm64 *)
            | LOADl of Label.t     (* LEA the label *)
            | STORE of mem * def   (* MOV m64 r64 *)
            | ADD of def * def
            | SUB of def * def
            | IMUL of def * def
            | IDIV of def * def
            | CALL of string * def vector (* relative/absolute (foreign) CALL *)
            | CALLd of string * def vector (* dynamically linked (foreign) CALL *)
            | CALLi of def * def vector    (* indirect (foreign) CALL *)

        val move : def -> t
        val stackLoad : def -> int -> t
        val stackStore : def -> int -> def -> t

        val toDoc : t -> PPrint.t
        val foldDefs : (def * 'a -> 'a) -> 'a -> t -> 'a
        val appLabels : (Label.t -> unit) -> t -> unit
    end

    structure Transfer : sig
        type def = def

        datatype pred = Eq

        datatype t
            = JMP of Label.t * def vector (* relative/absolute JMP *)
            | JMPi of def * def vector    (* indirect JMP through register *)
            | Jcc of pred * Label.t * Label.t
            | RET of def vector

        val toDoc : t -> PPrint.t
        val isReturn : t -> bool
        val foldDefs : (def * 'a -> 'a) -> 'a -> t -> 'a
        val foldLabels : (Label.t * 'a -> 'a) -> 'a -> t -> 'a
        val appLabels : (Label.t -> unit) -> t -> unit
    end
end = struct
    type def = Register.t

    val op|> = Fn.|>
    val text = PPrint.text
    val space = PPrint.space
    val comma = PPrint.comma
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val parens = PPrint.parens
    val brackets = PPrint.brackets
    val punctuate = PPrint.punctuate

    val registerSize = 8

    type mem =
        { base : def option
        , index : (Word.word * def) option
        , disp : int }

    fun memToDoc {base, index, disp} =
        (case base (* case base :D not the same as base case ;) *)
         of SOME base =>
             (case index
              of SOME (scale, index) =>
                  Register.toDoc base <+> text "+"
                  <+> (if scale = 0w1
                       then PPrint.empty
                       else PPrint.word scale <> text "*")
                  <> Register.toDoc index
                  <> (if disp = 0
                      then PPrint.empty
                      else space <> text "+" <+> PPrint.int disp)
               | NONE => 
                  Register.toDoc base
                  <> (if disp = 0
                      then PPrint.empty
                      else space <> text "+" <+> PPrint.int disp))
          | NONE =>
             (case index
              of SOME (scale, index) =>
                  (if scale = 0w1
                   then PPrint.empty
                   else PPrint.word scale <> text "*")
                  <> Register.toDoc index
                  <> (if disp = 0
                      then PPrint.empty
                      else space <> text "+" <+> PPrint.int disp)
               | NONE =>
                  if disp = 0
                  then raise Fail "unreachable"
                  else PPrint.int disp))
        |> brackets

    fun foldMemDefs f acc ({base, index, ...} : mem) =
        let val acc = case base
                      of SOME base => f (base, acc)
                       | NONE => acc
        in  case index
            of SOME (_, index) => f (index, acc)
             | NONE => acc
        end

    structure Oper = struct
        type def = def

        datatype t
            = MOV of def
            | LOAD of mem          (* MOV r64 m64 *)
            | LOADc of Word32.word (* MOV r64 imm64 *)
            | LOADl of Label.t     (* LEA the label *)
            | STORE of mem * def   (* MOV m64 r64 *)
            | ADD of def * def
            | SUB of def * def
            | IMUL of def * def
            | IDIV of def * def
            | CALL of string * def vector (* relative/absolute (foreign) CALL *)
            | CALLd of string * def vector (* dynamically linked (foreign) CALL *)
            | CALLi of def * def vector    (* indirect (foreign) CALL *)

        val move = MOV

        fun stackLoad sp i =
            LOAD {base = SOME sp, index = NONE, disp = 8 * i}

        fun stackStore sp i def =
            STORE ({base = SOME sp, index = NONE, disp = 8 * i}, def)

        fun foldDefs f acc =
            fn LOAD mem => foldMemDefs f acc mem
             | STORE (mem, def) => f (def, foldMemDefs f acc mem)
             | ADD (def, def') | SUB (def, def') | IMUL (def, def') | IDIV (def, def') =>
                f (def', f (def, acc))
             | LOADc _ | LOADl _ => acc
             | CALL (_, defs) | CALLd (_, defs) => Vector.foldl f acc defs
             | CALLi (def, defs) => Vector.foldl f (f (def, acc)) defs

        fun appLabels f =
            fn LOADl label => f label
             | MOV _ | LOAD _ | LOADc _ | STORE _ | ADD _ | SUB _ | IMUL _ | IDIV _ | CALL _ | CALLd _ | CALLi _ => ()

        val toDoc =
            fn MOV src => text "mov" <+> Register.toDoc src
             | LOAD mem => text "mov" <+> memToDoc mem
             | LOADc n => text "mov" <+> text (Int.toString (Word32.toInt n)) (* HACK: toInt *)
             | LOADl label => text "lea" <+> Label.toDoc label
             | STORE (target, src) =>
                text "mov" <+> memToDoc target <+> Register.toDoc src
             | CALLd (callee, args) =>
                text "call" <+> text (callee ^ "@PLT")
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
    end

    structure Transfer = struct
        type def = def

        datatype pred = Eq

        datatype t
            = JMP of Label.t * def vector (* relative/absolute JMP *)
            | JMPi of def * def vector    (* indirect JMP through register *)
            | Jcc of pred * Label.t * Label.t
            | RET of def vector

        val isReturn =
            fn RET _ => true
             | _ => false

        fun foldDefs f acc =
            fn JMP (_, defs) | RET defs => Vector.foldl f acc defs
             | JMPi (def, defs) => Vector.foldl f (f (def, acc)) defs
             | Jcc _ => acc

        fun foldLabels f acc =
            fn JMP (label, _) => f (label, acc)
             | JMPi _ | RET _ => acc
             | Jcc (_, conseq, alt) => f (alt, f (conseq, acc))

        fun appLabels f =
            fn JMP (label, _) => f label
             | JMPi _ | RET _ => ()
             | Jcc (_, conseq, alt) => (f conseq; f alt)

        val toDoc =
            fn JMP (label, args) =>
                text "jmp" <+> Label.toDoc label
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
             | JMPi (def, args) =>
                text "jmp" <+> Register.toDoc def
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
             | RET args =>
                text "ret"
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
    end
end

structure X64Instructions = X64InstructionsFn(CpsId)

structure X64Isa = IsaFn(struct
    structure Register = CpsId
    structure Instrs = X64Instructions
end)

structure X64RegInstructions = X64InstructionsFn(X64Register)

structure X64RegIsa = IsaFn(struct
    structure Register = X64Register
    structure Instrs = X64RegInstructions
end)

