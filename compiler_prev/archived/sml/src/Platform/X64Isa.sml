structure X64JumpCondition = struct
    val text = PPrint.text

    datatype t = Neq | Overflow

    val toDoc =
        fn Neq => text "ne"
         | Overflow => text "o"
end

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
            | LOADg of Name.t      (* LEA the global *)
            | LOADgv of Name.t     (* MOV the global *)
            | STORE of mem * def   (* MOV m64 r64 *)
            | PUSH of def
            | LEAVE
            | ADD of def * def
            | SUB of def * def
            | SUBc of def * LargeWord.word (* HACK *)
            | IMUL of def * def
            | IDIV of def * def
            | CMP of def * Word32.word
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

        datatype pred = datatype X64JumpCondition.t

        datatype oper
            = JMP of Label.t * def vector (* relative/absolute JMP *)
            | JMPi of def * def vector    (* indirect JMP through register *)
            | Jcc of pred * Label.t * Label.t
            | RET of def vector

        type t = {pos : Pos.span, oper : oper}

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
            | LOADg of Name.t      (* LEA the global *)
            | LOADgv of Name.t     (* MOV the global *)
            | STORE of mem * def   (* MOV m64 r64 *)
            | PUSH of def
            | LEAVE
            | ADD of def * def
            | SUB of def * def
            | SUBc of def * LargeWord.word (* HACK *)
            | IMUL of def * def
            | IDIV of def * def
            | CMP of def * Word32.word
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
             | (PUSH def | SUBc (def, _)) => f (def, acc)
             | (ADD (def, def') | SUB (def, def') | IMUL (def, def') | IDIV (def, def')) =>
                f (def', f (def, acc))
             | (LOADc _ | LOADl _ | LOADg _ | LOADgv _ | LEAVE) => acc
             | (CALL (_, defs) | CALLd (_, defs)) => Vector.foldl f acc defs
             | CALLi (def, defs) => Vector.foldl f (f (def, acc)) defs

        fun appLabels f =
            fn LOADl label => f label
             | ( MOV _ | LOAD _ | LOADg _ | LOADgv _ | LOADc _ | STORE _ | PUSH _ | LEAVE
               | ADD _ | SUB _ | SUBc _ | IMUL _ | IDIV _ | CMP _ | CALL _ | CALLd _ | CALLi _ ) => ()

        val toDoc =
            fn MOV src => text "mov" <+> Register.toDoc src
             | LOAD mem => text "mov" <+> memToDoc mem
             | LOADc n => text "mov" <+> text (Word32.fmt StringCvt.DEC n)
             | LOADl label => text "lea" <+> Label.toDoc label
             | LOADg name => text "lea" <+> Name.toDoc name
             | LOADgv name => text "mov" <+> brackets (Name.toDoc name)
             | STORE (target, src) =>
                text "mov" <+> memToDoc target <+> Register.toDoc src
             | PUSH def => text "push" <+> Register.toDoc def
             | LEAVE => text "leave"
             | ADD (a, b) => text "add" <+> Register.toDoc a <> comma <+> Register.toDoc b
             | SUB (a, b) => text "sub" <+> Register.toDoc a <> comma <+> Register.toDoc b
             | IMUL (a, b) => text "imul" <+> Register.toDoc a <> comma <+> Register.toDoc b
             | SUBc (def, n) =>
                text "sub" <+> Register.toDoc def <> comma <+> text (LargeWord.fmt StringCvt.DEC n)
             | CMP (def, n) =>
                text "cmp" <+> Register.toDoc def <> comma <+> text (Word32.fmt StringCvt.DEC n)
             | CALL (callee, args) =>
                text "call" <+> text callee
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
             | CALLd (callee, args) =>
                text "call" <+> text (callee ^ "@PLT")
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
    end

    structure Transfer = struct
        type def = def

        datatype pred = datatype X64JumpCondition.t

        datatype oper
            = JMP of Label.t * def vector (* relative/absolute JMP *)
            | JMPi of def * def vector    (* indirect JMP through register *)
            | Jcc of pred * Label.t * Label.t
            | RET of def vector

        type t = {pos : Pos.span, oper : oper}

        fun isReturn {pos = _, oper} =
            case oper
            of RET _ => true
             | _ => false

        fun foldDefs f acc {pos = _, oper} =
            case oper
            of (JMP (_, defs) | RET defs) => Vector.foldl f acc defs
             | JMPi (def, defs) => Vector.foldl f (f (def, acc)) defs
             | Jcc _ => acc

        fun foldLabels f acc {pos = _, oper} =
            case oper
            of JMP (label, _) => f (label, acc)
             | (JMPi _ | RET _) => acc
             | Jcc (_, conseq, alt) => f (alt, f (conseq, acc))

        fun appLabels f {pos = _, oper} =
            case oper
            of JMP (label, _) => f label
             | (JMPi _ | RET _) => ()
             | Jcc (_, conseq, alt) => (f conseq; f alt)

        fun toDoc {pos = _, oper} =
            case oper
            of JMP (label, args) =>
                text "jmp" <+> Label.toDoc label
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
             | JMPi (def, args) =>
                text "jmp" <+> Register.toDoc def
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
             | Jcc (pred, target, target') =>
                text "j" <> X64JumpCondition.toDoc pred
                <+> Label.toDoc target <> comma <+> Label.toDoc target'
             | RET args =>
                text "ret"
                <+> parens (punctuate (comma <> space) (Vector.map Register.toDoc args))
    end
end


structure X64Instructions = X64InstructionsFn(CpsId)

structure X64Isa = IsaFn(struct
    structure Register = CpsId
    structure Location = CpsId
    structure Instrs = X64Instructions
end)

structure X64Location = Location(X64Register)

structure X64RegInstructions = X64InstructionsFn(X64Register)

structure X64RegIsa = IsaFn(struct
    structure Register = X64Register
    structure Location = X64Location
    structure Instrs = X64RegInstructions
end)

