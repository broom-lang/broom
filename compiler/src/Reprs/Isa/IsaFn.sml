signature REGISTER = sig
    type t

    val toDoc : t -> PPrint.t
end

signature ISA_OPER = sig
    type t

    val toDoc : t -> PPrint.t
end

signature ISA_TRANSFER = sig
    type t

    val toDoc : t -> PPrint.t
end

signature INSTRUCTIONS = sig
    type def

    structure Oper : ISA_OPER

    structure Transfer : ISA_TRANSFER
end

functor IsaFn (Args : sig
    structure Register : REGISTER
    structure Instrs : INSTRUCTIONS where type def = Register.t
end) :> sig
    type def = Args.Register.t
    type oper = Args.Instrs.Oper.t

    structure Stmt : sig
        datatype t
            = Def of def * oper
            | Eff of oper
            | Param of def * Label.t * int

        val toDoc : t -> PPrint.t
    end

    structure Transfer : ISA_TRANSFER where type t = Args.Instrs.Transfer.t

    structure Cont : sig
        type t = { name : Name.t option
                 , argc : int
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        val toDoc : Label.t * t -> PPrint.t
    end

    structure Program : sig
        type t = {conts : Cont.t Cps.Program.LabelMap.t, main : Label.t}

        val toDoc : t -> PPrint.t

        structure Builder : sig
            type builder

            val new : unit -> builder
            val build : builder -> Label.t -> t
        end
    end
end = struct
    structure Register = Args.Register
    structure Oper = Args.Instrs.Oper

    type def = Register.t
    type oper = Oper.t

    val text = PPrint.text
    val newline = PPrint.newline
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>
    val punctuate = PPrint.punctuate
    val nest = PPrint.nest

    structure Stmt = struct
        datatype t
            = Def of def * oper
            | Eff of oper
            | Param of def * Label.t * int

        val toDoc =
            fn Def (reg, oper) => Register.toDoc reg <+> text "=" <+> Oper.toDoc oper
             | Eff oper => Oper.toDoc oper
             | Param (reg, label, i) =>
                Register.toDoc reg <+> text "="
                <+> text "param" <+> Label.toDoc label <+> PPrint.int i
    end

    structure Transfer = Args.Instrs.Transfer

    structure Cont = struct
        type t = { name : Name.t option
                 , argc : int
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        fun toDoc (label, {name, argc, stmts, transfer}) =
            text "fun" <+> Label.toDoc label <+> PPrint.int argc <+> text "="
            <++> nest 4 (punctuate newline (Vector.map Stmt.toDoc stmts)
                         <++> Transfer.toDoc transfer)
    end

    structure Program = struct
        structure LabelMap = Cps.Program.LabelMap

        type t = {conts : Cont.t LabelMap.t, main : Label.t}

        fun toDoc {conts, main} =
            LabelMap.fold (fn (kv, acc) => acc <++> newline <> Cont.toDoc kv)
                          PPrint.empty conts
            <++> newline <++> text "entry" <+> Label.toDoc main

        structure Builder = struct
            type builder = Cont.t Cps.Program.LabelMap.t ref

            fun new () = ref Cps.Program.LabelMap.empty

            fun build (ref conts) main = {conts, main}
        end
    end
end

