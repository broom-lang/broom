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

signature ISA = sig
    type def
    type oper

    structure Instrs : INSTRUCTIONS where type Oper.t = oper

    structure Stmt : sig
        datatype t
            = Def of def * oper
            | Eff of oper
            | Param of def * Label.t * int

        val toDoc : t -> PPrint.t
    end

    type transfer

    structure Transfer : ISA_TRANSFER where type t = transfer

    structure Cont : sig
        type t = { name : Name.t option
                 , argc : int
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        val toDoc : Label.t * t -> PPrint.t

        structure Builder : sig
            type builder

            val new : {name : Name.t option, argc : int} -> builder
            val insertStmt : builder -> Stmt.t -> unit
            val build : builder -> transfer -> t
        end
    end

    structure Program : sig
        type t = {conts : Cont.t Cps.Program.LabelMap.t, main : Label.t}

        val toDoc : t -> PPrint.t

        structure Builder : sig
            type builder

            val new : unit -> builder
            val insertCont : builder -> Label.t -> Cont.t -> unit
            val build : builder -> Label.t -> t
        end
    end
end

functor IsaFn (Args : sig
    structure Register : REGISTER
    structure Instrs : INSTRUCTIONS where type def = Register.t
end) :> ISA
    where type def = Args.Register.t
    where type oper = Args.Instrs.Oper.t
    where type transfer = Args.Instrs.Transfer.t
= struct
    structure Register = Args.Register
    structure Instrs = Args.Instrs
    structure Oper = Instrs.Oper

    type def = Register.t
    type oper = Oper.t
    type transfer = Args.Instrs.Transfer.t

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
            <> nest 4 (newline <> punctuate newline (Vector.map Stmt.toDoc stmts)
                       <++> Transfer.toDoc transfer)

        structure Builder = struct
            type builder = {name : Name.t option, argc : int, stmts : Stmt.t list ref}

            fun new {name, argc} = {name, argc, stmts = ref []}

            fun insertStmt ({stmts, ...} : builder) stmt = stmts := stmt :: !stmts

            fun build {name, argc, stmts} transfer =
                {name, argc, stmts = Vector.fromList (List.rev (!stmts)), transfer}
        end
    end

    structure Program = struct
        structure LabelMap = Cps.Program.LabelMap

        type t = {conts : Cont.t LabelMap.t, main : Label.t}

        fun toDoc {conts, main} =
            LabelMap.fold (fn (kv, acc) => acc <++> newline <> Cont.toDoc kv)
                          PPrint.empty conts
            <++> newline <++> text "entry" <+> Label.toDoc main

        structure Builder = struct
            type builder = Cont.t LabelMap.t ref

            fun new () = ref Cps.Program.LabelMap.empty

            fun insertCont builder label cont =
                builder := LabelMap.insert (!builder) (label, cont)

            fun build (ref conts) main = {conts, main}
        end
    end
end

