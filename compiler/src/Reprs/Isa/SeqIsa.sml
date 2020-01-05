signature SEQ_ISA = sig
    structure RegIsa : ISA

    structure Program : sig
        type t = (Label.t * RegIsa.Cont.t) vector

        val toDoc : t -> PPrint.t

        structure Builder : sig
            type builder

            val new : unit -> builder
            val appendCont : builder -> Label.t * RegIsa.Cont.t -> unit
            val build : builder -> t
        end
    end
end

functor SeqIsaFn (RegIsa : ISA) :> SEQ_ISA
    where type RegIsa.Stmt.t = RegIsa.Stmt.t
    where type RegIsa.Transfer.t = RegIsa.Transfer.t
= struct
    structure RegIsa = RegIsa
    structure Cont = RegIsa.Cont

    val text = PPrint.text
    val newline = PPrint.newline
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>

    structure Program = struct
        type t = (Label.t * RegIsa.Cont.t) vector

        fun toDoc kvs =
            Vector.foldl (fn (kv, acc) => acc <++> newline <> Cont.toDoc kv)
                         PPrint.empty kvs

        structure Builder = struct
            type builder = (Label.t * RegIsa.Cont.t) list ref

            fun new () = ref []

            fun appendCont builder kv = builder := kv :: (!builder)

            fun build (ref kvs) = Vector.fromList (List.rev kvs)
        end
    end
end

