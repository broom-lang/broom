functor LinearizeFn (Args : sig
    structure SeqIsa : SEQ_ISA
    structure LabelUses : LABEL_USES
        where type Isa.Stmt.t = SeqIsa.RegIsa.Stmt.t
        where type Isa.transfer = SeqIsa.RegIsa.transfer
end) :> sig
    val linearize : Args.SeqIsa.RegIsa.Program.t -> Args.SeqIsa.Program.t
end = struct
    structure SeqIsa = Args.SeqIsa
    structure RegIsa = SeqIsa.RegIsa
    structure LabelMap = Cps.Program.LabelMap
    structure Builder = SeqIsa.Program.Builder

    fun linearize (program as {conts, main}) =
        let val labelUses = Args.LabelUses.useCounts program
            val builder = Builder.new ()
            val worklist = Queue.mkQueue ()
            val visited = Label.HashSetMut.mkEmpty 0

            fun schedule label = Queue.enqueue (worklist, label)

            fun linearizeStmt stmt = RegIsa.Stmt.appLabels schedule stmt

            fun linearizeSucc label =
                let val {calls, ...} = LabelMap.lookup labelUses label
                in  if calls = 1
                    then linearizeEBB label
                    else schedule label
                end

            and linearizeTransfer transfer = RegIsa.Transfer.appLabels linearizeSucc transfer

            and linearizeEBB label =
                if not (Label.HashSetMut.member (visited, label))
                then let do Label.HashSetMut.add (visited, label)
                         val cont as {name, cconv, argc, stmts, transfer} = LabelMap.lookup conts label
                     in Builder.appendCont builder (label, cont)
                      ; Vector.app linearizeStmt stmts
                      ; linearizeTransfer transfer
                     end
                else ()

            fun processLabels () =
                case Queue.next worklist
                of SOME label =>
                    ( linearizeEBB label
                    ; processLabels () )
                 | NONE => ()

            do linearizeEBB main
            do processLabels ()
        in Builder.build builder
        end
end

