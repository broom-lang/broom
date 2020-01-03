(* FIXME: Freeing registers *)
structure X64SysVRegisterizer = struct
    structure Abi = X64SysVAbi
    structure Isa = Abi.Isa
    structure RegIsa = Abi.RegIsa
    structure Reg = X64Register
    structure Env = RegisterEnvFn(Abi)
    structure Builder = RegIsa.Program.Builder
    structure Stmt = RegIsa.Stmt

    datatype oper = datatype X64RegInstructions.Oper.t
    datatype transfer = datatype X64RegInstructions.Transfer.t

    fun stmt lastUses cconvs builder label env i =
        fn Isa.Stmt.Param (dest, pLabel, i) =>
            let val reg = Vector.sub (Label.HashTable.lookup cconvs pLabel, i)
            in Env.insertReg env dest reg (* OK since `reg` must be free at `Param`:s *)
            end
         | Isa.Stmt.Def (dest, expr) =>
            (case expr
             of X64Instructions.Oper.LOAD src =>
                 let val src = Env.lookupReg env src
                               handle Subscript => Reg.rax (* FIXME *)
                 in  case Env.allocateReg env dest
                      of SOME (env, dest) =>
                          ( Builder.insertStmt builder label (Stmt.Def (dest, LOAD src))
                          ; env )
                 end
              | X64Instructions.Oper.LOADc n =>
                 (case Env.allocateReg env dest
                  of SOME (env, dest) =>
                      ( Builder.insertStmt builder label (Stmt.Def (dest, LOADc n))
                      ; env ))
              | X64Instructions.Oper.LOADl lLabel =>
                 (case Env.allocateReg env dest
                  of SOME (env, dest) =>
                      ( Builder.insertStmt builder label (Stmt.Def (dest, LOADl lLabel))
                      ; env ))
              | _ => env) (* FIXME *)
         | Isa.Stmt.Eff expr =>
            (case expr
             of X64Instructions.Oper.STORE (target, src) =>
                 let val target = Env.lookupReg env target handle Subscript => Reg.rax (* FIXME *)
                     val src = Env.lookupReg env src handle Subscript => Reg.rax (* FIXME *)
                 in Builder.insertStmt builder label (Stmt.Eff (STORE (target, src)))
                  ; env
                 end
              | _ => env) (* FIXME *)
         | _ => env (* FIXME *)

    (* FIXME: Arg shuffling etc: *)
    fun transfer lastUses cconvs builder label env =
        fn X64Instructions.Transfer.JMP (target, args) =>
            ( Builder.setTransfer builder label (JMP (target, #[]))
            ; env )
         | X64Instructions.Transfer.JMPi (target, args) =>
            let val target = Env.lookupReg env target
                             handle Subscript => Reg.rax (* FIXME *)
            in Builder.setTransfer builder label (JMPi (target, #[]))
             ; env
            end
end

