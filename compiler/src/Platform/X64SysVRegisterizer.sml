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

    val op|> = Fn.|>

    fun allocateMem env builder label {base, index, disp} =
        let val (env, base) =
                case base
                of SOME base =>
                    let val (env, base) = Env.regUse env builder label base
                    in (env, SOME base)
                    end
                 | NONE => (env, NONE)
            val (env, index) =
                case index
                of SOME (scale, index) =>
                    let val (env, index) = Env.regUse env builder label index
                    in (env, SOME (scale, index))
                    end
                 | NONE => (env, NONE)
        in (env, {base, index, disp})
        end

    fun stmt cconvs builder label env =
        fn Isa.Stmt.Param (target, pLabel, i) => (* FIXME: *)
            let val paramRegs = #args Abi.foreignCallingConvention
            in Env.fixedRegDef env builder label target (Vector.sub (paramRegs, i))
            end

         | Isa.Stmt.Def (target, X64Instructions.Oper.CALLd (dest, args)) => (* FIXME: *)
            let val targetReg = Reg.rax
                val env = Env.fixedRegDef env builder label target targetReg
                val env = Env.evacuateCallerSaves env builder label
                val paramRegs = #args Abi.foreignCallingConvention
                val env = Vector.zip (args, paramRegs)
                        |> Vector.foldl (fn ((arg, reg), env) =>
                                             Env.fixedRegUse env builder label arg reg)
                                        env
            in Builder.insertStmt builder label (Stmt.Def (targetReg, CALLd (dest, #[])))
             ; env
            end

         | Isa.Stmt.Def (target, expr) =>
            let val (env, target) = Env.regDef env builder label target
            in  case expr
                of X64Instructions.Oper.LOAD src =>
                    let val (env, src) = allocateMem env builder label src
                    in Builder.insertStmt builder label (Stmt.Def (target, LOAD src))
                     ; env
                    end
                 | X64Instructions.Oper.LOADc n =>
                    ( Builder.insertStmt builder label (Stmt.Def (target, LOADc n))
                    ; env )
                 | X64Instructions.Oper.LOADl lLabel =>
                    ( Builder.insertStmt builder label (Stmt.Def (target, LOADl lLabel))
                    ; env )
                 | _ => env (* FIXME *)
            end
         | Isa.Stmt.Eff expr =>
            (case expr
             of X64Instructions.Oper.STORE (target, src) =>
                 let val (env, target) = allocateMem env builder label target
                     val (env, src) = Env.regUse env builder label src
                 in Builder.insertStmt builder label (Stmt.Eff (STORE (target, src)))
                  ; env
                 end
              | _ => env) (* FIXME *)
         | _ => env (* FIXME *)

    fun transfer cconvs builder label env =
        fn X64Instructions.Transfer.JMP (dest, args) =>
            (case Label.HashTable.find cconvs dest
             of SOME paramRegs =>
                  let val env = Vector.zip (args, paramRegs)
                              |> Vector.foldl (fn ((arg, reg), env) =>
                                                   Env.fixedRegUse env builder label arg reg)
                                              env
                  in Builder.setTransfer builder label (JMP (dest, #[]))
                   ; env
                  end)
         | X64Instructions.Transfer.JMPi (dest, args) =>
            let val paramRegs = Abi.escapeeCallingConvention
                val env = Vector.zip (args, paramRegs)
                        |> Vector.foldl (fn ((arg, reg), env) =>
                                             Env.fixedRegUse env builder label arg reg)
                                        env
                val (env, dest) = Env.regUse env builder label dest
            in Builder.setTransfer builder label (JMPi (dest, #[]))
             ; env
            end
         | X64Instructions.Transfer.RET args =>
            let val paramRegs = Vector.concat [ #retVal Abi.foreignCallingConvention
                                              , #calleeSaves Abi.foreignCallingConvention ]
                val env = Vector.zip (args, paramRegs)
                        |> Vector.foldl (fn ((arg, reg), env) =>
                                             Env.fixedRegUse env builder label arg reg)
                                        env
            in Builder.setTransfer builder label (RET #[])
             ; env
            end
end

