structure X64InstrSelection = InstrSelectionFn(struct
    structure Isa = X64Isa
    structure Type = Cps.Type
    structure Global = Cps.Global
    structure Builder = Isa.Program.Builder

    datatype oper = datatype Cps.Expr.oper
    datatype pat = datatype Cps.Transfer.pat
    datatype transfer = datatype Cps.Transfer.oper
    datatype instr = datatype X64Instructions.Oper.t
    datatype stmt = datatype Isa.Stmt.t
    datatype transfer = datatype X64Instructions.Transfer.oper

    structure Implement = struct
        fun global program builder name =
            let val v = Cps.Program.global program name
            in Global.appDeps (global program builder) v
             ; Builder.insertGlobal builder name v
            end

        fun expr program builder parent def typ {pos, oper, parent = _, typ = _} =
            case oper
            of ClosureNew (layout, label, clovers) =>
                let val ldef = CpsId.fresh ()
                in Builder.insertStmt builder parent (Def (pos, def, typ, CALL ("Broom_allocate", #[layout])))
                 ; Builder.insertStmt builder parent (Def (pos, ldef, Cps.Program.labelType program label, LOADl label))
                 ; Builder.insertStmt builder parent (Eff (pos, STORE ( { base = SOME def
                                                                   , index = NONE
                                                                   , disp = 0 }
                                                                 , ldef )))
                 ; Vector.appi (fn (i, clover) =>
                                    let val disp = X64RegInstructions.registerSize * (1 + i)
                                    in Builder.insertStmt builder parent
                                                          (Eff (pos, STORE ( { base = SOME def
                                                                        , index = NONE
                                                                        , disp }
                                                                      , clover )))
                                    end)
                               clovers
                 ; #[def]
                end
             | ClosureFn closure =>
                ( Builder.insertStmt builder parent (Def (pos, def, typ, LOAD { base = SOME closure
                                                                         , index = NONE
                                                                         , disp = 0 }))
                ; #[def] )
             | Clover (closure, i) =>
                let val disp = X64RegInstructions.registerSize * (1 + i)
                in Builder.insertStmt builder parent (Def (pos, def, typ, LOAD { base = SOME closure
                                                                          , index = NONE
                                                                          , disp }))
                 ; #[def]
                end
             | EmptyRecord =>
                ( Builder.insertStmt builder parent (Def (pos, def, typ, LOADc 0w0))
                ; #[def] )
             | Cps.Expr.Param (label, i) =>
                ( Builder.setParam builder parent i def
                ; #[def] )
             | PrimApp {opn, tArgs = _, vArgs} =>
                (case opn
                 of Primop.StackNew => (* HACK: *)
                     ( Builder.insertStmt builder parent (Def (pos, def, typ, LOADc 0w0))
                     ; #[def] )
                  | Primop.BoxNew =>
                     let val #[] = vArgs
                         val layout = CpsId.fresh ()
                         val layoutTyp = Type.Prim PrimType.Layout
                     in expr program builder parent layout layoutTyp
                             {pos, oper = Global (Name.fromString "layout_Box"), parent = SOME parent, typ = layoutTyp} (* HACK *)
                      ; Builder.insertStmt builder parent (Def (pos, def, typ, CALL ("Broom_allocate", #[layout])))
                      ; #[def]
                     end
                  | Primop.BoxInit =>
                     let val #[stack, dest, src] = vArgs
                     in Builder.insertStmt builder parent (Eff (pos, STORE ( { base = SOME dest
                                                                        , index = NONE
                                                                        , disp = 0 }
                                                                      , src )))
                      ; #[stack]
                     end
                  | Primop.BoxGet =>
                     let val #[stack, box] = vArgs
                         val v = CpsId.fresh ()
                     in Builder.insertStmt builder parent (Def (pos, v, typ, LOAD { base = SOME box
                                                                             , index = NONE
                                                                             , disp = 0 }))
                      ; #[stack, v]
                     end)
             | Result (vals, i) => raise Fail "unreachable"
             | Global name =>
                ( global program builder name
                ; Builder.insertStmt builder parent (Def (pos, def, typ, LOADg name))
                ; #[def] )
             | Const (Const.Int n) => (* FIXME: `n` might not fit into 32 bits: *)
                ( Builder.insertStmt builder parent (Def (pos, def, typ, LOADc (Word32.fromInt n)))
                ; #[def] )

        fun checked builder label pos {opn, tArgs = #[], vArgs = #[a, b], succeed, fail} =
            let val instr =
                    case opn
                    of Primop.IAdd => ADD
                     | Primop.ISub => SUB
                     | Primop.IMul => IMUL
                val (succDef, typ) = Pair.first valOf (Builder.getParam builder succeed 0)
            in Builder.setParams builder succeed (Array.fromList [])
             ; Builder.insertStmt builder label (Def (pos, succDef, typ, instr (a, b)))
             ; Jcc (X64Instructions.Transfer.Overflow, succeed, fail)
            end

        fun transfer builder label {pos, oper} =
            {pos, oper =
            case oper
            of Goto {callee, tArgs = _, vArgs} => JMP (callee, vArgs)
             | Jump {callee, tArgs = _, vArgs} => JMPi (callee, vArgs)
             | Match (matchee, #[{pattern = AnyP, target}]) => JMP (target, #[])
             | Match (matchee, #[ {pattern = ConstP (Const.Int n), target}
                                , {pattern = AnyP, target = target'} ]) => (* FIXME: n might not fit in 32 bits: *)
                ( Builder.insertStmt builder label (Eff (pos, CMP (matchee, Word32.fromInt n)))
                ; Jcc (X64Instructions.Transfer.Neq, target, target') )
             | Checked args => checked builder label pos args
             | Return (_, args) => RET args }
    end
end)

