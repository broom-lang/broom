structure Typecheck :> sig
    exception UvOutOfScope of Name.t
    exception OvOutOfScope of Name.t
    exception Unbound of Name.t
    exception UnboundType of Name.t
    exception Occurs of Type.t Type.TypeVars.uv * Type.t
    exception Uncallable of Cst.expr * Type.t
    exception TypeMismatch of Type.t * Type.t
    exception MalformedType of Type.t

    val typecheck: Cst.stmt vector -> Cst.stmt vector
end = struct
    structure TypeVars = Type.TypeVars

    exception UvOutOfScope of Name.t
    exception OvOutOfScope of Name.t
    exception Unbound of Name.t
    exception UnboundType of Name.t
    exception Occurs of Type.t Type.TypeVars.uv * Type.t
    exception Uncallable of Cst.expr * Type.t
    exception TypeMismatch of Type.t * Type.t
    exception MalformedType of Type.t

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    fun withOv tenv name f = let val ov = TypeVars.pushOv tenv name
                                 val res = f ov
                             in TypeVars.popOv tenv ov
                              ; res
                             end

    fun withMarker tenv f = let val marker = TypeVars.pushMarker tenv
                                val res = f ()
                            in TypeVars.popMarker tenv marker
                             ; res
                            end

    fun articulate tenv uv =
        let val cuv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
            val duv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
        in (duv, cuv)
        end

    fun annFreeVars annEnv =
        fn Cst.ForAll (_, param, t) =>
            annFreeVars (ValTypeCtx.insert annEnv param (Type.UseT param)) t
         | Cst.UseT (_, name) => if isSome (ValTypeCtx.find annEnv name)
                                 then NameSortedSet.empty
                                 else NameSortedSet.fromList [name]
         | Cst.Arrow (_, {domain, codomain}) =>
            NameSortedSet.union (annFreeVars annEnv domain, annFreeVars annEnv codomain)
         | Cst.Prim _ => NameSortedSet.empty

    fun hydrate annEnv =
        fn Cst.ForAll (_, param, t) =>
            Type.ForAll (param, hydrate (ValTypeCtx.insert annEnv param (Type.UseT param)) t)
         | Cst.UseT (_, name) => (case ValTypeCtx.find annEnv name
                                  of SOME t => t
                                   | NONE => raise UnboundType name)
         | Cst.Arrow (_, {domain, codomain}) => Type.Arrow { domain = hydrate annEnv domain
                                                           , codomain = hydrate annEnv codomain }
         | Cst.Prim (_, p) => Type.Prim p

    val checkConst = fn c as Const.Int _ => (c, Type.Prim Type.Int)

    datatype 'a goal = Unannotated of Name.t * 'a

    val stmtGoal = fn Cst.Def (_, name, _) => Unannotated (name, Name.fresh ())

    fun typecheck program =
        let val tenv = TypeVars.newEnv ()

            fun assignForSome annEnv param y uv t =
                case y
                of Sub => withOv tenv param (fn ov =>
                              assign annEnv y uv (Type.substitute (param, Type.OVar ov) t)
                          )
                 | Super => withMarker tenv (fn () =>
                                let val uv' = TypeVars.pushUv tenv (Name.fresh ())
                                in assign annEnv y uv (Type.substitute (param, Type.UVar uv') t)
                                end
                            )

            and assign annEnv y uv t =
                let fun doassign annEnv uv =
                        fn Type.ForAll (param, t') => assignForSome annEnv param y uv t'
                         | t as Type.UseT _ => raise Fail "unreachable"
                         | t as Type.OVar _ => TypeVars.uvSet uv t
                         | Type.UVar uv' => (case TypeVars.uvGet uv'
                                             of Either.Left uv' => TypeVars.uvMerge uv uv'
                                              | Either.Right t => doassign annEnv uv t)
                         | Type.Arrow {domain, codomain} =>
                            let val (duv, cuv) = articulate tenv uv
                            in assign annEnv (flipY y) duv domain
                             ; assign annEnv y cuv codomain
                            end
                         | t as Type.Prim _ => TypeVars.uvSet uv t
                in if TypeVars.uvInScope uv
                   then if Type.occurs uv t
                        then raise Occurs (uv, t)
                        else doassign annEnv uv t
                   else raise UvOutOfScope (TypeVars.uvName uv)
                end

            fun checkSub annEnv (Type.UVar uv) (Type.UVar uv') =
                (case (TypeVars.uvGet uv, TypeVars.uvGet uv')
                 of (Either.Left uv, Either.Left uv') =>
                     if TypeVars.uvInScope uv
                     then if TypeVars.uvInScope uv'
                          then if TypeVars.uvEq (uv, uv') then () else TypeVars.uvMerge uv uv'
                          else raise UvOutOfScope (TypeVars.uvName uv')
                     else raise UvOutOfScope (TypeVars.uvName uv)
                  | (Either.Left uv, Either.Right t') => assign annEnv Sub uv t'
                  | (Either.Right t, Either.Left uv') => assign annEnv Super uv' t
                  | (Either.Right t, Either.Right t') => checkSub annEnv t t')
              | checkSub annEnv (Type.UVar uv) t' =
                (case TypeVars.uvGet uv
                 of Either.Left uv => assign annEnv Sub uv t'
                  | Either.Right t => checkSub annEnv t t')
              | checkSub annEnv t (Type.UVar uv') =
                (case TypeVars.uvGet uv'
                 of Either.Left uv' => assign annEnv Super uv' t
                  | Either.Right t' => checkSub annEnv t t')
              | checkSub annEnv t (Type.ForAll (param, t')) =
                withOv tenv param (fn ov =>
                    checkSub annEnv t (Type.substitute (param, Type.OVar ov) t')
                )
              | checkSub annEnv (Type.ForAll (ov, t)) t' =
                withMarker tenv (fn () =>
                    let val uv = TypeVars.pushUv tenv (Name.fresh ())
                    in checkSub annEnv (Type.substitute (ov, Type.UVar uv) t) t'
                    end
                )
              | checkSub annEnv (t as Type.OVar ov) (t' as Type.OVar ov') =
                if TypeVars.ovInScope ov
                then if TypeVars.ovInScope ov'
                     then if TypeVars.ovEq (ov, ov') then () else raise TypeMismatch (t, t')
                     else raise OvOutOfScope (TypeVars.ovName ov)
                else raise OvOutOfScope (TypeVars.ovName ov')
              | checkSub annEnv (Type.Arrow arr) (Type.Arrow arr') =
                 ( checkSub annEnv (#domain arr') (#domain arr)
                 ; checkSub annEnv (#codomain arr) (#codomain arr') )
              | checkSub annEnv (t as Type.Prim p) (t' as Type.Prim p') = if p = p'
                                                                   then ()
                                                                   else raise TypeMismatch (t, t')
              | checkSub annEnv t t' = raise TypeMismatch (t, t')

            fun check annEnv env =
                fn Cst.Fn (pos, param, body) =>
                    let val domain = Type.UVar (TypeVars.pushUv tenv (Name.fresh ()))
                        val codomain = Type.UVar (TypeVars.pushUv tenv (Name.fresh ()))
                    in withMarker tenv (fn () =>
                           let val env = ValTypeCtx.insert env param domain
                               val body' = checkAs annEnv env codomain body
                           in (Cst.Fn (pos, param, body'), Type.Arrow {domain, codomain})
                           end
                       )
                    end
                 | Cst.App (pos, {callee, arg}) =>
                    let val (callee', {domain, codomain}) = coerceCallee (check annEnv env callee)
                        val arg' = checkAs annEnv env domain arg
                    in (Cst.App (pos, {callee = callee', arg = arg'}), codomain)
                    end
                 | Cst.Ann (pos, expr, ann) =>
                    let val t = hydrate annEnv ann
                    in if Type.isWellFormedType annEnv t
                       then let val expr' = checkAs annEnv env t expr
                            in (Cst.Ann (pos, expr', ann), t)
                            end
                       else raise MalformedType t
                    end
                 | Cst.Use (pos, name) => (case ValTypeCtx.find env name
                                           of SOME t => (Cst.Use (pos, name), t)
                                            | NONE => raise Unbound name)
                 | Cst.Const (pos, c) => let val (c, t) = checkConst c
                                         in (Cst.Const (pos, c), t)
                                         end

            and checkAs annEnv env (Type.ForAll (param, t)) expr =
                withOv tenv param (fn ov =>
                    checkAs annEnv env (Type.substitute (param, Type.OVar ov) t) expr
                )
              | checkAs annEnv env (Type.Arrow {domain, codomain}) (Cst.Fn (pos, param, body)) =
                withMarker tenv (fn () =>
                    let val env = ValTypeCtx.insert env param domain
                        val body' = checkAs annEnv env codomain body
                    in Cst.Fn (pos, param, body')
                    end
                )
              | checkAs annEnv env t expr =
                let val (expr', t') = check annEnv env expr
                in checkSub annEnv t' t
                 ; expr'
                end

            and coerceCallee (callee, t) =
                (case t
                 of Type.ForAll (ov, t') =>
                     let val uv = TypeVars.pushUv tenv (Name.fresh ())
                     in coerceCallee (callee, Type.substitute (ov, Type.UVar uv) t')
                     end
                  | Type.UVar uv =>
                     (case TypeVars.uvGet uv
                      of Either.Left uv =>
                          let val (duv, cuv) = articulate tenv uv
                          in (callee, {domain = Type.UVar duv, codomain = Type.UVar cuv})
                          end
                      | Either.Right t' => coerceCallee (callee, t'))
                  | Type.Arrow arr => (callee, arr)
                  | _ => raise Uncallable (callee, t))

            fun checkStmt annEnv env =
                fn Cst.Def (pos, name, expr) => let val t = valOf (ValTypeCtx.find env name)
                                                    val expr' = checkAs annEnv env t expr
                                                in Cst.Def (pos, name, expr')
                                                end

            fun checkStmts annEnv env stmts =
                let val goals = Vector.map stmtGoal stmts
                    val inferGoals = Vector.map (fn Unannotated b => b) goals
                    val uvs = TypeVars.pushUvs tenv (Vector.map #2 inferGoals)
                    val env = Vector.foldli (fn (i, (name, _), valUvs) =>
                                                 let val uv = Vector.sub (uvs, i)
                                                 in ValTypeCtx.insert valUvs name (Type.UVar uv)
                                                 end)
                                            env inferGoals
                in Vector.map (checkStmt annEnv env) stmts
                end                                  
        in checkStmts ValTypeCtx.empty ValTypeCtx.empty program
        end
end
