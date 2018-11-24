structure Typecheck :> sig
    exception UvOutOfScope of Name.t
    exception OvOutOfScope of Name.t
    exception Unbound of Name.t
    exception Occurs of Type.t Type.TypeVars.uv * Type.t
    exception Uncallable of Cst.expr * Type.t
    exception TypeMismatch of Type.t * Type.t

    val typecheck: Cst.stmt vector -> Cst.stmt vector
end = struct
    structure TypeVars = Type.TypeVars

    exception UvOutOfScope of Name.t
    exception OvOutOfScope of Name.t
    exception Unbound of Name.t
    exception Occurs of Type.t Type.TypeVars.uv * Type.t
    exception Uncallable of Cst.expr * Type.t
    exception TypeMismatch of Type.t * Type.t

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    fun assignForSome tenv ov y uv t =
        case y
        of Sub => ( TypeVars.pushOv tenv ov
                  ; assign tenv y uv t
                  ; TypeVars.popOv tenv ov )
         | Super => let val (uv', marker) = TypeVars.pushScopedUv tenv (Name.fresh ())
                    in assign tenv y uv (Type.substitute (ov, Type.UVar uv') t)
                     ; TypeVars.popMarker tenv marker
                    end

    and assign tenv y uv t =
        let fun doAssign uv =
                fn Type.ForAll (ov, t') => assignForSome tenv ov y uv t'
                 | t as Type.OVar _ => TypeVars.uvSet uv t
                 | Type.UVar uv' => (case TypeVars.uvGet uv'
                                     of Either.Left uv' => TypeVars.uvMerge uv uv'
                                      | Either.Right t => doAssign uv t)
                 | Type.Arrow {domain, codomain} =>
                    let val cuv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
                        val duv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
                    in assign tenv (flipY y) duv domain
                     ; assign tenv y cuv codomain
                    end
                 | t as Type.Prim _ => TypeVars.uvSet uv t
        in if TypeVars.uvInScope tenv uv
           then if Type.occurs uv t
                then raise Occurs (uv, t)
                else doAssign uv t
           else raise UvOutOfScope (TypeVars.uvName uv)
        end

    fun checkSub tenv (Type.UVar uv) (Type.UVar uv') =
        (case (TypeVars.uvGet uv, TypeVars.uvGet uv')
         of (Either.Left uv, Either.Left uv') =>
             if TypeVars.uvInScope tenv uv
             then if TypeVars.uvInScope tenv uv'
                  then if TypeVars.uvEq (uv, uv') then () else TypeVars.uvMerge uv uv'
                  else raise UvOutOfScope (TypeVars.uvName uv')
             else raise UvOutOfScope (TypeVars.uvName uv)
          | (Either.Left uv, Either.Right t') => assign tenv Sub uv t'
          | (Either.Right t, Either.Left uv') => assign tenv Super uv' t
          | (Either.Right t, Either.Right t') => checkSub tenv t t')
      | checkSub tenv (Type.UVar uv) t' =
        (case TypeVars.uvGet uv
         of Either.Left uv => assign tenv Sub uv t'
          | Either.Right t => checkSub tenv t t')
      | checkSub tenv t (Type.UVar uv') =
        (case TypeVars.uvGet uv'
         of Either.Left uv' => assign tenv Super uv' t
          | Either.Right t' => checkSub tenv t t')
      | checkSub tenv t (Type.ForAll (ov, t')) = ( TypeVars.pushOv tenv ov
                                                 ; checkSub tenv t t'
                                                 ; TypeVars.popOv tenv ov )
      | checkSub tenv (Type.ForAll (ov, t)) t' =
        let val (uv, marker) = TypeVars.pushScopedUv tenv (Name.fresh ())
        in checkSub tenv (Type.substitute (ov, Type.UVar uv) t) t'
         ; TypeVars.popMarker tenv marker
        end
      | checkSub tenv (t as Type.OVar ov) (t' as Type.OVar ov') =
        if TypeVars.ovInScope tenv ov
        then if TypeVars.ovInScope tenv ov'
             then if TypeVars.ovEq (ov, ov') then () else raise TypeMismatch (t, t')
             else raise OvOutOfScope (TypeVars.ovName ov)
        else raise OvOutOfScope (TypeVars.ovName ov')
      | checkSub tenv (Type.Arrow arr) (Type.Arrow arr') =
         ( checkSub tenv (#domain arr') (#domain arr)
         ; checkSub tenv (#codomain arr) (#codomain arr') )
      | checkSub _ (t as Type.Prim p) (t' as Type.Prim p') = if p = p'
                                                             then ()
                                                             else raise TypeMismatch (t, t')
      | checkSub _ t t' = raise TypeMismatch (t, t')

    val checkConst = fn c as Const.Int _ => (c, Type.Prim Type.Int)

    datatype 'a goal = Unannotated of Name.t * 'a

    val stmtGoal = fn Cst.Def (_, name, _) => Unannotated (name, Name.fresh ())

    fun typecheck program =
        let val tenv = TypeVars.newEnv ()

            fun check env =
                fn Cst.Fn (pos, param, body) =>
                    let val domain = Type.UVar (TypeVars.pushUv tenv (Name.fresh ()))
                        val codomain = Type.UVar (TypeVars.pushUv tenv (Name.fresh ()))
                        val marker = TypeVars.pushMarker tenv
                        val env = ValTypeCtx.insert env param domain
                        val body' = checkAs env codomain body
                    in TypeVars.popMarker tenv marker
                     ; (Cst.Fn (pos, param, body'), Type.Arrow {domain, codomain})
                    end
                 | Cst.App (pos, {callee, arg}) =>
                    let val (callee', {domain, codomain}) = coerceCallee env (check env callee)
                        val arg' = checkAs env domain arg
                    in (Cst.App (pos, {callee = callee', arg = arg'}), codomain)
                    end
                 | Cst.Use (pos, name) => (case ValTypeCtx.find env name
                                           of SOME t => (Cst.Use (pos, name), t)
                                            | NONE => raise Unbound name)
                 | Cst.Const (pos, c) => let val (c, t) = checkConst c
                                         in (Cst.Const (pos, c), t)
                                         end

            and checkAs env (Type.ForAll (ov, t)) expr =
                let val _ = TypeVars.pushOv tenv ov
                    val expr' = checkAs env t expr
                in TypeVars.popOv tenv ov
                 ; expr'
                end
              | checkAs env (Type.Arrow {domain, codomain}) (Cst.Fn (pos, param, body)) =
                let val marker = TypeVars.pushMarker tenv
                    val env = ValTypeCtx.insert env param domain
                    val body' = checkAs env codomain body
                in TypeVars.popMarker tenv marker
                 ; Cst.Fn (pos, param, body')
                end
              | checkAs env t expr =
                let val (expr', t') = check env expr
                in checkSub tenv t' t
                 ; expr'
                end

            and coerceCallee env (callee, t) =
                (case t
                 of Type.ForAll (ov, t') =>
                     let val uv = TypeVars.pushUv tenv (Name.fresh ())
                     in coerceCallee env (callee, Type.substitute (ov, Type.UVar uv) t')
                     end
                  | Type.UVar uv =>
                     (case TypeVars.uvGet uv
                      of Either.Left uv =>
                          let val cuv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
                              val duv = TypeVars.insertUvBefore tenv uv (Name.fresh ())
                          in (callee, { domain = Type.UVar duv
                                      , codomain = Type.UVar cuv })
                          end
                      | Either.Right t' => coerceCallee env (callee, t'))
                  | Type.Arrow arr => (callee, arr)
                  | _ => raise Uncallable (callee, t))

            fun checkStmt env =
                fn Cst.Def (pos, name, expr) => let val t = valOf (ValTypeCtx.find env name)
                                                    val expr' = checkAs env t expr
                                                in Cst.Def (pos, name, expr')
                                                end

            fun checkStmts env stmts =
                let val goals = Vector.map stmtGoal stmts
                    val inferGoals = Vector.map (fn Unannotated b => b) goals
                    val uvs = TypeVars.pushUvs tenv (Vector.map #2 inferGoals)
                    val env = Vector.foldli (fn (i, (name, _), valUvs) =>
                                                 let val uv = Vector.sub (uvs, i)
                                                 in ValTypeCtx.insert valUvs name (Type.UVar uv)
                                                 end)
                                            env inferGoals
                in Vector.map (checkStmt env) stmts
                end                                  
        in checkStmts ValTypeCtx.empty program
        end
end
