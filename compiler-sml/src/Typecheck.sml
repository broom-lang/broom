structure Typecheck :> sig
    structure Type: TYPE

    exception UvOutOfScope of Name.t
    exception Unbound of Name.t
    exception Occurs of Type.t Type.TypeVars.uv * Type.t
    exception TypeMismatch of Type.t * Type.t

    val typecheck: Cst.stmt vector -> Cst.stmt vector
end = struct
    structure Type = Type
    structure TypeVars = Type.TypeVars

    exception UvOutOfScope of Name.t
    exception Unbound of Name.t
    exception Occurs of Type.t Type.TypeVars.uv * Type.t
    exception TypeMismatch of Type.t * Type.t

    fun assignLeft tenv uv t =
        let fun assignL uv =
                fn Type.ForAll _ => raise Fail "unimplemented"
                 | t as Type.OVar _ => TypeVars.uvSet uv t
                 | Type.UVar uv' => (case TypeVars.uvGet uv'
                                     of Either.Left uv' => TypeVars.uvMerge uv uv'
                                      | Either.Right t => assignL uv t)
                 | Type.Arrow _ => raise Fail "unimplemented"
                 | t as Type.Prim _ => TypeVars.uvSet uv t
        in if TypeVars.uvInScope tenv uv
           then if Type.occurs uv t
                then raise Occurs (uv, t)
                else assignL uv t
           else raise UvOutOfScope (TypeVars.uvName uv)
        end

    fun assignRight tenv uv t =
        let fun assignR uv =
                fn Type.ForAll _ => raise Fail "unimplemented"
                 | t as Type.OVar _ => TypeVars.uvSet uv t
                 | Type.UVar uv' => (case TypeVars.uvGet uv'
                                     of Either.Left uv' => TypeVars.uvMerge uv uv'
                                      | Either.Right t => assignR uv t)
                 | Type.Arrow _ => raise Fail "unimplemented"
                 | t as Type.Prim _ => TypeVars.uvSet uv t
        in if TypeVars.uvInScope tenv uv
           then if Type.occurs uv t
                then raise Occurs (uv, t)
                else assignR uv t
           else raise UvOutOfScope (TypeVars.uvName uv)
        end

    fun checkSub tenv (Type.UVar uv) (Type.UVar uv') =
        (case (TypeVars.uvGet uv, TypeVars.uvGet uv')
         of (Either.Left uv, Either.Left uv') => if TypeVars.uvEq (uv, uv')
                                                 then ()
                                                 else TypeVars.uvMerge uv uv'
          | (Either.Left uv, Either.Right t') => assignLeft tenv uv t'
          | (Either.Right t, Either.Left uv') => assignRight tenv uv' t
          | (Either.Right t, Either.Right t') => checkSub tenv t t')
      | checkSub tenv (Type.UVar uv) t' =
        (case TypeVars.uvGet uv
         of Either.Left uv => assignLeft tenv uv t'
          | Either.Right t => checkSub tenv t t')
      | checkSub tenv t (Type.UVar uv') =
        (case TypeVars.uvGet uv'
         of Either.Left uv' => assignRight tenv uv' t
          | Either.Right t' => checkSub tenv t t')
      | checkSub tenv (Type.ForAll (ov, t)) (Type.ForAll (ov', t')) = raise Fail "unimplemented"
      | checkSub tenv (t as Type.OVar ov) (t' as Type.OVar ov') = if TypeVars.ovEq (ov, ov')
                                                                  then ()
                                                                  else raise TypeMismatch (t, t')
      | checkSub tenv (Type.Arrow arr) (Type.Arrow arr') = raise Fail "unimplemented"
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
                fn Cst.Use (pos, name) => (case ValTypeCtx.find env name
                                           of SOME t => (Cst.Use (pos, name), t)
                                            | NONE => raise Unbound name)
                 | Cst.Const (pos, c) => let val (c, t) = checkConst c
                                         in (Cst.Const (pos, c), t)
                                         end

            fun checkAs env t =
                fn Cst.Use (pos, name) => (case ValTypeCtx.find env name
                                           of SOME t' => (checkSub tenv t' t; Cst.Use (pos, name))
                                            | NONE => raise Unbound name)
                 | Cst.Const (pos, c) => let val (c, t') = checkConst c
                                         in checkSub tenv t' t
                                          ; Cst.Const (pos, c)
                                         end

            and checkStmt env =
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
