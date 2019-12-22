(* TODO: Check domination and cont nesting: *)
(* MAYBE: Check dead code (unreachable from main): *)
structure CpsTypechecker :> sig
    datatype error
        = InequalKinds of Kind.t * Kind.t
        | Inequal of Cps.Type.t * Cps.Type.t
        | UnCallable of CpsId.t * Cps.Type.t
        | NonThunk of CpsId.t * Cps.Type.t
        | NonResults of CpsId.t * Cps.Type.t
        | Unbound of CpsId.t
        | UnboundLabel of Label.t
        | OutboundsParam of Label.t * int
        | OutboundsResult of CpsId.t * Cps.Type.t * int
        | Argc of int * int
        | ArgcT of int * int

    val checkProgram : Cps.Program.t -> (error, unit) Either.t
end = struct
    structure Type = Cps.Type
    structure Expr = Cps.Expr
    structure Transfer = Cps.Cont.Transfer
    structure Program = Cps.Program
    structure DefMap = Program.Map
    structure LabelMap = Program.LabelMap

    datatype typ = datatype Type.t
    datatype oper = datatype Expr.oper
    datatype transfer = datatype Transfer.t
    datatype pat = datatype Transfer.pat

    val op|> = Fn.|>

    datatype error
        = InequalKinds of Kind.t * Kind.t
        | Inequal of Cps.Type.t * Cps.Type.t
        | UnCallable of CpsId.t * Cps.Type.t
        | NonThunk of CpsId.t * Cps.Type.t
        | NonResults of CpsId.t * Cps.Type.t
        | Unbound of CpsId.t
        | UnboundLabel of Label.t
        | OutboundsParam of Label.t * int
        | OutboundsResult of CpsId.t * Cps.Type.t * int
        | Argc of int * int
        | ArgcT of int * int

    exception TypeError of error

    fun kindOf program =
        fn FnT _ => Kind.TypeK
         | Prim _ => Kind.TypeK

    fun checkKind program (kind, t) =
        let val tkind = kindOf program t
        in  if tkind = kind
            then ()
            else raise TypeError (InequalKinds (tkind, kind))
        end

    fun operType (program : Program.t) =
        fn PrimApp {opn, tArgs, vArgs} =>
            let val {tParams, vParams, codomain} = Expr.primopType opn
                do if Vector.length tArgs = Vector.length tParams
                   then Vector.zip (Vector.map #kind tParams, tArgs)
                        |> Vector.app (checkKind program)
                   else raise TypeError (ArgcT (Vector.length tParams, Vector.length tArgs))
                val mapping = Vector.zip (Vector.map #var tParams, tArgs)
                              |> FType.Id.SortedMap.fromVector
                val vParams = Vector.map (Type.substitute mapping) vParams
                val codomain = Vector.map (Type.substitute mapping) codomain
            in if Vector.length vArgs = Vector.length vParams
               then Vector.zip (vParams, vArgs)
                    |> Vector.app (checkDef program)
               else raise TypeError (Argc (Vector.length vParams, Vector.length vArgs))
             ; case codomain (* HACK *)
               of #[codomain] => codomain
                | codomain => Results codomain
            end
         | Result (def, i) =>
            (case defType program def
             of t as Results ts =>
                 if i < Vector.length ts
                 then Vector.sub (ts, i)
                 else raise TypeError (OutboundsResult (def, t, i))
              | t => raise TypeError (NonResults (def, t)))
         | EmptyRecord => Record EmptyRow
         | Label label => checkCont program label
         | Param (label, i) =>
            (case LabelMap.find (#conts program) label
             of SOME {vParams, ...} =>
                 if i < Vector.length vParams
                 then Vector.sub (vParams, i)
                 else raise TypeError (OutboundsParam (label, i))
              | NONE => raise TypeError (UnboundLabel label))
         | Const c => Prim (Const.typeOf c)

    and defType (program : Program.t) def =
        case DefMap.find (#stmts program) def
        of SOME {oper, parent = _} => operType program oper
         | NONE => raise TypeError (Unbound def)

    and checkDef program (t, def) =
        let val deft = defType program def
        in  if Type.eq (deft, t)
            then ()
            else raise TypeError (Inequal (deft, t))
        end

    and patternTyp (ConstP (Const.Int _)) = SOME (Prim PrimType.Int)
      | patternTyp AnyP = NONE

    and checkPattern program matcheeTyp pat =
        case patternTyp pat
        of SOME patTyp =>
            if not (Type.eq (patTyp, matcheeTyp))
            then raise TypeError (Inequal (matcheeTyp, patTyp))
            else ()
         | NONE => ()

    and checkClause program matcheeTyp {pattern, target} =
        ( checkPattern program matcheeTyp pattern
        ; case defType program target
          of FnT {tDomain = #[], vDomain = #[]} => ()
           | targetTyp => raise TypeError (NonThunk (target, targetTyp)) )

    and checkTransfer (program : Program.t) =
        fn Goto {callee, tArgs, vArgs} =>
            (case defType program callee
             of FnT {tDomain, vDomain} =>
                let do if Vector.length tArgs = Vector.length tDomain
                       then Vector.zip (Vector.map #kind tDomain, tArgs)
                            |> Vector.app (checkKind program)
                       else raise TypeError (ArgcT (Vector.length tDomain, Vector.length tArgs))
                    val mapping = Vector.zip (Vector.map #var tDomain, tArgs)
                                  |> FType.Id.SortedMap.fromVector
                    val vDomain = Vector.map (Type.substitute mapping) vDomain
                in if Vector.length vArgs = Vector.length vDomain
                   then Vector.zip (vDomain, vArgs)
                        |> Vector.app (checkDef program)
                   else raise TypeError (Argc (Vector.length vDomain, Vector.length vArgs))
                end
              | t => raise TypeError (UnCallable (callee, t)))
         | Match (matchee, clauses) =>
            let val matcheeTyp = defType program matchee
            in Vector.app (checkClause program matcheeTyp) clauses
            end

    and checkCont (program : Program.t) label =
        case LabelMap.find (#conts program) label
        of SOME {name = _, tParams, vParams, body} =>
            ( checkTransfer program body
            ; FnT {tDomain = tParams, vDomain = vParams} )
         | NONE => raise TypeError (UnboundLabel label)
    
    fun checkProgram (program as {typeFns, main, ...} : Program.t) =
        ( checkCont program main
        ; Either.Right () )
        handle TypeError err => Either.Left err
end

