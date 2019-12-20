(* TODO: Check domination and cont nesting: *)
(* MAYBE: Check dead code (unreachable from main): *)
structure CpsTypechecker :> sig
    datatype error
        = InequalKinds of Kind.t * Kind.t
        | Inequal of Cps.Type.t * Cps.Type.t
        | UnCallable of CpsId.t * Cps.Type.t
        | Unbound of CpsId.t
        | UnboundLabel of Label.t
        | OutboundsParam of Label.t * int

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

    val op|> = Fn.|>

    datatype error
        = InequalKinds of Kind.t * Kind.t
        | Inequal of Cps.Type.t * Cps.Type.t
        | UnCallable of CpsId.t * Cps.Type.t
        | Unbound of CpsId.t
        | UnboundLabel of Label.t
        | OutboundsParam of Label.t * int

    exception TypeError of error

    fun kindOf program =
        fn Prim _ => Kind.TypeK

    fun checkKind program (kind, t) =
        let val tkind = kindOf program t
        in  if tkind = kind
            then ()
            else raise TypeError (InequalKinds (tkind, kind))
        end

    fun operType (program : Program.t) =
        fn Param (label, i) =>
            (case LabelMap.find (#conts program) label
             of SOME {vParams, ...} =>
                 if i < Vector.length vParams
                 then Vector.sub (vParams, i)
                 else raise TypeError (OutboundsParam (label, i))
              | NONE => raise TypeError (UnboundLabel label))
         | Const c => Prim (Const.typeOf c)

    fun defType (program : Program.t) def =
        case DefMap.find (#stmts program) def
        of SOME {oper, parent = _} => operType program oper
         | NONE => raise TypeError (Unbound def)

    fun checkDef program (t, def) =
        let val deft = defType program def
        in  if Type.eq (deft, t)
            then ()
            else raise TypeError (Inequal (deft, t))
        end

    fun checkTransfer (program : Program.t) =
        fn Goto {callee, tArgs, vArgs} =>
            (case defType program callee
             of FnT {tDomain, vDomain} =>
                 ( if Vector.length tArgs = Vector.length tDomain
                   then Vector.zip (Vector.map #kind tDomain, tArgs)
                        |> Vector.app (checkKind program)
                   else ()
                 ; if Vector.length vArgs = Vector.length vDomain
                   then Vector.zip (vDomain, vArgs)
                        |> Vector.app (checkDef program)
                   else () )
              | t => raise TypeError (UnCallable (callee, t)))
         | Match (matchee, clauses) =>
            raise Fail "unimplemented"

    fun checkCont (program : Program.t) label =
        case LabelMap.find (#conts program) label
        of SOME {name = _, tParams = _, vParams = _, body} =>
            checkTransfer program body
         | NONE => raise TypeError (UnboundLabel label)
    
    fun checkProgram (program as {typeFns, main, ...} : Program.t) =
        Either.Right (checkCont program main)
        handle TypeError err => Either.Left err
end

