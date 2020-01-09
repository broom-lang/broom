(* TODO: Check domination and cont nesting: *)
(* MAYBE: Check dead code (unreachable from main): *)
structure CpsTypechecker :> sig
    datatype error
        = InequalKinds of Kind.t * Kind.t
        | Inequal of Cps.Type.t * Cps.Type.t
        | UnGoable of Label.t * Cps.Type.t
        | UnCallable of CpsId.t * Cps.Type.t
        | NonThunk of Label.t * Cps.Type.t
        | NonResults of CpsId.t * Cps.Type.t
        | NonClosure of CpsId.t * Cps.Type.t
        | Unbound of CpsId.t
        | UnboundLabel of Label.t
        | OutboundsParam of Label.t * int
        | OutboundsResult of CpsId.t * Cps.Type.t * int
        | OutboundsClover of CpsId.t * int
        | Argc of int * int
        | ArgcT of int * int

    val errorToDoc : error -> PPrint.t

    val defType : Cps.Program.t -> CpsId.t -> Cps.Type.t
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
    val text = PPrint.text
    val op<+> = PPrint.<+>

    datatype error
        = InequalKinds of Kind.t * Kind.t
        | Inequal of Cps.Type.t * Cps.Type.t
        | UnGoable of Label.t * Cps.Type.t
        | UnCallable of CpsId.t * Cps.Type.t
        | NonThunk of Label.t * Cps.Type.t
        | NonResults of CpsId.t * Cps.Type.t
        | NonClosure of CpsId.t * Cps.Type.t
        | Unbound of CpsId.t
        | UnboundLabel of Label.t
        | OutboundsParam of Label.t * int
        | OutboundsResult of CpsId.t * Cps.Type.t * int
        | OutboundsClover of CpsId.t * int
        | Argc of int * int
        | ArgcT of int * int

    val errorToDoc =
        fn Inequal (t, t') => Type.toDoc t <+> text "!=" <+> Type.toDoc t'
         | UnGoable (label, t) =>
            text "Ungoable:" <+> Label.toDoc label <+> text ":" <+> Type.toDoc t
         | UnCallable (def, t) =>
            text "Uncallable:" <+> CpsId.toDoc def <+> text ":" <+> Type.toDoc t
         | NonClosure (def, t) =>
            text "Non-closure:" <+> CpsId.toDoc def <+> text ":" <+> Type.toDoc t
         | Unbound def => text "Unbound def" <+> CpsId.toDoc def
         | UnboundLabel label => text "Unbound label" <+> Label.toDoc label
         | OutboundsParam (label, i) => text "Out of bounds param" <+> Label.toDoc label <+> PPrint.int i
         | OutboundsResult (def, t, i) => text "Out of bounds result" <+> CpsId.toDoc def <+> PPrint.int i
         | OutboundsClover (def, i) => text "Out of bounds clover" <+> CpsId.toDoc def <+> PPrint.int i
         | Argc (expected, actual) =>
            text "Expected" <+> PPrint.int expected <+> text "arguments,"
            <+> text "got" <+> PPrint.int actual
         | ArgcT (expected, actual) =>
            text "Expected" <+> PPrint.int expected <+> text "type arguments,"
            <+> text "got" <+> PPrint.int actual

    exception TypeError of error

    fun kindOf program =
        fn FnT _ | Closure _ | AnyClosure _ | Prim _ => Kind.TypeK

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
         | ClosureNew (label, clovers) =>
            (case checkCont program label
             of FnT {tDomain, vDomain} => (* HACK?: Avoid need for subtyping by AnyClosure instead of Closure: *)
                 AnyClosure { tDomain
                            , vDomain = VectorSlice.vector (VectorSlice.slice (vDomain, 0, SOME (Vector.length vDomain - 1))) }
              | _ => raise Fail "unreachable")
         | ClosureFn def =>
            (case defType program def
             of Closure {tDomain, vDomain, clovers = _} | AnyClosure {tDomain, vDomain} =>
                 FnT {tDomain, vDomain = Vector.append (vDomain, Singleton def)}
              | t => raise TypeError (NonClosure (def, t)))
         | Clover (def, i) =>
            (case defType program def
             of Closure {clovers, ...} =>
                 if i < Vector.length clovers
                 then Vector.sub (clovers, i)
                 else raise TypeError (OutboundsClover (def, i))
              | t => raise TypeError (NonClosure (def, t)))
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
        case t
        of Singleton def' => 
            if def = def'
            then ()
            else raise TypeError (Inequal (defType program def, t))
         | _ =>
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
        ; case checkCont program target
          of FnT {tDomain = #[], vDomain = #[]} => ()
           | targetTyp => raise TypeError (NonThunk (target, targetTyp)) )

    and checkTransfer (program : Program.t) =
        fn Goto {callee, tArgs, vArgs} =>
            (case labelType program callee
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
              | t => raise TypeError (UnGoable (callee, t)))
         | Jump {callee, tArgs, vArgs} =>
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
         | Return (domain, args) =>
            if Vector.length args = Vector.length domain
            then Vector.zip (domain, args) |> Vector.app (checkDef program)
            else raise TypeError (Argc (Vector.length domain, Vector.length args))

    and labelType (program : Program.t) label =
        case LabelMap.find (#conts program) label
        of SOME {name = _, cconv = _, tParams, vParams, body = _} => FnT {tDomain = tParams, vDomain = vParams}
         | NONE => raise TypeError (UnboundLabel label)

    and checkCont (program : Program.t) label =
        case LabelMap.find (#conts program) label
        of SOME {name = _, cconv = _, tParams, vParams, body} =>
            ( checkTransfer program body
            ; FnT {tDomain = tParams, vDomain = vParams} )
         | NONE => raise TypeError (UnboundLabel label)
    
    fun checkProgram (program as {typeFns, main, ...} : Program.t) =
        ( checkCont program main
        ; Either.Right () )
        handle TypeError err => Either.Left err
end

