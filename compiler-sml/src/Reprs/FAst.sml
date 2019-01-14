signature FTYPE = sig
    type kind
    type t
    type def

    val kindToString: kind -> string
    val defToString: def -> string
    val toString: t -> string
end

signature FAST_TYPE = sig
    datatype prim = datatype Type.prim

    datatype kind = TypeK
                  | ArrowK of Pos.t * {domain: kind, codomain: kind}

    and t = ForAll of Pos.t * def * t
          | UseT of Pos.t * def
          | Arrow of Pos.t * {domain: t, codomain: t}
          | Prim of Pos.t * prim

    withtype def = {name: Name.t, kind: kind}

    val kindToString: kind -> string
    val defToString: def -> string
    val toString: t -> string

    val kindEq: kind * kind -> bool
    val eq: t * t -> bool
end

signature FAST_TERM = sig
    structure Type: FTYPE

    datatype expr = Fn of Pos.t * def * expr
                  | TFn of Pos.t * Type.def * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | TApp of Pos.t * {callee: expr, arg: Type.t}
                  | Let of Pos.t * stmt vector * expr
                  | Use of Pos.t * def
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * def * expr

    withtype def = {name: Name.t, typ: Type.t}

    val exprPos: expr -> Pos.t
    val stmtPos: stmt -> Pos.t

    val defToString: def -> string
    val exprToString: expr -> string
    val stmtToString: stmt -> string
end

structure FType :> FAST_TYPE = struct
    datatype prim = datatype Type.prim

    datatype kind = TypeK
                  | ArrowK of Pos.t * {domain: kind, codomain: kind}

    and t = ForAll of Pos.t * def * t
          | UseT of Pos.t * def
          | Arrow of Pos.t * {domain: t, codomain: t}
          | Prim of Pos.t * prim

    withtype def = {name: Name.t, kind: kind}

    val primEq = fn (Int, Int) => true

    val rec kindEq =
        fn (TypeK, TypeK) => true
         | ( ArrowK (_, {domain, codomain})
           , ArrowK (_, {domain = domain', codomain = codomain'}) ) =>
            kindEq (domain, domain') andalso kindEq (codomain, codomain')
         | _ => false

    fun eq args =
        let fun canonicalName names name = getOpt (NameSortedMap.find (names, name), name)
            fun eq' names =
                    fn ( ForAll (_, {name, kind}, body)
                       , ForAll (_, {name = name', kind = kind'}, body') ) =>
                        kindEq (kind, kind')
                        andalso eq' (NameSortedMap.insert (names, name', name))
                                    (body, body')
                     | (UseT (_, {name, kind}), UseT (_, {name = name', kind = kind'})) =>
                        kindEq (kind, kind')
                        andalso (canonicalName names name = canonicalName names name')
                     | ( Arrow (_, {domain, codomain})
                       , Arrow (_, {domain = domain', codomain = codomain'}) ) =>
                        eq' names (domain, domain') andalso eq' names (codomain, codomain')
                     | (Prim (_, p), Prim (_, p')) => primEq (p, p')
                     | _ => false
        in eq' NameSortedMap.empty args
        end

    val rec kindToString =
        fn TypeK => "Type"
         | ArrowK (_, {domain, codomain}) =>
            kindToString domain ^ " -> " ^ kindToString codomain

    fun defToString {name, kind} = Name.toString name ^ ": " ^ kindToString kind

    val rec toString =
        fn ForAll (_, def, body) => "\\/ " ^ defToString def ^ " . " ^ toString body
         | UseT (_, {name, ...}) => Name.toString name
         | Arrow (_, {domain, codomain}) => toString domain ^ " -> " ^ toString codomain
         | Prim (_, p) => Type.primToString p
end

functor FTerm (Type: FTYPE) :> FAST_TERM where
    type Type.kind = Type.kind and
    type Type.t = Type.t and
    type Type.def = Type.def
= struct
    structure Type = Type

    datatype expr = Fn of Pos.t * def * expr
                  | TFn of Pos.t * Type.def * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | TApp of Pos.t * {callee: expr, arg: Type.t}
                  | Let of Pos.t * stmt vector * expr
                  | Use of Pos.t * def
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * def * expr

    withtype def = {name: Name.t, typ: Type.t}

    val exprPos = fn Fn (pos, _, _) => pos
                   | TFn (pos, _, _) => pos
                   | App (pos, _) => pos
                   | TApp (pos, _) => pos
                   | Let (pos, _, _) => pos
                   | Use (pos, _) => pos
                   | Const (pos, _) => pos

    val stmtPos = fn Def (pos, _, _) => pos

    fun defToString {name, typ} = Name.toString name ^ ": " ^ Type.toString typ

    val rec exprToString =
        fn Fn (_, param, body) =>
            "\\" ^ defToString param ^ " => " ^ exprToString body
         | TFn (_, param, body) =>
            "/\\" ^ Type.defToString param ^ " => " ^ exprToString body
         | App (_, {callee, arg}) =>
            "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
         | TApp (_, {callee, arg}) =>
            "(" ^ exprToString callee ^ " [" ^ Type.toString arg ^ "])" 
         | Let (_, stmts, body) =>
           let fun step (stmt, acc) = acc ^ stmtToString stmt ^ "\n"
           in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                  "    " ^ exprToString body ^ "\nend"
           end
         | Use (_, {name, ...}) => Name.toString name
         | Const (_, c) => Const.toString c

    and stmtToString =
        fn Def (_, def, valExpr) => "val " ^ defToString def ^ " = " ^ exprToString valExpr
end

structure SemiFAst :> sig
    structure Type: TYPE where
        type t = Type.t

    structure Term: FAST_TERM where
        type Type.kind = Type.kind and
        type Type.t = Type.t and
        type Type.def = Type.def
end = struct
    structure Type = Type

    structure Term = FTerm(Type)
end

structure FAst :> sig
    structure Type: FAST_TYPE

    structure Term: FAST_TERM where
        type Type.kind = Type.kind and
        type Type.t = Type.t and
        type Type.def = Type.def
end = struct
    structure Type = FType

    structure Term = FTerm(Type)
end
