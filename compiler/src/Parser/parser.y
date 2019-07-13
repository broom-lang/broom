structure Term = Cst.Term
structure Type = Cst.Type

type expr = Term.expr
type stmt = Term.stmt

type typ = Type.typ
type decl = Name.t * Type.typ

%%

%name Broom

%verbose

%pos Pos.t

%term INT of int | BOOL of bool | ID of string
    | VAL | TYPE | DO | FN | LET | IN | END | IF | THEN | ELSE
    | MODULE | INTERFACE | FUN
    | LPAREN | RPAREN | LBRACE | RBRACE
    | EQ | DARROW | COLON | ARROW | BAR | DDOT | DOT | COMMA | SEMICOLON
    | AMP
    | EOF
%nonterm program of stmt vector
       | stmts of stmt vector
       | stmtList of stmt list
       | stmt of stmt
       | blockStmts of stmt list * expr
       | ascription of expr
       | params of (Name.t * typ option) list
       | param of Name.t * typ option
       | body of expr
       | binapp of expr
       | app of expr
       | nestable of expr
       | purelyExpr of expr
       | record of expr
       | fieldExprs of (Name.t * expr) vector
       | fieldExprList of (Name.t * expr) list
       | fieldExpr of (Name.t * expr)
       | optSplat of expr option
       | triv of expr
       | typ of typ
       | bodyTyp of typ
       | binTyp of typ
       | appTyp of typ
       | paramType of typ
       | arrowTyp of typ
       | nonArrowTyp of typ
       | nestableTyp of typ
       | purelyTyp of typ
       | rowType of typ
       | rowFields of (Name.t * typ) vector
       | rowFieldList of (Name.t * typ) list
       | rowExt of typ
       | decls of decl vector
       | declList of decl list
       | decl of decl
       | pattern of Name.t * typ option
       | paramPattern of Name.t * typ option

%keyword VAL EQ
%noshift EOF
%eop EOF

%%

program : stmts (stmts)

(* # Statements *)

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : pattern EQ ascription SEMICOLON (Term.Val (patternleft, #1 pattern, #2 pattern, ascription))
     | TYPE ID EQ typ SEMICOLON (Term.Val (TYPEleft, Name.fromString ID, NONE, Term.Type (typleft, typ)))
     | ascription SEMICOLON (Term.Expr ascription)

blockStmts : stmt SEMICOLON blockStmts
               (let val (stmts, expr) = blockStmts
                in (stmt :: stmts, expr)
                end)
           | ascription (([], ascription))

(* # Expressions *)

ascription : ascription COLON typ (Term.Ann (ascriptionleft, ascription, typ))
           | body (body)

body : IF ascription THEN ascription ELSE ascription (Term.If (IFleft, ascription1, ascription2, ascription3))
     | binapp (binapp)

binapp : app (app)

app : app nestable (Term.App (appleft, {callee = app, arg = nestable}))
    | nestable (nestable)

nestable : purelyExpr (purelyExpr)
         | purelyTyp (Term.Type (purelyTypleft, purelyTyp))
         | LPAREN ascription RPAREN (ascription)

purelyExpr
    : LBRACE BAR params ascription RBRACE
        (List.foldl (fn ((param, domain), expr) => Term.Fn (LBRACEleft, param, domain, expr))
                    ascription params)
    | DO blockStmts END (let val (stmts, expr) = blockStmts
                             in Term.Let (DOleft, Vector.fromList stmts, expr)
                             end)
    | record (record)
    | MODULE stmts END (Term.Module (MODULEleft, stmts))
    | purelyExpr DOT ID (Term.Field (purelyExprleft, purelyExpr, Name.fromString ID))
    | triv (triv)

params : params param (param :: params)
       | param ([param])

param : paramPattern ARROW (paramPattern)

triv : BOOL (Term.Const (BOOLleft, Const.Bool BOOL))
     | ID (case ID (* HACK *)
           of "Int" => Term.Type (IDleft, Type.Prim (IDleft, Type.Prim.I32))
            | "Bool" => Term.Type (IDleft, Type.Prim (IDleft, Type.Prim.Bool))
            | "Unit" => Term.Type (IDleft, Type.Prim (IDleft, Type.Prim.Unit))
            | _ => Term.Use (IDleft, Name.fromString ID))
     | INT (Term.Const (INTleft, Const.Int INT))

(* ## Record fields *)

record : LBRACE fieldExprs optSplat RBRACE (Term.Record (LBRACEleft, {fields = fieldExprs, ext = optSplat}))

fieldExprs : fieldExprList (Vector.fromList (List.rev fieldExprList) (* OPTIMIZE *))

fieldExprList : ([])
              | fieldExpr ([fieldExpr])
              | fieldExprList COMMA fieldExpr (fieldExpr :: fieldExprList)

fieldExpr : ID ((Name.fromString ID, Term.Use (IDleft, Name.fromString ID)))
          | ID EQ ascription ((Name.fromString ID, ascription))

optSplat : (NONE)
         | DDOT ascription (SOME ascription)

(* # Types *)

typ : FUN paramPattern ARROW typ
       (Type.Pi (FUNleft, {var = #1 paramPattern, typ = #2 paramPattern}, typ))
    | bodyTyp ARROW typ
       (Type.Pi (bodyTypleft, {var = Name.fresh (), typ = SOME bodyTyp}, typ))
    | bodyTyp (bodyTyp)

bodyTyp : IF typ THEN typ ELSE typ (raise Fail "unimplemented")
        | binTyp (binTyp)

binTyp : appTyp (appTyp)

appTyp : appTyp nestableTyp
           (Type.Path (Term.App (appTypleft, { callee = Term.Type (appTypleft, appTyp)
                                             , arg = Term.Type (nestableTypleft, nestableTyp) })))
       | nestableTyp (nestableTyp)

nestableTyp
    : purelyExpr (Type.Path purelyExpr)
    | purelyTyp (purelyTyp)
    | LPAREN typ RPAREN (typ)
    | LPAREN typ COLON typ RPAREN (raise Fail "unimplemented")

purelyTyp : TYPE (Type.TypeT TYPEleft)
          | LBRACE rowType RBRACE (Type.RecordT (LBRACEleft, rowType))
          | LPAREN EQ ascription RPAREN (Type.Singleton (LPARENleft, ascription))
          | INTERFACE decls END (Type.Interface (INTERFACEleft, decls))

(* ## Rows *)

rowType: COLON (Type.EmptyRow COLONleft)
       | rowFields (Type.RowExt (rowFieldsleft, { fields = rowFields
                                                , ext = Type.EmptyRow rowFieldsright }))
       | rowExt (Type.RowExt (rowExtleft, {fields = Vector.fromList [], ext = rowExt}))
       | rowFields rowExt (Type.RowExt (rowFieldsleft, {fields = rowFields, ext = rowExt}))

rowFields : rowFieldList (Vector.fromList (List.rev rowFieldList) (* OPTIMIZE *))

rowFieldList : ID COLON typ ([(Name.fromString ID, typ)])
             | ID COLON typ COMMA rowFieldList ((Name.fromString ID, typ) :: rowFieldList)

rowExt : AMP (Type.WildRow AMPleft)
       | AMP typ (typ)

(* ## Declarations *)

decls : declList (Vector.fromList (List.rev declList))

declList : ([])
         | declList decl (decl :: declList)

decl : ID COLON typ SEMICOLON ((Name.fromString ID, typ))
     | TYPE ID SEMICOLON ((Name.fromString ID, Type.TypeT TYPEleft))
     | TYPE ID EQ typ SEMICOLON
        ((Name.fromString ID, Type.Singleton (TYPEleft, Term.Type (TYPEleft, typ))))

(* # Patterns *)

pattern : ID ((Name.fromString ID, NONE))
        | ID COLON typ ((Name.fromString ID, SOME typ))

paramPattern : ID ((Name.fromString ID, NONE))
             | ID COLON bodyTyp ((Name.fromString ID, SOME bodyTyp))

