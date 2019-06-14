structure Term = FixedCst.Term
structure Type = FixedCst.Type

type expr = Term.fexpr
type stmt = Term.stmt

type typ = Type.ftyp
type decl = Type.decl

%%

%name Broom

%pos Pos.t

%term INT of int | BOOL of bool | ID of string
    | VAL | TYPE | FN | LET | IN | END | IF | THEN | ELSE
    | MODULE | INTERFACE | FUN
    | LPAREN | RPAREN | LBRACE | RBRACE
    | EQ | DARROW | COLON | ARROW | DDOT | DOT | COMMA
    | AMP
    | EOF
%nonterm program of expr
       | stmts of stmt vector
       | stmtList of stmt list
       | stmt of stmt
       | expr of expr
       | body of expr
       | app of expr
       | nestable of expr
       | record of expr
       | fieldExprs of (Name.t * expr) vector
       | fieldExprList of (Name.t * expr) list
       | fieldExpr of (Name.t * expr)
       | optSplat of expr option
       | triv of expr
       | typ of typ
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

%keyword VAL EQ
%noshift EOF
%eop EOF

%%

program : stmts (Term.Fix (Term.Let (stmtsleft, stmts, Term.Fix (Term.Const (stmtsright, Const.Int 0)))))

(* Statements *)

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Term.Val (VALleft, Name.fromString ID, NONE, expr))
     | VAL ID COLON typ EQ expr (Term.Val (VALleft, Name.fromString ID, SOME typ, expr))
     | TYPE ID EQ typ (Term.Val ( TYPEleft, Name.fromString ID, NONE
                                , Term.Fix (Term.Type (typleft, typ)) ))

(* Expressions *)

expr : FN ID DARROW expr (Term.Fix (Term.Fn (FNleft, Name.fromString ID, NONE, expr)))
     | FN ID COLON typ DARROW expr (Term.Fix (Term.Fn (FNleft, Name.fromString ID, SOME typ, expr)))
     | IF expr THEN expr ELSE expr (Term.Fix (Term.If (IFleft, expr1, expr2, expr3)))
     | body (body)

body : body COLON nestableTyp (Term.Fix (Term.Ann (bodyleft, body, nestableTyp)))
     | app (app)

app : app nestable (Term.Fix (Term.App (appleft, {callee = app, arg = nestable})))
    | nestable (nestable)

nestable : LET stmts IN expr END (Term.Fix (Term.Let (exprleft, stmts, expr)))
         | record (record)
         | MODULE stmts END (Term.Fix (Term.Module (MODULEleft, stmts)))
         | nestable DOT ID (Term.Fix (Term.Field (nestableleft, nestable, Name.fromString ID)))
         | LPAREN TYPE typ RPAREN (Term.Fix (Term.Type (typleft, typ)))
         | LPAREN expr RPAREN (expr)
         | triv (triv)

record : LBRACE fieldExprs optSplat RBRACE (Term.Fix (Term.Record (LBRACEleft, {fields = fieldExprs, ext = optSplat})))

fieldExprs : fieldExprList (Vector.fromList (List.rev fieldExprList) (* OPTIMIZE *))

fieldExprList : ([])
              | fieldExpr ([fieldExpr])
              | fieldExprList COMMA fieldExpr (fieldExpr :: fieldExprList)

fieldExpr : ID ((Name.fromString ID, Term.Fix (Term.Use (IDleft, Name.fromString ID))))
          | ID EQ expr ((Name.fromString ID, expr))

optSplat : (NONE)
         | DDOT expr (SOME expr)

triv : BOOL (Term.Fix (Term.Const (BOOLleft, Const.Bool BOOL)))
     | ID (Term.Fix (Term.Use (IDleft, Name.fromString ID)))
     | INT (Term.Fix (Term.Const (INTleft, Const.Int INT)))

(* Types *)

typ : FUN ID COLON nestableTyp ARROW arrowTyp
       (Type.FixT (Type.Pi (FUNleft, {var = Name.fromString ID, typ = nestableTyp}, arrowTyp)))
    | FUN ID ARROW arrowTyp
       (Type.FixT (Type.Pi (FUNleft, {var = Name.fromString ID, typ = Type.FixT (Type.Type IDleft)}, arrowTyp)))
    | arrowTyp (arrowTyp)

arrowTyp : nonArrowTyp ARROW typ
            (Type.FixT (Type.Pi (typleft, {var = Name.fresh (), typ = nonArrowTyp}, typ)))
         | nonArrowTyp (nonArrowTyp)

nonArrowTyp : purelyTyp (purelyTyp)
            | LPAREN typ RPAREN (typ)
            | expr (Type.FixT (case expr
                               of Term.Fix (Term.Use (_, name)) => (case Name.toString name
                                                                    of "Int" => Type.Prim (exprleft, Type.Prim.I32)
                                                                     | _ => Type.Path expr)
                                | _ => Type.Path expr)) 

nestableTyp : purelyTyp (purelyTyp)
            | LPAREN typ RPAREN (typ)
            | nestable (Type.FixT (case nestable
                               of Term.Fix (Term.Use (_, name)) => (case Name.toString name
                                                                    of "Int" => Type.Prim (nestableleft, Type.Prim.I32)
                                                                     | _ => Type.Path nestable)
                                | _ => Type.Path nestable)) 

purelyTyp : TYPE (Type.FixT (Type.Type TYPEleft))
          | LBRACE rowType RBRACE (Type.FixT (Type.Record (LBRACEleft, rowType)))
          | LPAREN EQ expr RPAREN (Type.FixT (Type.Singleton (LPARENleft, expr)))
          | INTERFACE decls END (Type.FixT (Type.Interface (INTERFACEleft, decls)))

rowType: COLON (Type.FixT (Type.EmptyRow COLONleft))
       | rowFields (Type.FixT (Type.RowExt (rowFieldsleft, { fields = rowFields
                                                           , ext = Type.FixT (Type.EmptyRow rowFieldsright) })))
       | rowExt (Type.FixT (Type.RowExt (rowExtleft, {fields = Vector.fromList [], ext = rowExt})))
       | rowFields rowExt (Type.FixT (Type.RowExt (rowFieldsleft, {fields = rowFields, ext = rowExt})))

rowFields : rowFieldList (Vector.fromList (List.rev rowFieldList) (* OPTIMIZE *))

rowFieldList : ID COLON typ ([(Name.fromString ID, typ)])
             | ID COLON typ COMMA rowFieldList ((Name.fromString ID, typ) :: rowFieldList)

rowExt : AMP (Type.FixT (Type.WildRow AMPleft))
       | AMP typ (typ)

decls : declList (Vector.fromList (List.rev declList))

declList : ([])
         | declList decl (decl :: declList)

decl : VAL ID COLON typ ((Name.fromString ID, typ))
     | TYPE ID ((Name.fromString ID, Type.FixT (Type.Type TYPEleft)))
     | TYPE ID EQ typ ((Name.fromString ID, Type.FixT (Type.Singleton (TYPEleft, Term.Fix (Term.Type (TYPEleft, typ))))))

