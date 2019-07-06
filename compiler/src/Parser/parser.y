structure Term = Cst.Term
structure Type = Cst.Type

type expr = Term.expr
type stmt = Term.stmt

type typ = Type.typ
type decl = Name.t * Type.typ

%%

%name Broom

%pos Pos.t

%term INT of int | BOOL of bool | ID of string
    | VAL | TYPE | DO | FN | LET | IN | END | IF | THEN | ELSE
    | MODULE | INTERFACE | FUN
    | LPAREN | RPAREN | LBRACE | RBRACE
    | EQ | DARROW | COLON | ARROW | DDOT | DOT | COMMA
    | AMP
    | EOF
%nonterm stmts of stmt vector
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

(* Statements *)

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Term.Val (VALleft, Name.fromString ID, NONE, expr))
     | VAL ID COLON typ EQ expr (Term.Val (VALleft, Name.fromString ID, SOME typ, expr))
     | TYPE ID EQ typ (Term.Val (TYPEleft, Name.fromString ID, NONE, Term.Type (typleft, typ)))
     | DO expr (Term.Expr expr)

(* Expressions *)

expr : FN ID DARROW expr (Term.Fn (FNleft, Name.fromString ID, NONE, expr))
     | FN ID COLON typ DARROW expr (Term.Fn (FNleft, Name.fromString ID, SOME typ, expr))
     | IF expr THEN expr ELSE expr (Term.If (IFleft, expr1, expr2, expr3))
     | body (body)

body : body COLON nestableTyp (Term.Ann (bodyleft, body, nestableTyp))
     | app (app)

app : app nestable (Term.App (appleft, {callee = app, arg = nestable}))
    | nestable (nestable)

nestable : LET stmts IN expr END (Term.Let (exprleft, stmts, expr))
         | record (record)
         | MODULE stmts END (Term.Module (MODULEleft, stmts))
         | nestable DOT ID (Term.Field (nestableleft, nestable, Name.fromString ID))
         | LPAREN TYPE typ RPAREN (Term.Type (typleft, typ))
         | LPAREN expr RPAREN (expr)
         | triv (triv)

record : LBRACE fieldExprs optSplat RBRACE (Term.Record (LBRACEleft, {fields = fieldExprs, ext = optSplat}))

fieldExprs : fieldExprList (Vector.fromList (List.rev fieldExprList) (* OPTIMIZE *))

fieldExprList : ([])
              | fieldExpr ([fieldExpr])
              | fieldExprList COMMA fieldExpr (fieldExpr :: fieldExprList)

fieldExpr : ID ((Name.fromString ID, Term.Use (IDleft, Name.fromString ID)))
          | ID EQ expr ((Name.fromString ID, expr))

optSplat : (NONE)
         | DDOT expr (SOME expr)

triv : BOOL (Term.Const (BOOLleft, Const.Bool BOOL))
     | ID (Term.Use (IDleft, Name.fromString ID))
     | INT (Term.Const (INTleft, Const.Int INT))

(* Types *)

typ : FUN ID COLON nestableTyp ARROW arrowTyp
       (Type.Pi (FUNleft, {var = Name.fromString ID, typ = SOME nestableTyp}, arrowTyp))
    | FUN ID ARROW arrowTyp
       (Type.Pi (FUNleft, {var = Name.fromString ID, typ = NONE}, arrowTyp))
    | arrowTyp (arrowTyp)

arrowTyp : nonArrowTyp ARROW typ
            (Type.Pi (typleft, {var = Name.fresh (), typ = SOME nonArrowTyp}, typ))
         | nonArrowTyp (nonArrowTyp)

nonArrowTyp : purelyTyp (purelyTyp)
            | LPAREN typ RPAREN (typ)
            | expr (case expr
                    of Term.Use (_, name) => (case Name.toString name
                                              of "Int" => Type.Prim (exprleft, Type.Prim.I32)
                                               | "Unit" => Type.Prim (exprleft, Type.Prim.Unit)
                                               | _ => Type.Path expr)
                    | _ => Type.Path expr)

nestableTyp : purelyTyp (purelyTyp)
            | LPAREN typ RPAREN (typ)
            | nestable (case nestable
                        of Term.Use (_, name) => (case Name.toString name
                                                  of "Int" => Type.Prim (nestableleft, Type.Prim.I32)
                                                   | "Unit" => Type.Prim (nestableleft, Type.Prim.Unit)
                                                   | _ => Type.Path nestable)
                        | _ => Type.Path nestable)

purelyTyp : TYPE (Type.TypeT TYPEleft)
          | LBRACE rowType RBRACE (Type.RecordT (LBRACEleft, rowType))
          | LPAREN EQ expr RPAREN (Type.Singleton (LPARENleft, expr))
          | INTERFACE decls END (Type.Interface (INTERFACEleft, decls))

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

decls : declList (Vector.fromList (List.rev declList))

declList : ([])
         | declList decl (decl :: declList)

decl : VAL ID COLON typ ((Name.fromString ID, typ))
     | TYPE ID ((Name.fromString ID, Type.TypeT TYPEleft))
     | TYPE ID EQ typ
        ((Name.fromString ID, Type.Singleton (TYPEleft, Term.Type (TYPEleft, typ))))

