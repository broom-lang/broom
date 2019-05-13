structure Term = FixedCst.Term
structure Type = FixedCst.Type

type expr = (Type.ftyp option, Term.fexpr) Term.expr
type stmt = Term.stmt

type typ = expr Type.typ

%%

%name Broom

%pos Pos.t

%term INT of int | ID of string
    | VAL | TYPE | FN | LET | IN | END
    | LPAREN | RPAREN | LBRACE | RBRACE
    | EQ | DARROW | COLON | ARROW | DOT | COMMA
    | EOF
%nonterm program of expr
       | stmts of stmt vector
       | stmtList of stmt list
       | stmt of stmt
       | expr of expr
       | app of expr
       | nestable of expr
       | rowExpr of (Name.t * expr) vector
       | rowExprList of (Name.t * expr) list
       | triv of expr
       | typeAnn of typ
       | rowType of typ

%keyword VAL EQ
%noshift EOF
%eop EOF

%%

program : stmts (Term.Let (stmtsleft, stmts, Term.Const (stmtsright, Const.Int 0)))

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Term.Val (VALleft, Name.fromString ID, NONE, Term.Fix expr))
     | VAL ID COLON typeAnn EQ expr (Term.Val (VALleft, Name.fromString ID, SOME (Type.FixT typeAnn), Term.Fix expr))
     | TYPE ID EQ typeAnn (Term.Val ( TYPEleft, Name.fromString ID, NONE
                                    , Term.Fix (Term.Type (typeAnnleft, typeAnn)) ))

expr : FN ID DARROW expr (Term.Fn (FNleft, Name.fromString ID, NONE, expr))
     | FN ID COLON typeAnn DARROW expr (Term.Fn ( FNleft, Name.fromString ID, SOME (Type.FixT typeAnn), expr))
     | LET stmts IN expr END (Term.Let (exprleft, stmts, expr))
     | expr COLON typeAnn (Term.Ann (exprleft, expr, typeAnn))
     | TYPE typeAnn (Term.Type (typeAnnleft, typeAnn))
     | expr DOT ID (Term.Field (exprleft, expr, Name.fromString ID))
     | app (app)

app : app nestable (Term.App (appleft, {callee = app, arg = nestable}))
    | nestable (nestable)

nestable : LPAREN expr RPAREN (expr)
         | LBRACE rowExpr RBRACE (Term.Record (LBRACEleft, rowExpr))
         | triv (triv)

rowExpr : rowExprList (Vector.fromList (List.rev rowExprList) (* OPTIMIZE *))

rowExprList : ([])
            | ID EQ expr ([(Name.fromString ID, expr)])
            | rowExprList COMMA ID EQ expr ((Name.fromString ID, expr) :: rowExprList)

triv : ID  (Term.Use (IDleft, Name.fromString ID))
     | INT (Term.Const (INTleft, Const.Int INT))

typeAnn : LPAREN typeAnn RPAREN (typeAnn)
        | typeAnn ARROW typeAnn (Type.Arrow (typeAnnleft, {domain = typeAnn1, codomain = typeAnn}))
        | LBRACE rowType RBRACE (Type.Record (LBRACEleft, rowType))
        | LBRACE RBRACE (Type.Record (LBRACEleft, Type.EmptyRow LBRACEleft))
        | LPAREN EQ expr RPAREN (Type.Singleton (LPARENleft, expr))
        | expr (case expr
                of Term.Use (_, name) => (case Name.toString name
                                          of "Int" => Type.Prim (exprleft, Type.Prim.I32)
                                           | _ => Type.Path expr)
                 | _ => Type.Path expr)

rowType: ID COLON typeAnn (Type.RowExt (IDleft, { field = (Name.fromString ID, typeAnn)
                                                , ext = Type.EmptyRow typeAnnright }))
       | ID COLON typeAnn COMMA rowType (Type.RowExt (IDleft, { field = (Name.fromString ID, typeAnn)
                                                              , ext = rowType }))

