structure Term = FixedCst.Term
structure Type = FixedCst.Type

type expr = Term.fexpr
type stmt = Term.stmt

type typ = Type.ftyp

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

program : stmts (Term.Fix (Term.Let (stmtsleft, stmts, Term.Fix (Term.Const (stmtsright, Const.Int 0)))))

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Term.Val (VALleft, Name.fromString ID, NONE, expr))
     | VAL ID COLON typeAnn EQ expr (Term.Val (VALleft, Name.fromString ID, SOME typeAnn, expr))
     | TYPE ID EQ typeAnn (Term.Val ( TYPEleft, Name.fromString ID, NONE
                                    , Term.Fix (Term.Type (typeAnnleft, typeAnn)) ))

expr : FN ID DARROW expr (Term.Fix (Term.Fn (FNleft, Name.fromString ID, NONE, expr)))
     | FN ID COLON typeAnn DARROW expr (Term.Fix (Term.Fn ( FNleft, Name.fromString ID, SOME typeAnn, expr)))
     | LET stmts IN expr END (Term.Fix (Term.Let (exprleft, stmts, expr)))
     | expr COLON typeAnn (Term.Fix (Term.Ann (exprleft, expr, typeAnn)))
     | TYPE typeAnn (Term.Fix (Term.Type (typeAnnleft, typeAnn)))
     | expr DOT ID (Term.Fix (Term.Field (exprleft, expr, Name.fromString ID)))
     | app (app)

app : app nestable (Term.Fix (Term.App (appleft, {callee = app, arg = nestable})))
    | nestable (nestable)

nestable : LPAREN expr RPAREN (expr)
         | LBRACE rowExpr RBRACE (Term.Fix (Term.Record (LBRACEleft, rowExpr)))
         | triv (triv)

rowExpr : rowExprList (Vector.fromList (List.rev rowExprList) (* OPTIMIZE *))

rowExprList : ([])
            | ID EQ expr ([(Name.fromString ID, expr)])
            | rowExprList COMMA ID EQ expr ((Name.fromString ID, expr) :: rowExprList)

triv : ID  (Term.Fix (Term.Use (IDleft, Name.fromString ID)))
     | INT (Term.Fix (Term.Const (INTleft, Const.Int INT)))

typeAnn : LPAREN typeAnn RPAREN (typeAnn)
        | typeAnn ARROW typeAnn (Type.FixT (Type.Arrow (typeAnnleft, {domain = typeAnn1, codomain = typeAnn})))
        | LBRACE rowType RBRACE (Type.FixT (Type.Record (LBRACEleft, rowType)))
        | LBRACE RBRACE (Type.FixT (Type.Record (LBRACEleft, Type.FixT (Type.EmptyRow LBRACEleft))))
        | LPAREN EQ expr RPAREN (Type.FixT (Type.Singleton (LPARENleft, expr)))
        | expr (Type.FixT (case expr
                of Term.Fix (Term.Use (_, name)) => (case Name.toString name
                                          of "Int" => Type.Prim (exprleft, Type.Prim.I32)
                                           | _ => Type.Path expr)
                 | _ => Type.Path expr))

rowType: ID COLON typeAnn (Type.FixT (Type.RowExt (IDleft, { field = (Name.fromString ID, typeAnn)
                                                , ext = Type.FixT (Type.EmptyRow typeAnnright) })))
       | ID COLON typeAnn COMMA rowType (Type.FixT (Type.RowExt (IDleft, { field = (Name.fromString ID, typeAnn)
                                                              , ext = rowType })))

