structure Term = FixedCst.Term
structure Type = FixedCst.Type

type stmt = Term.stmt
type expr = Term.expr

%%

%name Broom

%pos Pos.t

%term INT of int | ID of string
    | VAL | TYPE | FN | FORALL | LET | IN | END
    | LPAREN | RPAREN
    | EQ | DARROW | COLON | ARROW | DOT
    | EOF
%nonterm program of expr
       | stmts of stmt vector
       | stmtList of stmt list
       | stmt of stmt
       | expr of expr
       | app of expr
       | nestable of expr
       | triv of expr
       | typeAnn of Type.typ
       | typeAnnBody of Type.typ
       | ids of Type.def list

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
     | app (app)

app : app nestable (Term.Fix (Term.App (appleft, {callee = app, arg = nestable})))
    | nestable (nestable)

nestable : LPAREN expr RPAREN (expr)
         | triv (triv)

triv : ID  (Term.Fix (Term.Use (IDleft, Name.fromString ID)))
     | INT (Term.Fix (Term.Const (INTleft, Const.Int INT)))

typeAnn : LPAREN typeAnn RPAREN (typeAnn)
        | typeAnn ARROW typeAnn (Type.FixT (Type.Arrow (typeAnnleft, {domain = typeAnn1, codomain = typeAnn})))
        | LPAREN EQ expr RPAREN (Type.FixT (Type.Singleton (LPARENleft, expr)))
        | expr (Type.FixT (case expr
                           of Term.Fix (Term.Use (_, name)) => (case Name.toString name
                                                                of "Int" => Type.Prim (exprleft, Type.I32)
                                                                 | _ => Type.Path expr)
                            | _ => Type.Path expr))

