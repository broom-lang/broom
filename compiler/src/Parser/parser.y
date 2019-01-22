structure Term = FixedCst.Term
structure Type = FixedCst.Type

type stmt = Term.stmt
type expr = Term.expr

fun lookup "bogus" = 10000
  | lookup s = 0

%%

%name Broom

%pos Pos.t

%term INT of int | ID of string
    | VAL | FN | FORALL | LET | IN | END
    | LPAREN | RPAREN
    | EQ | DARROW | COLON | ARROW | DOT
    | EOF
%nonterm program of stmt vector
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

program : stmts (stmts)

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Term.Val (VALleft, Name.fromString ID, NONE, expr))
     | VAL ID COLON typeAnn EQ expr (Term.Val (VALleft, Name.fromString ID, SOME typeAnn, expr))

expr : FN ID DARROW expr (Term.Fix (Term.Fn (FNleft, Name.fromString ID, NONE, expr)))
     | FN ID COLON typeAnn DARROW expr (Term.Fix (Term.Fn ( FNleft, Name.fromString ID, SOME typeAnn, expr)))
     | LET stmts IN expr END (Term.Fix (Term.Let (exprleft, stmts, expr)))
     | expr COLON typeAnn (Term.Fix (Term.Ann (exprleft, expr, typeAnn)))
     | app (app)

app : app nestable (Term.Fix (Term.App (appleft, {callee = app, arg = nestable})))
    | nestable (nestable)

nestable : LPAREN expr RPAREN (expr)
         | triv (triv)

triv : ID  (Term.Fix (Term.Use (IDleft, Name.fromString ID)))
     | INT (Term.Fix (Term.Const (INTleft, Const.Int INT)))

typeAnn : FORALL ids DOT typeAnnBody (List.foldl (fn (id, t) => Type.Fix (Type.ForAll (FORALLleft, id, t)))
                                                 typeAnnBody ids)
        | typeAnnBody (typeAnnBody)

typeAnnBody : LPAREN typeAnn RPAREN (typeAnn)
            | typeAnnBody ARROW typeAnnBody (Type.Fix (Type.Arrow ( typeAnnBody1left
                                                                  , { domain = typeAnnBody1
                                                                    , codomain = typeAnnBody2 })))
            | ID (Type.Fix (case ID
                            of "Int" => Type.Prim (IDleft, Type.I32)
                             | _ => Type.UseT (IDleft, {var = Name.fromString ID, kind = Type.TypeK IDleft})))

ids : ids ID ({var = Name.fromString ID, kind = Type.TypeK IDleft} :: ids)
    | ID ([{var = Name.fromString ID, kind = Type.TypeK IDleft}])
