type stmt = Cst.stmt
type expr = Cst.expr
type type_ann = Cst.type_ann

fun lookup "bogus" = 10000
  | lookup s = 0

%%

%name Broom

%pos Pos.t

%term INT of int | ID of string
    | VAL | FN | FORALL
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
       | typeAnn of type_ann
       | ids of Name.t list

%keyword VAL EQ
%noshift EOF
%eop EOF

%%

program : stmts (stmts)

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Cst.Def (VALleft, Name.fromString ID, expr))

expr : FN ID DARROW expr (Cst.Fn (FNleft, Name.fromString ID, expr))
     | expr COLON typeAnn (Cst.Ann (exprleft, expr, typeAnn))
     | app (app)

app : app nestable (Cst.App (appleft, {callee = app, arg = nestable}))
    | nestable (nestable)

nestable : LPAREN expr RPAREN (expr)
         | triv (triv)

triv : ID  (Cst.Use (IDleft, Name.fromString ID))
     | INT (Cst.Const (INTleft, Const.Int INT))

typeAnn : FORALL ids DOT typeAnn (List.foldl (fn (id, t) => Cst.ForAll (FORALLleft, id, t))
                                             typeAnn ids)
        | typeAnn ARROW typeAnn (Cst.Arrow (typeAnn1left, { domain = typeAnn1
                                                          , codomain = typeAnn2 }))
        | ID (case ID
              of "Int" => Cst.Prim (IDleft, Type.Int)
               | _ => Cst.UseT (IDleft, Name.fromString ID))

ids : ids ID (Name.fromString ID :: ids)
    | ID ([Name.fromString ID])
