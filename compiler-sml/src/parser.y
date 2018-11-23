type stmt = Cst.stmt
type expr = Cst.expr

fun lookup "bogus" = 10000
  | lookup s = 0

%%

%name Broom

%pos Pos.t

%term INT of int | ID of string | LPAREN | RPAREN | VAL | FN | EQ | DARROW | EOF
%nonterm program of stmt vector
       | stmts of stmt vector
       | stmtList of stmt list
       | stmt of stmt
       | expr of expr
       | app of expr
       | nestable of expr
       | triv of expr

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
     | app (app)

app : app nestable (Cst.App (appleft, {callee = app, arg = nestable}))
    | nestable (nestable)

nestable : LPAREN expr RPAREN (expr)
         | triv (triv)

triv : ID  (Cst.Use (IDleft, Name.fromString ID))
     | INT (Cst.Const (INTleft, Const.Int INT))
