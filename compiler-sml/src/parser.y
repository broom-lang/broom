type stmt = Cst.stmt
type expr = Cst.expr

fun lookup "bogus" = 10000
  | lookup s = 0

%%

%name Broom

%pos Pos.t

%term INT of int | ID of string | VAL | EQ | EOF
%nonterm program of stmt vector
       | stmts of stmt vector
       | stmtList of stmt list
       | stmt of stmt
       | expr of expr

%keyword VAL EQ
%noshift EOF
%eop EOF

%%

program : stmts (stmts)

stmts : stmtList (Vector.fromList (List.rev stmtList) (* OPTIMIZE *))

stmtList : ([])
         | stmtList stmt (stmt :: stmtList)

stmt : VAL ID EQ expr (Cst.Def (VALleft, Name.fromString ID, expr))

expr : INT (Cst.Const (INTleft, Const.Int INT))
