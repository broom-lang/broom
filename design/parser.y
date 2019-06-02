%%

%name Broom

%pos int

%term VAR of string | BINOP of string
    | TYPE
    | LPAREN | RPAREN | LBRACKET | RBRACKET | LBRACE | RBRACE
    | BAR | AMP
    | EQ | DRARROW | DLARROW | DLRARROW
    | DOT | DDOT | COLON | COMMA | SEMICOLON
    | EOF

%nonterm program of unit
       | stmts of unit
       | stmt of unit
       | expr of unit
       | binapp of unit
       | app of unit
       | nestableExpr of unit
       | lambda of unit
       | clauses of unit
       | clause of unit
       | params of unit
       | param of unit
       | block of unit
       | triv of unit
       | pattern of unit
       | typ of unit

%noshift EOF
%eop EOF

%%

program : stmts (())

(* Statements *)

stmts : (())
      | stmts SEMICOLON stmt (())

stmt : pattern EQ expr (())
     | expr (())

(* Expressions *)

expr : expr COLON typ (())
     | binapp (())

binapp : binapp BINOP app (())

app : app nestableExpr (())
    | nestableExpr (())

nestableExpr : lambda (())
             | block (())
             | TYPE typ (())
             | LPAREN BINOP RPAREN (())
             | LPAREN expr RPAREN (())
             | triv (())

lambda : LBRACE clauses RBRACE (())

clauses : clauses clause (())
        | clause (())

clause : BAR params expr (())

params : params param (())
       | param (())

param : pattern DRARROW (())

block : LBRACE stmts RBRACE (())

triv : VAR (())

(* Patterns *)

pattern : pattern COLON typ (())
        | VAR (())

(* Types *)

typ : LPAREN EQ typ RPAREN (())
    | expr (())

