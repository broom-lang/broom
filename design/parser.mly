%token VAR BINOP
       (*TYPE "type"*)
       EQ "=" RDARROW "=>"
       LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}"
       BAR "|"
       COLON ":" SEMICOLON ";"
       EOF

%start <unit> program

%%

program : stmts EOF {()}

(* Statements *)

stmts : {()}
      | stmts stmt {()}

stmt : pattern "=" expr ";" {()}
     | expr ";" {()}

(* Expressions *)

expr : (*expr ":" typ {()}
     |*) binapp {()}

binapp : binapp BINOP app {()}
       | app {()}

app : app nestableExpr {()}
    | nestableExpr {()}

nestableExpr : lambda {()}
             | block {()}
             (*| "type" typ {()}*)
             | "(" BINOP ")" {()}
             | "(" expr ")" {()}
             | triv {()}

lambda : "{" clauses "}" {()}

clauses : clauses clause {()}
        | clause {()}

clause : "|" params expr {()}

params : params param {()}
       | param {()}

param : pattern "=>" {()}

block : "{" stmts "}" {()}

triv : VAR {()}

(* Patterns *)

pattern : pattern ":" typ {()}
        | VAR {()}

(* Types *)

typ : "(" "=" typ ")" {()}
    | expr {()}

