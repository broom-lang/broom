%token VAR BINOP
       WILD "_"
       DO "do" END "end" MODULE "module"
       TYPE "type" INTERFACE "interface"
       EQ "=" RDARROW "=>"
       DOT "." DDOT ".."
       LPAREN "(" RPAREN ")" LBRACE "{" RBRACE "}"
       BAR "|" AMP "&"
       COLON ":" SEAL ":>"
       COMMA "," SEMICOLON ";"
       EOF

%start <unit> program

%%

program : stmts EOF {()}

(* Statements *)

stmts : {()}
      | stmts stmt {()}

stmt : pattern "=" expr ";" {()}
     | "type" pattern "=" expr ";" {()}
     | expr ";" {()}

(* Expressions *)

expr : expr ":>" nestableTyp {()}
     | binapp {()}

binapp : binapp BINOP app {()}
       | app {()}

app : app nestableExpr {()}
    | "type" nestableTyp {()}
    | nestableExpr {()}

nestableExpr : "{" clauses "}" {()}
             | "{" rowExpr "}" {()}
             | "do" stmts "end" {()}
             | "module" stmts "end" {()}
             | nestableExpr "." VAR {()}
             | "(" BINOP ")" {()}
             | "(" expr ")" {()}
             | triv {()}

clauses : clauses clause {()}
        | clause {()}

clause : "|" params expr {()}

params : params param {()}
       | param {()}

param : pattern "=>" {()}

rowExpr : fields tail {()}

fields : {()}
       | field {()}
       | fields "," field {()}

field : VAR "=" expr {()}
      | VAR {()}

tail : {()}
     | ".." expr {()}

triv : VAR {()}
     | const {()}

const : "(" ")" {()}

(* Patterns *)

pattern : pattern ":" typ {()}
        | VAR {()}

(* Types *)

typ : purelyTyp {()}
    | expr {()}

nestableTyp : purelyTyp {()}
            | nestableExpr {()}

purelyTyp : "{" row "}" {()}
          | "interface" decls "end" {()}
          | "(" row ")" {()}
          | "(" "=" expr ")" {()}

row : ":" {()}
    | rowFields {()}
    | rowTail {()}
    | rowFields rowTail {()}

rowFields : rowField {()}
          | rowFields "," rowField {()}

rowField : VAR ":" typ {()}

rowTail : "&" {()}
        | "|" {()}
        | "&" typ {()}
        | "|" typ {()}

(* Declarations *)

decls : {()}
      | decls decl {()}

decl : VAR ":" typ ";" {()}
     | "type" VAR "=" typ ";" {()}
     | "type" VAR ":" typ ";" {()}
     | "type" VAR ";" {()}

