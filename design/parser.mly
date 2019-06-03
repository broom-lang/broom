%token VAR BINOP
       WILD "_"
       DO "do" END "end" MODULE "module"
       TYPE "type" INTERFACE "interface"
       EQ "=" RDARROW "=>"
       DOT "." DDOT ".."
       LPAREN "(" RPAREN ")" LBRACKET "[" RBRACKET "]" LBRACE "{" RBRACE "}"
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
     | pattern "=" purelyTyp ";" {()}
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
             | "[" "|" stmts "]" {()}
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

param : apattern "=>" {()}

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

pattern : pattern "|" apattern {()}
        | apattern {()}

apattern : apattern "&" expr {()}
         | expr {()}

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

