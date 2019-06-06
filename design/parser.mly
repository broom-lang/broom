%token VAR BINOP
       WILD "_"
       DO "do" END "end" MODULE "module"
       TYPE "type" INTERFACE "interface"
       EQ "=" RDARROW "=>"
       DOT "." DDOT ".."
       LPAREN "(" RPAREN ")" LBRACKET "[" RBRACKET "]" LBRACE "{" RBRACE "}"
       BAR "|" AMP "&"
       COLON ":"
       COMMA "," SEMICOLON ";"
       EOF

(* Semicolon and `end` inference can be added to lexer if desired. *)

%start <unit> program

%%

program : stmts EOF {()}

(* Statements *)

stmts : {()}
      | stmts stmt {()}

stmt : pattern "=" expr ";" {()}
     | expr ";" {()}

(* Expressions *)

expr : expr ":" typeAnn {()}
     | binapp {()}

binapp : binapp BINOP app {()} (* need auxiliary precedence parser because of custom binops *)
       | app {()}

app : app nestableExpr {()}
    | nestableExpr {()}

nestableExpr : "{" clauses "}" {()}
             | "{" rowExpr "}" {()}
             | "do" stmts "end" {()}
             | "[" "|" stmts "]" {()}
             | "module" stmts "end" {()}
             | nestableExpr "." VAR {()}
             | "(" BINOP ")" {()}
             | purelyTyp {()}
             | "(" expr ")" {()}
             | triv {()}

clauses : clauses clause {()}
        | clause {()}

clause : "|" params expr {()}

params : params param {()}
       | param {()}

param : apattern "=>" {()} (* or-patterns need to be parenthesized to be unambiguous *)

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
         | expr {()} (* validating that expr is a valid pattern is easier outside grammar proper *)

(* Types *)

typ : expr {()}

typeAnn : binapp {()}

purelyTyp : "{" row "}" {()}
          | "interface" decls "end" {()}
          | "(" "|" row "|" ")" {()}
          | "(" "=" expr ")" {()}

row : ":" {()}
    | rowFields {()}
    | rowTail {()}
    | rowFields rowTail {()}

rowFields : rowField {()}
          | rowFields "," rowField {()}

rowField : VAR ":" typ {()}

rowTail : "&" {()}
        | "&" typ {()}

(* Declarations *)

decls : {()}
      | decls decl {()}

decl : VAR ":" typ ";" {()}
     | "type" VAR "=" typ ";" {()}
     | "type" VAR ":" typ ";" {()}
     | "type" VAR ";" {()}

