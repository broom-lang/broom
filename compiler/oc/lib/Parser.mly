%{
open Ast
open Ast.Term
open Ast.Type
open Util

let path = function
    | Proxy typ -> typ
    | expr -> Path expr

let proxy = function
    | Path expr -> expr
    | typ -> Proxy typ

%}

%token
    ARROW "->" LARROW "<-" DARROW "=>" DOT "." COLON ":" EQ "=" COMMA "," SEMI ";" BAR "|" (* ELLIPSIS "..." *)
    BANG "!" AT "@"
    LPAREN "(" RPAREN ")"
    LBRACKET "[" RBRACKET "]"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> OP1 OP2 OP3 OP4 OP5 PRIMOP ID WILD (* FIXME: actually design infix operators *)
%token <int> CONST

%start <Ast.Term.stmt Vector.t> program

%%

program : defs? EOF { failwith "TODO" }

(* # Definitions & Statements *)

def : exprs "=" exprs { failwith "TODO" }

defs : separated_nonempty_list(";", def) { failwith "TODO" }

stmt :
    | def { failwith "TODO" }
    | exprs { failwith "TODO" }

stmts : separated_nonempty_list(";", stmt) { failwith "TODO" }

(* # Expressions *)

expr : typ { failwith "TODO" }

exprs : separated_nonempty_list(",", expr) { failwith "TODO" }

ann_expr :
    | explicitly ":" typ { failwith "TODO" } (* NOTE: ~ right-associative *)
    | explicitly { failwith "TODO" }

explicitly :
    | binapp at_params { failwith "TODO" }
    | binapp { failwith "TODO" }

binapp :
    | binapp OP1 binapp2 { failwith "TODO" }
    | binapp2 { failwith "TODO" }

binapp2 :
    | binapp2 OP2 binapp3 { failwith "TODO" }
    | binapp3 { failwith "TODO" }

binapp3 :
    | binapp4 OP3 binapp4 { failwith "TODO" } (* NOTE: nonassociative *)
    | binapp4 { failwith "TODO" }

binapp4 :
    | binapp4 OP4 binapp5 { failwith "TODO" }
    | binapp5 { failwith "TODO" }

binapp5 :
    | binapp5 OP5 app { failwith "TODO" }
    | app { failwith "TODO" }

app :
    | PRIMOP params? { failwith "TODO" }
    | select params { failwith "TODO" }
    | select { failwith "TODO" }

select :
    | select "." nestable { failwith "TODO" }
    | nestable { failwith "TODO" }

nestable :
    | "{" stmts? "}" { failwith "TODO" }
    | "[" clause* "]" { failwith "TODO" }
    | "[" stmts "]" { failwith "TODO" }
    | "(" exprs? ")" { failwith "TODO" }
    | "(" OP1 ")" { failwith "TODO" }
    | "(" OP2 ")" { failwith "TODO" }
    | "(" OP3 ")" { failwith "TODO" }
    | "(" OP4 ")" { failwith "TODO" }
    | "(" OP5 ")" { failwith "TODO" }
    | ID { failwith "TODO" }
    | WILD { failwith "TODO" }
    | CONST { failwith "TODO" }

clause : "|" params? at_params? "->" exprs { failwith "TODO" }

params : select+ { failwith "TODO" }

at_params : "@" params? { failwith "TODO" } (* TODO: Implicit args need more design *)

(* # Types *)

typ : explicitly "->" typ "!" typ { failwith "TODO" }
    | explicitly "=>" typ { failwith "TODO" }
    | ann_expr { failwith "TODO" }

