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
%token <int> INT

%start program commands
%type <Ast.Term.def Vector.t> program
%type <Ast.Term.stmt Vector.t> commands

%%

program : defs EOF { $1 }

commands : stmts? EOF { match $1 with
        | Some stmts -> Vector1.to_vector stmts
        | None -> Vector.empty ()
    }

(* # Definitions & Statements *)

def : exprs "=" exprs { failwith "TODO" }

defs : separated_list(";", def) { Vector.of_list $1 }

stmt :
    | def { Def $1 }
    | exprs { Expr {v = Values (Vector1.to_vector $1); pos = $loc} }

stmts : separated_nonempty_list(";", stmt) { Vector1.of_list $1 |> Option.get }

(* # Expressions *)

expr : typ { {$1 with v = proxy $1.v} }

exprs : separated_nonempty_list(",", expr) { Vector1.of_list $1 |> Option.get }

ann_expr :
    | explicitly ":" typ { failwith "TODO" } (* NOTE: ~ right-associative *)
    | explicitly { $1 }

explicitly :
    | binapp at_params { failwith "TODO" }
    | binapp { $1 }

binapp :
    | binapp OP1 binapp2 {
        let operator = {v = Use (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp2 { $1 }

binapp2 :
    | binapp2 OP2 binapp3 {
        let operator = {v = Use (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp3 { $1 }

binapp3 :
    | binapp4 OP3 binapp4 { (* NOTE: nonassociative *)
        let operator = {v = Use (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp4 { $1 }

binapp4 :
    | binapp4 OP4 binapp5 {
        let operator = {v = Use (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp5 { $1 }

binapp5 :
    | binapp5 OP5 app {
        let operator = {v = Use (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | app { $1 }

app :
    | PRIMOP params? { failwith "TODO" }
    | select params { {v = AppSequence (Vector1.append (Vector1.singleton $1) $2); pos = $loc} }
    | select { $1 }

select :
    | select "." ID { {v = Select ($1, Name.of_string $3); pos = $loc} }
    | nestable { $1 }

nestable : nestable_without_pos { {v = $1; pos = $sloc} }

nestable_without_pos :
    | "{" stmts? "}" { match $2 with
        | Some stmts -> Record (Vector1.to_vector stmts)
        | None -> Record (Vector.empty ())
    }
    | "[" clause* "]" { Fn (Vector.of_list $2) }
    | "[" stmts "]" { failwith "TODO" }
    | "(" exprs? ")" { match $2 with
        | Some exprs -> Values (Vector1.to_vector exprs)
        | None -> Values (Vector.empty ())
    }
    | "(" OP1 ")" { Values (Vector.singleton ({v = Use (Name.of_string $2); pos = $loc($2)}))}
    | "(" OP2 ")" { Values (Vector.singleton ({v = Use (Name.of_string $2); pos = $loc($2)}))}
    | "(" OP3 ")" { Values (Vector.singleton ({v = Use (Name.of_string $2); pos = $loc($2)}))}
    | "(" OP4 ")" { Values (Vector.singleton ({v = Use (Name.of_string $2); pos = $loc($2)}))}
    | "(" OP5 ")" { Values (Vector.singleton ({v = Use (Name.of_string $2); pos = $loc($2)}))}
    | ID { Use (Name.of_string $1) }
    | WILD { failwith "TODO" }
    | INT { Const (Int $1) }

clause : "|" params? at_params? "->" exprs { failwith "TODO" }

params : select+ { Vector1.of_list $1 |> Option.get }

at_params : "@" params? { match $2 with (* TODO: Implicit args need more design *)
        | Some params -> Vector1.to_vector params
        | None -> Vector.empty ()
    }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos :
    | explicitly "->" typ "!" typ { failwith "TODO" }
    | explicitly "=>" typ { failwith "TODO" }
    | ann_expr { path $1.v }

