%{
open Ast.Type
open Ast.Term.Expr
open Ast.Term.Stmt
open Util

(* TODO: or-patterns *)

let path = function
    | Proxy typ -> typ
    | expr -> Path expr

let proxy = function
    | Path expr -> expr
    | typ -> Proxy typ

let to_arg args pos =
    if Vector.length args = 1
    then Vector.get args 0
    else {v = Values args; pos}
%}

%token
    EFFOW "-!" ARROW "->" LARROW "<-" DARROW "=>" EQ "="
    DOT "." COLON ":" COMMA "," SEMI ";"
    BAR "|" BANG "!" QMARK "?" AT "@" BACKSLASH
    LPAREN "(" RPAREN ")" LBRACKET "[" RBRACKET "]" LBRACE "{" RBRACE "}"
    EOF
%token <string> DISJUNCTION "||" CONJUNCTION "&&" COMPARISON ADDITIVE MULTIPLICATIVE
%token <string> PRIMOP WILD ID OP
%token <string> STRING
%token <int> INT

%start program commands
%type <Ast.Term.Stmt.def Vector.t> program
%type <Ast.Term.Stmt.t Vector.t> commands

%%

tail(separator, item, terminator) :
    | separator item tail(separator, item, terminator) { $2 :: $3 }
    | separator? terminator { [] }

trail(separator, item, terminator) :
    | item tail(separator, item, terminator) { Vector.of_list ($1 :: $2) }
    | terminator { Vector.empty }

trailer(init, separator, item, terminator) : init trail(separator, item, terminator) { $2 }

(* # Entry Points *)

program : trail(";", def, EOF) { $1 }

commands : trail(";", stmt, EOF) { $1 }

(* # Definitions & Statements *)

def : expr "=" expr { ($loc, $1, $3) }

stmt :
    | def { Def $1 }
    | expr { Expr $1 }

(* # Expressions *)

expr : typ { {$1 with v = proxy $1.v} }

ann_expr :
    | binapp ":" typ { {v = Ann ($1, $3); pos = $loc} } (* NOTE: ~ right-associative *)
    | binapp { $1 }

binapp :
    | binapp "||" binapp2 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Right {v = Values (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp2 { $1 }

binapp2 :
    | binapp2 "&&" binapp3 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Right {v = Values (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp3 { $1 }

binapp3 :
    | binapp4 COMPARISON binapp4 { (* NOTE: nonassociative *)
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Right {v = Values (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp4 { $1 }

binapp4 :
    | binapp4 ADDITIVE binapp5 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Right {v = Values (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp5 { $1 }

binapp5 :
    | binapp5 MULTIPLICATIVE app {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Right {v = Values (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | app { $1 }

app :
    | PRIMOP args {
        let op = match Primop.of_string $1 with
            | Some op -> op
            | None -> failwith ("No such primop: __" ^ $1) in
        match $2 with
        | Left iargs -> {v = PrimApp (op, Left (to_arg iargs $loc($2))); pos = $loc}
        | Right eargs -> {v = PrimApp (op, Right (to_arg eargs $loc($2))); pos = $loc}
        | Both (iargs, eargs) ->
            {v = PrimApp (op, Both (to_arg iargs $loc($2), to_arg eargs $loc($2))); pos = $loc}
    }
    | select args { match $2 with
        | Left iargs -> {v = App ($1, Left (to_arg iargs $loc($2))); pos = $loc}
        | Right args ->
            let args = args |> Vector1.of_vector |> Option.get in
            {v = AppSequence (Vector1.append (Vector1.singleton $1) args); pos = $loc}
        | Both (iargs, eargs) ->
            {v = App ($1, Both (to_arg iargs $loc($2), to_arg eargs $loc($2))); pos = $loc}
    }
    | select { $1 }

select :
    | select "." ID { {v = Select ($1, Name.of_string $3); pos = $loc} }
    | select "." INT { {v = Focus ($1, $3); pos = $loc} }
    | nestable { $1 }

nestable : nestable_without_pos { {v = $1; pos = $sloc} }

nestable_without_pos :
    | trailer("{", ";", stmt, "}") { Record $1 }
    | "{" clause+ "}" { Fn (Vector.of_list $2) }
    | "{" "||" stmt tail(";", stmt, "}") {
        let body = App ( {v = Var (Name.of_string "do"); pos = $loc}
            , Right {v = Record (Vector.of_list ($3 :: $4)); pos = $loc} ) in
        Fn (Vector.singleton
            { params = Ior.Right {v = Values Vector.empty; pos = $loc($2)}
            ; body = {v = body; pos = $loc} })
    }
    | "{" "|" "}" { Fn Vector.empty }
    | trailer("(", ",", expr, ")") { Values $1 }
    | "(" "||" ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" "&&" ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" COMPARISON ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" ADDITIVE ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" MULTIPLICATIVE ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" "|" stmt tail("|", stmt, ")") { proxy (Row (Vector.of_list ($3 :: $4))) }
    | "(" "|" ")" { proxy (Row Vector.empty) }
    | "{" ":" stmt tail(";", stmt, "}") { proxy (Record (Vector.of_list ($3 :: $4))) }
    | "{" ":" "}" { proxy (Record Vector.empty) }
    | "(" ":" typ tail(",", typ, ")") { proxy (Ast.Type.Values (Vector.of_list ($3 :: $4))) }
    | "(" ":" ")" { proxy (Values Vector.empty) }
    | ID { Var (Name.of_string $1) }
    | WILD { failwith "TODO" }
    | INT { Const (Int $1) }

clause : params expr { {params = $1; body = $2} }

params :
    | "?" select* "|" select* "|" {
        Both ( {v = Values (Vector.of_list $2); pos = $loc($2)}
             , {v = Values (Vector.of_list $4); pos = $loc($4)} )
    }
    | "|" select* "|" { Ior.Right {v = Values (Vector.of_list $2); pos = $loc($2)} }
    | "?" select* "?" { Ior.Left {v = Values (Vector.of_list $2); pos = $loc($2)} }

args :
    | select+ "@" select+ { Ior.Both (Vector.of_list $1, Vector.of_list $3) }
    | select+ { Ior.Right (Vector.of_list $1) }
    | select+ "@" { Ior.Left (Vector.of_list $1) }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos :
    | binapp "=>" binapp "-!" binapp "->" typ {
        Pi {domain = Both ($1, ($3, Some {$5 with v = path $5.v})); codomain = $7}
    }
    | binapp "=>" binapp "->" typ {
        Pi {domain = Both ($1, ($3, None)); codomain = $5}
    }
    | binapp "=>" ann_expr {
        Pi {domain = Left $1; codomain = {$3 with v = path $3.v}}
    }
    | binapp "-!" binapp "->" typ {
        Pi {domain = Right ($1, Some {$3 with v = path $3.v}); codomain = $5}
    }
    | binapp "->" typ {
        Pi {domain = Right ($1, None); codomain = $3}
    }
    | ann_expr { path $1.v }

