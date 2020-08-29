%{
open Ast.Term.Expr
open Ast.Term.Stmt
open Ast.Type
open Util

(* TODO: or-patterns *)

let path = function
    | Proxy typ -> typ
    | expr -> Path expr

let proxy = function
    | Path expr -> expr
    | typ -> Proxy typ
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

(* # Entry Points *)

program : defs EOF { $1 }

commands : stmts? EOF { match $1 with
        | Some stmts -> Vector1.to_vector stmts
        | None -> Vector.empty ()
    }

(* # Definitions & Statements *)

def : expr "=" expr { ($loc, $1, $3) }

defs : separated_list(";", def) { Vector.of_list $1 }

stmt :
    | def { Def $1 }
    | expr { Expr $1 }

stmts : separated_nonempty_list(";", stmt) { Vector1.of_list $1 |> Option.get }

(* # Expressions *)

expr : typ { {$1 with v = proxy $1.v} }

ann_expr :
    | explicitly ":" typ { {v = Ann ($1, $3); pos = $loc} } (* NOTE: ~ right-associative *)
    | explicitly { $1 }

explicitly :
    | binapp at_args { failwith "TODO" }
    | binapp { $1 }

binapp :
    | binapp "||" binapp2 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp2 { $1 }

binapp2 :
    | binapp2 "&&" binapp3 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp3 { $1 }

binapp3 :
    | binapp4 COMPARISON binapp4 { (* NOTE: nonassociative *)
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp4 { $1 }

binapp4 :
    | binapp4 ADDITIVE binapp5 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | binapp5 { $1 }

binapp5 :
    | binapp5 MULTIPLICATIVE app {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Vector.of_list [$1; $3]); pos = $loc}
    }
    | app { $1 }

app :
    | PRIMOP args? {
        let args = match $2 with
            | Some args -> Vector1.to_vector args
            | None -> Vector.empty () in
        match Primop.of_string $1 with
        | Some op -> {v = PrimApp (op, args); pos = $loc}
        | None -> failwith ("No such primop: __" ^ $1)
    }
    | select args { {v = AppSequence (Vector1.append (Vector1.singleton $1) $2); pos = $loc} }
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
    | "[" stmts "]" { Thunk (Vector1.to_vector $2) }
    | "(" separated_list(",", expr) ")" { Values (Vector.of_list $2) }
    | "(" "||" ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" "&&" ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" COMPARISON ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" ADDITIVE ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" MULTIPLICATIVE ")" { Values (Vector.singleton ({v = Var (Name.of_string $2); pos = $loc($2)}))}
    | "(" "|" stmts "|" ")" { proxy (Row (Vector1.to_vector $3)) }
    | "(" "|" ")" { proxy (Row (Vector.empty ())) }
    | "{" "|" stmts "|" "}" { proxy (Record (Vector1.to_vector $3)) }
    | "{" "|" "}" { proxy (Record (Vector.empty ())) }
    | ID { Var (Name.of_string $1) }
    | WILD { failwith "TODO" }
    | INT { Const (Int $1) }

clause : "|" params "->" expr {
        let (iparams, eparams) = $2 in
        {iparams; eparams; body = $4}
    }

params :
    | select+ "=>" select* { ($1 |> Vector.of_list, $3 |> Vector.of_list) }
    | select* { (Vector.empty (), Vector.of_list $1) }

args : select+ { Vector1.of_list $1 |> Option.get }

at_args : "@" args? { match $2 with (* TODO: Implicit args need more design *)
        | Some args -> Vector1.to_vector args
        | None -> Vector.empty ()
    }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos :
    | binapp "=>" binapp "-!" binapp "->" typ { failwith "TODO" }
    | binapp "=>" binapp "->" typ { failwith "TODO" }
    | binapp "=>" ann_expr { failwith "TODO" }
    | binapp "-!" binapp "->" typ { Pi ($1, {$3 with v = path $3.v}, $5) }
    | binapp "->" typ { Pi ($1, {v = Row (Vector.empty ()); pos = $loc($2)}, $3) }
    | ann_expr { path $1.v }

