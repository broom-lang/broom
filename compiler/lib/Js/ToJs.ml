open Streaming
open Asserts

open Cfg

module Uses = Expr.Id.Hashtbl

let count_uses_by_cont program =
    let counts = Expr.Id.Hashtbl.create 0 in
    let visited = Cont.Id.HashSet.create 0 in

    let visit_use parent use =
        let use_counts = match Expr.Id.Hashtbl.find_opt counts use with
            | Some use_counts -> use_counts
            | None ->
                let use_counts = Cont.Id.Hashtbl.create 1 in
                Expr.Id.Hashtbl.add counts use use_counts;
                use_counts in
        let count = match Cont.Id.Hashtbl.find_opt use_counts parent with
            | Some n -> n
            | None -> 0 in
        Cont.Id.Hashtbl.add use_counts parent (count + 1) in

    let rec visit_stmt parent stmt =
        Stmt.iter_labels visit_label stmt;
        Stmt.iter_uses (visit_use parent) stmt

    and visit_transfer parent transfer =
        Transfer.iter_labels visit_label transfer;
        Transfer.iter_uses (visit_use parent) transfer

    and visit_label label =
        if Cont.Id.HashSet.mem visited label
        then ()
        else begin
            Cont.Id.HashSet.insert visited label;
            let {Cont.pos = _; name = _; universals = _; params = _; stmts; transfer} =
                Program.cont program label in
            Vector.iter (visit_stmt label) stmts;
            visit_transfer label transfer
        end in

    Source.each visit_label (Program.exports program);
    counts

(* OPTIMIZE: Get rid of intermediate lists *)

module Js = struct
    type expr =
        | Function of Name.t Vector.t * block
        | Call of expr * expr Vector.t
        | Object of (string * expr) Vector.t
        | Select of expr * string
        | Array of expr Vector.t
        | Use of Expr.Id.t
        | UseExtern of string
        | String of string
        | Int of int

    and stmt =
        | Var of expr * expr
        | Assign of expr * expr
        | Expr of expr
        | Return of expr
        | Switch of expr * (expr option * block) Vector.t

    and block = stmt Vector.t

    let fn_ = PIso.prism (fun (params, body) -> Function (params, body)) (function
        | Function (params, body) -> Some (params, body)
        | _ -> None)

    let call_ = PIso.prism (fun (callee, args) -> Call (callee, args)) (function
        | Call (callee, args) -> Some (callee, args)
        | _ -> None)

    let object_ = PIso.prism (fun fields -> Object fields) (function
        | Object fields -> Some fields
        | _ -> None)

    let array_ = PIso.prism (fun xs -> Array xs) (function
        | Array xs -> Some xs
        | _ -> None)

    let select_ = PIso.prism (fun (expr, label) -> Select (expr, label)) (function
        | Select (expr, label) -> Some (expr, label)
        | _ -> None)

    let use_ = PIso.prism (fun id -> Use id) (function
        | Use id -> Some id
        | _ -> None)

    let use_extern_ = PIso.prism (fun name -> UseExtern name) (function
        | UseExtern name -> Some name
        | _ -> None)

    let string_ = PIso.prism (fun s -> String s) (function
        | String s -> Some s
        | _ -> None)

    let int_ = PIso.prism (fun n -> Int n) (function
        | Int n -> Some n
        | _ -> None)

    let var_ = PIso.prism (fun (l, r) -> Var (l, r)) (function
        | Var (l, r) -> Some (l, r)
        | _ -> None)

    let assign_ = PIso.prism (fun (l, r) -> Assign (l, r)) (function
        | Assign (l, r) -> Some (l, r)
        | _ -> None)

    let expr_ = PIso.prism (fun expr -> Expr expr) (function
        | Expr expr -> Some expr
        | _ -> None)

    let return_ = PIso.prism (fun expr -> Return expr) (function
        | Return expr -> Some expr
        | _ -> None)

    let switch_ = PIso.prism (fun (expr, cases) -> Switch (expr, cases)) (function
        | Switch (expr, cases) -> Some (expr, cases)
        | _ -> None)

    type any =
        | Expr' of expr
        | Stmt of stmt

    let expr'_ = PIso.prism (fun expr -> Expr' expr) (function
        | Expr' expr -> Some expr
        | _ -> None)

    let stmt_ = PIso.prism (fun stmt -> Stmt stmt) (function
        | Stmt stmt -> Some stmt
        | _ -> None)

    let grammar =
        let open Grammar in let open Grammar.Infix in

        fix (fun any ->
            let expr = PIso.inv expr'_ <$> any in
            let stmt = PIso.inv stmt_ <$> any in

            let stmts = PIso.vector <$> many (stmt <* break 1) in
            let block = surround_separate 4 1 (braces (pure Vector.empty))
                lbrace (break 1) rbrace stmt in

            let use = Name.grammar in

            let use_extern =
                let cs = many (PIso.subset (Fun.negate (String.contains " \t\r\n")) <$> char) in
                PIso.string <$> cs in

            let string =
                let cs = many (PIso.subset ((<>) '"') <$> char) in
                token '"' *> (PIso.string <$> cs) <* token '"' in

            let fn =
                let params = surround_separate 4 0 (parens (pure Vector.empty))
                    lparen (comma *> break 1) rparen Name.grammar in
                fn_ <$> (text "function" *> blank 1 *> params <*> blank 1 *> block) in

            let obj =
                let fields = separate (semi *> break 1) (infix 4 1 colon use_extern expr) in
                PIso.comp object_ PIso.vector <$> braces fields in

            let atom = 
                use_ <$> use
                <|> (use_extern_ <$> use_extern)
                <|> (string_ <$> string)
                <|> (int_ <$> int) in

            let nestable = obj
                <|> (PIso.comp array_ PIso.vector <$> brackets (separate (comma *> break 1) expr))
                <|> atom
                <|> parens expr in

            let select =
                let f = PIso.iso (fun (expr, labels) ->
                        List.fold_left (fun expr label -> Select (expr, label)) expr labels)
                    (fun expr ->
                        let rec loop labels expr = match PIso.unapply select_ expr with
                            | Some (expr, label) -> loop (label :: labels) expr
                            | None -> (expr, labels) in
                        loop [] expr) in
                f <$> (nestable <*> many (dot *> use_extern)) in

            let call =
                let f = PIso.iso (fun (callee, argss) ->
                        List.fold_left (fun callee args -> Call (callee, args))
                            callee argss)
                    (fun expr ->
                        let rec loop argss expr = match PIso.unapply call_ expr with
                            | Some (callee, args) -> loop (args :: argss) callee
                            | None -> (expr, argss) in
                        loop [] expr) in
                let args = surround_separate 4 0 (parens (pure Vector.empty))
                    lparen (comma *> break 1) rparen expr in
                f <$> (select <*> many args) in

            let expr = fn <|> call in

            let stmt =
                let case = (PIso.some <$> (text "case" *> blank 1 *> expr)
                        <|> text "default" *> pure None)
                    <*> nest 4 stmts in
                let cases = PIso.vector <$> many case in
                (var_ <$> infix 4 1 equals (text "var" *> blank 1 *> expr) expr
                <|> (assign_ <$> infix 4 1 equals expr expr)
                <|> (expr_ <$> expr)
                <|> (return_ <$> text "return" *> blank 1 *> expr)
                <|> (switch_ <$> (text "switch" *> blank 1 *> parens expr <* blank 1
                    <*> braces cases)))
                <* semi in

            expr'_ <$> expr
            <|> (stmt_ <$> stmt))

    let to_doc = PPrinter.of_grammar grammar
end

let to_js program =
    let usecounts = count_uses_by_cont program in
    let is_inlineable parent var expr =
        if Expr.is_pure expr then
            match Expr.Id.Hashtbl.find_opt usecounts var with
            | Some var_usecounts ->
                Cont.Id.Hashtbl.find_opt var_usecounts parent
                |> Option.value ~default: 0
                |> (=) 1
            | None -> false
        else false in

    let uses = Uses.create 0 in
    let add_var_name var =
        let expr = Js.Use var in
        Uses.add uses var expr;
        expr in
    let add_var_expr = Uses.add uses in
    let emit_use = Uses.find uses in

    let emit_label (label : Cont.Id.t) =
        let {name; _} : Cont.t = Program.cont program label in
        let prefix = match name with
            | Some name -> Name.to_string name
            | None -> "fn" in
        Js.UseExtern (prefix ^ "$" ^ Int.to_string (label :> int)) in

    let emit_const : Const.t -> Js.expr = function
        | Int n -> Js.Int n
        | String s -> Js.String s in

    let rec emit_transfer parent stmts (transfer : Transfer.t) =
        let emit_expr pos : Expr.t -> Js.expr = function
            | PrimApp {op = Import; universals = _; args} ->
                assert (Vector.length args = 2);
                Call (UseExtern "require", Vector.map emit_use (Vector.sub args 1 1))

            | PrimApp {op; _} -> todo (Some pos) ~msg: (Primop.to_string op)

            | Record fields -> Object (Vector.map (fun (label, field) ->
                (Name.basename label |> Option.get, emit_use field))
                fields)

            | Where {base; fields} ->
                let base_name = Name.fresh () in
                let copy = Js.Var (Use base_name
                    , Call (Select (UseExtern "Object", "assign")
                        , Vector.of_list [Js.Object Vector.empty; emit_use base])) in
                let assignments = fields |> Vector.map (fun (label, v) ->
                    Js.Assign (Select (Use base_name, Name.basename label |> Option.get)
                        , emit_use v)) in
                let body = Stream.single copy
                    |> Fun.flip Stream.concat (Stream.from (Vector.to_source assignments))
                    |> Fun.flip Stream.concat (Stream.single (Js.Return (Use base_name)))
                    |> Stream.into (Vector.sink ()) in
                Call (Js.Function (Vector.empty, body), Vector.empty)

            | With _ -> todo (Some pos)
(*
            | With {base; label; field} ->
                let base_name = fresh () in
                let stmt = infix 4 1 equals
                    (string "var" ^^ blank 1 ^^ base_name)
                    (string "Object.assign"
                    ^^ parens (braces empty ^^ comma ^^ break 1 ^^ emit_use base)) in
                CCVector.push stmts stmt;
                let stmt = infix 4 1 equals
                    (base_name ^^ dot ^^ string (Name.basename label |> Option.get))
                    (emit_use field) in
                CCVector.push stmts stmt;
                base_name
*)

            | Select {selectee; field} ->
                Select (emit_use selectee, Name.basename field |> Option.get)

            | Proxy _ -> Js.Int 0 (* OPTIMIZE: empty unboxed tuple = erase *)

            | Label label -> (* TODO: Assumes Label node has not been duplicated; stop that *)
                let cont = Program.cont program label in
                emit_fn label cont

            | Const c -> emit_const c

            | Pack {existentials = _; impl} -> emit_use impl
            | Unpack packed -> emit_use packed

            | Param _ -> bug (Some pos) ~msg: "Param in Cfg"
            | Tuple _ -> bug (Some pos) ~msg: "Tuple in Cfg"
            | Focus _ -> bug (Some pos) ~msg: "Focus in Cfg" in

        let emit_clause ({pat; dest} : Transfer.clause) =
            let emit_pat : Transfer.Pattern.t -> Js.expr option = function
                | Const c -> Some (emit_const c)
                | Wild -> None in

            let {Cont.pos = _; name = _; universals = _; params = _; stmts; transfer} =
                Program.cont program dest in
            (emit_pat pat, emit_transfer dest stmts transfer) in

        let emit_stmt ({term = (vars, expr); pos; typ = _} : Stmt.t) : Js.stmt Vector.t =
            match Vector.length vars with
            | 0 -> Vector.singleton (Js.Expr (emit_expr pos expr))
            | 1 ->
                let var = Vector.get vars 0 in
                let expr' = emit_expr pos expr in
                if is_inlineable parent var expr
                then begin
                    add_var_expr var expr';
                    Vector.empty
                end else begin
                    let name = add_var_name var in
                    Vector.singleton (Js.Var (name, expr'))
                end
            | _ -> bug (Some pos) ~msg: "> 1 vars reached emit_stmt" in

        let stmts = Vector.flat_map emit_stmt stmts in
        let transfer = match transfer.term with
            | Goto {callee; universals = _; args} ->
                Js.Return (Call (emit_label callee, Vector.map emit_use args))

            | Jump {callee; universals = _; args} ->
                Return (Call (emit_use callee, Vector.map emit_use args))

            | Match {matchee; clauses} ->
                Switch (emit_use matchee, Vector.map emit_clause clauses)

            | PrimApp _ -> todo (Some transfer.pos)

            | Return (_, args) -> Return (Array (Vector.map emit_use args)) in
        Stream.concat (Stream.from (Vector.to_source stmts)) (Stream.single transfer)
        |> Stream.into (Vector.sink ())

    and emit_fn label {Cont.pos = _; name = _; universals = _; params; stmts; transfer} =
        let params = Vector.map (fun (name, _) -> ignore (add_var_name name); name) params in
        Function (params, emit_transfer label stmts transfer) in

    let emit_export label =
        let cont = Program.cont program label in
        Js.Var (emit_label label, emit_fn label cont) in

    Stream.from (Program.exports program)
    |> Stream.map emit_export

let emit program = to_js program
    |> Stream.map (fun stmt -> Js.to_doc (Stmt stmt))
    |> Stream.into (Sink.fold PPrint.(^^) PPrint.empty)

