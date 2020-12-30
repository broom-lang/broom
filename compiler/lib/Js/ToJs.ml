open Streaming
open Cfg
open PPrint

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

let emit program =
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

    let counter = ref 0 in
    let fresh () =
        let i = !counter in
        counter := i + 1;
        string ("y$" ^ Int.to_string i) in

    let uses = Uses.create 0 in
    let add_var_name (var : Expr.Id.t) =
        let doc = string ("x$" ^ Int.to_string (var :> int)) in
        Uses.add uses var doc;
        doc in
    let add_var_expr = Uses.add uses in
    let emit_use = Uses.find uses in

    let emit_label (label : Cont.Id.t) =
        let {name; _} : Cont.t = Program.cont program label in
        let prefix = match name with
            | Some name -> Name.to_doc name
            | None -> string "fn" in
        prefix ^^ dollar ^^ string (Int.to_string (label :> int)) in

    let emit_const : Const.t -> PPrint.document = function
        | Int n -> string (Int.to_string n)
        | String s -> dquotes (string s) in (* HACK *)

    let rec emit_transfer parent stmts (transfer : Transfer.t) =
        let emit_expr : Expr.t -> PPrint.document = function
            | PrimApp {op = Import; universals = _; args} ->
                assert (Vector.length args = 2);
                string "require" ^^ parens (emit_use (Vector.get args 1))

            | PrimApp {op; _} -> failwith ("TODO: " ^ Primop.to_string op)

            | Record fields ->
                surround_separate_map 4 0 (braces empty)
                    lbrace (comma ^^ break 1) rbrace
                    (fun (label, field) ->
                        string (Name.basename label |> Option.get)
                        ^^ colon ^^ blank 1 ^^ emit_use field)
                    (Vector.to_list fields)

            | Where {base; fields} ->
                let base_name = fresh () in
                let copy = infix 4 1 equals
                    (string "var" ^^ blank 1 ^^ base_name)
                    (string "Object.assign"
                    ^^ parens (braces empty ^^ comma ^^ break 1 ^^ emit_use base)) in
                let assignments = fields |> Vector.map (fun (label, v) ->
                     infix 4 1 equals
                        (base_name ^^ dot ^^ string (Name.basename label |> Option.get))
                        (emit_use v)) in
                let fn = string "function" ^^ blank 1 ^^ parens empty ^^ blank 1
                    ^^ surround_separate 4 1 (braces empty) (* NOTE: empty is actually impossible *)
                        lbrace (semi ^^ break 1) rbrace
                        (copy
                        :: (Vector.to_list assignments
                        @ [string "return" ^^ blank 1 ^^ base_name ^^ semi])) in
                parens fn ^^ parens empty

            | With _ -> failwith "TODO"
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

            | Select {selectee; field} -> (* OPTIMIZE: parens not always necessary *)
                prefix 4 0 (parens (emit_use selectee))
                    (dot ^^ string (Name.basename field |> Option.get))

            | Proxy _ -> string "0" (* OPTIMIZE: empty unboxed tuple = erase *)

            | Label label -> (* TODO: Assumes Label node has not been duplicated; stop that *)
                let cont = Program.cont program label in
                emit_fn label cont

            | Const c -> emit_const c

            | Param _ -> failwith "compiler bug: Param in Cfg"
            | Tuple _ -> failwith "compiler bug: Tuple in Cfg"
            | Focus _ -> failwith "compiler bug: Focus in Cfg" in

        let emit_clause ({pat; dest} : Transfer.clause) =
            let emit_pat : Transfer.Pattern.t -> PPrint.document = function
                | Const c -> string "case" ^^ blank 1 ^^ emit_const c
                | Wild -> string "default" in

            let {Cont.pos = _; name = _; universals = _; params = _; stmts; transfer} =
                Program.cont program dest in
            emit_pat pat ^^ colon
            ^^ nest 4 (hardline ^^ emit_transfer dest stmts transfer) in

        let emit_stmt ({term = (vars, expr); pos; typ = _} : Stmt.t) =
            match Vector.length vars with
            | 0 -> emit_expr expr ^^ semi ^^ break 1
            | 1 ->
                let var = Vector.get vars 0 in
                let expr_doc = emit_expr expr in
                if is_inlineable parent var expr
                then begin
                    add_var_expr var expr_doc;
                    empty
                end else begin
                    let name = add_var_name var in
                    infix 4 1 equals (string "var" ^^ blank 1 ^^ name)
                        expr_doc ^^ semi ^^ break 1
                end
            | _ -> failwith ("compiler bug: > 1 vars reached emit_stmt at " ^ Util.span_to_string pos) in

        let stmts = concat_map emit_stmt (Vector.to_list stmts) in
        let transfer = match transfer.term with
            | Goto {callee; universals = _; args} ->
                string "return" ^^ blank 1 ^^ parens (emit_label callee) (* OPTIMIZE: don't always need parens *)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ blank 1) rparen
                    emit_use (Vector.to_list args)

            | Jump {callee; universals = _; args} ->
                string "return" ^^ blank 1 ^^ parens (emit_use callee) (* OPTIMIZE: don't always need parens *)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ blank 1) rparen
                    emit_use (Vector.to_list args)

            | Match {matchee; clauses} ->
                string "switch" ^^ blank 1 ^^ parens (emit_use matchee) ^^ blank 1
                ^^ surround_separate_map 0 0 (braces empty)
                    lbrace (break 1) rbrace
                    emit_clause (Vector.to_list clauses)

            | PrimApp _ -> failwith "TODO"

            | Return (_, args) ->
                string "return" ^^ blank 1 ^^ (Stream.from (Vector.to_source args)
                    |> Stream.map emit_use
                    |> Stream.into Sink.list
                    |> surround_separate 4 0 (brackets empty)
                        lbracket (comma ^^ break 1) rbracket) in
        stmts ^^ transfer ^^ semi

    and emit_block parent stmts transfer =
        surround 4 1 lbrace (emit_transfer parent stmts transfer) rbrace

    and emit_fn label {Cont.pos = _; name = _; universals = _; params; stmts; transfer} =
        let params_doc = surround_separate_map 4 0 (parens empty) lparen (comma ^^ break 1) rparen
            (fun param -> add_var_name (fst param)) (Vector.to_list params) in
        string "function" ^^ blank 1
        ^^ params_doc ^^ blank 1
        ^^ emit_block label stmts transfer in

    let emit_export label =
        let cont = Program.cont program label in
        let name_doc = emit_label label in
        prefix 4 1 (string "var" ^^ blank 1 ^^ name_doc ^^ blank 1 ^^ equals)
            (emit_fn label cont ^^ semi ^^ hardline) in

    Stream.from (Program.exports program)
    |> Stream.into Sink.list
    |> separate_map hardline emit_export

