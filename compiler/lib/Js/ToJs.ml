open Streaming
open Cps
open PPrint

(* OPTIMIZE: Get rid of intermediate lists *)

let emit program =
    let usecounts = Program.usecounts program in
    let usecount id = Expr.Id.HashMap.get_exn id usecounts in

    let counter = ref 0 in
    let fresh () =
        let i = !counter in
        counter := i + 1;
        string ("y$" ^ Int.to_string i) in

    let expr_vars = Expr.Id.Hashtbl.create 0 in
    let define (id : Expr.Id.t) =
        let doc = string ("x$" ^ Int.to_string (id :> int)) in
        Expr.Id.Hashtbl.add expr_vars id doc;
        doc in
    let expr_var = Expr.Id.Hashtbl.find_opt expr_vars in

    let param_docs = Cont.Id.Hashtbl.create 0 in
    let add_param_docs label fn_name n =
        let docs = Stream.iota n
            |> Stream.map (fun i -> fn_name ^^ underscore ^^ string (Int.to_string i))
            |> Stream.into (Vector.sink ()) in
        Cont.Id.Hashtbl.add param_docs label docs;
        docs in
    let emit_param label i = Vector.get (Cont.Id.Hashtbl.find param_docs label) i in

    let emit_label (label : Cont.Id.t) =
        let {name; _} : Cont.t = Program.cont program label in
        let prefix = match name with
            | Some name -> Name.to_doc name
            | None -> string "fn" in
        prefix ^^ dollar ^^ string (Int.to_string (label :> int)) in

    let emit_const : Const.t -> PPrint.document = function
        | Int n -> string (Int.to_string n) in

    let rec emit_transfer parent (transfer : Transfer.t) =
        let stmts = CCVector.create () in

        let rec emit_expr id =
            match expr_var id with
            | Some var -> var
            | None ->
                let {Expr.pos = _; typ = _; cont = parent'; term} = Program.expr program id in
                (* assert (Cont.Id.equal (Option.get parent') parent); FIXME *)
                let var = if usecount id > 1 then Some (define id) else None in
                let expr = match term with
                    | Values vals -> (* OPTIMIZE: unbox tuples (in an earlier pass) *)
                        surround_separate_map 4 0 (brackets empty)
                            lbracket (comma ^^ break 1) rbracket
                            emit_expr (Vector.to_list vals)

                    | Focus {focusee; index} -> (* OPTIMIZE: parens not always necessary *)
                        parens (emit_expr focusee) ^^ brackets (string (Int.to_string index))

                    | Record fields ->
                        surround_separate_map 4 0 (braces empty)
                            lbrace (comma ^^ break 1) rbrace
                            (fun (label, field) ->
                                Name.to_doc label ^^ colon ^^ blank 1 ^^ emit_expr field)
                            (Vector.to_list fields)

                    | Where {base; fields} ->
                        let base_name = fresh () in
                        let stmt = infix 4 1 equals
                            (string "var" ^^ blank 1 ^^ base_name)
                            (string "Object.assign"
                            ^^ parens (braces empty ^^ comma ^^ break 1 ^^ emit_expr base)) in
                        CCVector.push stmts stmt;
                        Vector.iter (fun (label, field) ->
                            let stmt = infix 4 1 equals (base_name ^^ dot ^^ Name.to_doc label)
                                (emit_expr field) in
                            CCVector.push stmts stmt
                        ) fields;
                        base_name

                    | With {base; label; field} ->
                        let base_name = fresh () in
                        let stmt = infix 4 1 equals
                            (string "var" ^^ blank 1 ^^ base_name)
                            (string "Object.assign"
                            ^^ parens (braces empty ^^ comma ^^ break 1 ^^ emit_expr base)) in
                        CCVector.push stmts stmt;
                        let stmt = infix 4 1 equals (base_name ^^ dot ^^ Name.to_doc label)
                            (emit_expr field) in
                        CCVector.push stmts stmt;
                        base_name

                    | Select {selectee; field} -> (* OPTIMIZE: parens not always necessary *)
                        prefix 4 0 (parens (emit_expr selectee)) (dot ^^ Name.to_doc field)

                    | Proxy _ -> string "0" (* OPTIMIZE: empty unboxed tuple = erase *)

                    | Param {label; index} -> emit_param label index
                    | Label label ->
                        let cont = Program.cont program label in
                        let name_doc = emit_label label in
                        emit_fn label name_doc cont

                    | Const c -> emit_const c in
                (match var with
                | Some var ->
                    let stmt = prefix 4 1
                        (string "var" ^^ blank 1 ^^ var ^^ blank 1 ^^ equals) expr in
                    CCVector.push stmts stmt;
                    var
                | None -> expr) in

        let emit_clause {Transfer.pat; dest} =
            let emit_pat = function
                | Pattern.Const c -> emit_const c
                | Wild -> string "default" in

            let {Cont.pos = _; name = _; universals = _; params; body} = Program.cont program dest in
            string "case" ^^ blank 1 ^^ emit_pat pat ^^ colon ^^ blank 1
            ^^ emit_block dest body ^^ semi in

        let transfer = match transfer.term with
            | Goto {callee; universals = _; args} ->
                string "return" ^^ blank 1 ^^ parens (emit_label callee) (* OPTIMIZE: don't always need parens *)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ blank 1) rparen
                    emit_expr (Vector.to_list args)

            | Jump {callee; universals = _; args} ->
                string "return" ^^ blank 1 ^^ parens (emit_expr callee) (* OPTIMIZE: don't always need parens *)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ blank 1) rparen
                    emit_expr (Vector.to_list args)

            | Match {matchee; state; clauses} ->
                string "switch" ^^ blank 1 ^^ parens (emit_expr matchee) ^^ blank 1
                ^^ surround_separate_map 0 0 (braces empty)
                    lbrace (break 1 ^^ string "break" ^^ semi ^^ break 1) rbrace
                    emit_clause (Vector.to_list clauses)

            | Return (_, args) ->
                string "return" ^^ blank 1 ^^ (Stream.from (Vector.to_source args)
                    |> Stream.map emit_expr
                    |> Stream.into Sink.list
                    |> surround_separate 4 0 (brackets empty)
                        lbracket (comma ^^ break 1) rbracket) in

        concat_map (fun stmt -> stmt ^^ semi ^^ break 1) (CCVector.to_list stmts)
        ^^ transfer ^^ semi

    and emit_block parent transfer =
        surround 4 1 lbrace (emit_transfer parent transfer) rbrace

    and emit_fn label name_doc {Cont.pos = _; name = _; universals = _; params; body} =
        let param_docs = add_param_docs label name_doc (Vector.length params) in
        string "function" ^^ blank 1
        ^^ surround_separate 4 0 (parens empty) lparen (comma ^^ break 1) rparen
            (Vector.to_list param_docs) ^^ blank 1
        ^^ emit_block label body in

    let emit_export label =
        let cont = Program.cont program label in
        let name_doc = emit_label label in
        prefix 4 1 (string "var" ^^ blank 1 ^^ name_doc ^^ blank 1 ^^ equals)
            (emit_fn label name_doc cont ^^ semi ^^ hardline) in

    Stream.from (Program.exports program)
    |> Stream.into Sink.list
    |> separate_map hardline emit_export

