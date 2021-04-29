module Log = struct
    type t =
        { mutable nesting : int
        ; refs : Obj.t ref CCVector.vector
        ; vals : Obj.t CCVector.vector }

    let log () =
        { nesting = 0
        ; refs = CCVector.create ()
        ; vals = CCVector.create () }

    let record : t -> 'a ref -> unit = fun log ref ->
        let ref = Obj.magic ref in
        CCVector.push log.refs ref;
        CCVector.push log.vals !ref

    let memento log = CCVector.length log.refs

    let abort =
        let rec loop refs vals memento i =
            if i >= memento
            then begin
                let ref = CCVector.get refs i in
                let v = CCVector.get vals i in
                ref := v;
                loop refs vals memento (i - 1)
            end in
        fun ({nesting = _; refs; vals} as log) memento ->
            loop refs vals memento (CCVector.length refs - 1);
            CCVector.truncate refs memento;
            CCVector.truncate vals memento;
            log.nesting <- log.nesting - 1

    let commit log memento =
        let nesting' = log.nesting - 1 in
        log.nesting <- nesting';
        if nesting' = 0 then begin
            CCVector.truncate log.refs memento;
            CCVector.truncate log.vals memento;
        end

    let transaction log body =
        let mem = memento log in
        try
            log.nesting <- log.nesting + 1;
            let res = body () in
            commit log mem;
            res
        with
        | exn ->
            abort log mem;
            raise exn
end

let log = Log.log ()

let transaction body = Log.transaction log body

module Ref = struct
    type 'a t = 'a ref

    let ref = ref

    let (!) = Stdlib.(!)

    let (:=) ref v =
        if log.nesting > 0
        then Log.record log ref;
        ref := v

    let eq : 'a t -> 'a t -> bool = (==)
end

type 'a ref = 'a Ref.t

let ref = Ref.ref
let (!) = Ref.(!)
let (:=) = Ref.(:=)

module Queue = struct
    type 'a t = {front : 'a list ref; back : 'a list ref}

    let create () = {front = ref []; back = ref []}

    let ensure_front {front; back} = match !front with
        | _ :: _ -> ()
        | [] ->
            front := List.rev !back;
            back := []

    let push {front = _; back} v = back := v :: !back

    let pop ({front; back = _} as q) =
        ensure_front q;
        match !front with
        | v :: vs -> front := vs; Some v
        | [] -> None
end

