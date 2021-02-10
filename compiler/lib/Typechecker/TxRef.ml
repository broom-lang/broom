module Id = Id.Make ()

module Subst = struct
    type t = Obj.t Id.HashMap.t

    let current = ref Id.HashMap.empty
end

type 'a t = Id.t

let equal r r' = Id.equal (Obj.magic r) (Obj.magic r')

let hash r = Id.hash (Obj.magic r)

let ref v =
    let id = Id.fresh () in
    Subst.current := Id.HashMap.add id (Obj.repr v) !Subst.current;
    Obj.magic id

let (!) (id : Id.t) = Obj.obj (Id.HashMap.get_exn (Obj.magic id) !Subst.current)

let (:=) (id : Id.t) v =
    Subst.current := Id.HashMap.add (Obj.magic id) (Obj.repr v) Stdlib.(!Subst.current)

type 'a txref = 'a t

module type T = sig type t end

module Hashtbl = struct
    module Make (T : T) = CCHashtbl.Make (struct
        type t = T.t txref

        let equal = equal
        let hash = hash
    end)
end

module HashSet = struct
    module Make (T : T) = CCHashSet.Make (struct
        type t = T.t txref

        let equal = equal
        let hash = hash
    end)
end

module Set = struct
    type 'a t = Id.Set.t

    let empty = Id.Set.empty
    let add v set = Id.Set.add (Obj.magic v) set
    let remove v set = Id.Set.remove (Obj.magic v) set
    let is_empty = Id.Set.is_empty
    let mem v set = Id.Set.mem (Obj.magic v) set

    let iter = Id.Set.iter
end

