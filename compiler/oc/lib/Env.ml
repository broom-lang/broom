module Bindings = Map.Make(Name)

type t = FcType.t Bindings.t

let interactive () = Bindings.empty

let eval () = Bindings.empty

let add = Bindings.add

let find = Bindings.find

