signature REGISTER_ENV = sig
    type t

    val empty : t
end

functor RegisterEnvFn (Register : REGISTER) :> REGISTER_ENV = struct
    type t = { registers : Register.t Cps.Program.Map.t
             , stack : int Cps.Program.Map.t }

    val empty = {registers = Cps.Program.Map.empty, stack = Cps.Program.Map.empty}
end

