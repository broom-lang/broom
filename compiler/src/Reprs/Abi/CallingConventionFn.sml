signature CALLING_CONVENTION = sig
    structure Register : REGISTER

    type internal = Register.t vector

    type foreign =
        { args : Register.t vector
        , retVal : Register.t vector
        , callerSaves : Register.t vector
        , calleeSaves : Register.t vector }
end

functor CallingConventionFn (Register : REGISTER) :> CALLING_CONVENTION
    where type Register.t = Register.t
= struct
    structure Register = Register

    type internal = Register.t vector

    type foreign =
        { args : Register.t vector
        , retVal : Register.t vector
        , callerSaves : Register.t vector
        , calleeSaves : Register.t vector }
end

