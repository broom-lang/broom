type USER_ID = interface
    type t
    
    val sudo: t -> t
end

val UserId: USER_ID = module
    type t = Int

    val sudo = fn _: t => 0
end

