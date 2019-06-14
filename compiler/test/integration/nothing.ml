type NOTHING = interface
    type T

    val unusable: fun a: type -> T -> a -> a
end

val Nothing: NOTHING = module
    type T = Unit

    val unusable = fn a: type => fn _ => fn x: a => x
end

