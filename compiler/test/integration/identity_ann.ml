val identity: fun a: type -> a -> a = fn a: type => fn x: a => x
val n: Int = identity (type Int) 5

