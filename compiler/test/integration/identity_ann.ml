val identity: fun a: type -> a -> a = fn _ => fn x => x
val n: Int = identity (type Int) 5

