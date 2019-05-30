val identity = fn a: type => fn x: a => x
val n: Int = identity (type Int) 5

