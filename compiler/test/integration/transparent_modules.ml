val Prelude = module
    val Fn = module
        val identity = fn a: Type => fn x: a => x
    end

    val Integer = module
        type T = Int

        val zero: T = 0
    end
end

val n: Prelude.Integer.T = Prelude.Fn.identity Prelude.Integer.zero

