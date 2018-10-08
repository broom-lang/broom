let val fact: Int -> Int = fn n: Int =>
        if n == 0
        then 1
        else n * fact (n - 1)
in  fact 5
end
