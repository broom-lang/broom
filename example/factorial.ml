let val fact = fn n =>
        if n == 0
        then 1
        else n * fact (n - 1)
in  fact 5
end
