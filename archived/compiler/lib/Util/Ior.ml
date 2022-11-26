type ('l, 'r) t = 
    | Left of 'l
    | Right of 'r
    | Both of 'l * 'r

let bimap f g = function
    | Left l -> Left (f l)
    | Right r -> Right (g r)
    | Both (l, r) -> Both (f l, g r)

let map f v = bimap f f v

let biter f g = function
    | Left l -> f l
    | Right r -> g r
    | Both (l, r) -> f l; g r

