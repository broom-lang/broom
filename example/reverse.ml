let newtype IntList = Cons (Int, IntList) | Nil
    val reverse = fn xs =>
        let rec loop = fn ys => fn xs =>
                         case xs of
                             IntList (Cons (x, rxs))) => loop (Cons x ys) rxs
                             IntList Nil => ys
                         end
        in  loop Nil xs
        end
in  reverse (IntList (Cons (1, IntList (Cons (2, IntList (Cons (3, IntList Nil)))))))
end
