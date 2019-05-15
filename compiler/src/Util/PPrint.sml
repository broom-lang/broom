infixr 6 <+>
infixr 6 <++>

signature PPRINT = sig
    include MONOID

    (* Whitespace: *)
    val space : t
    val newline : t

    (* Appending with whitespace: *)
    val <+> : t * t -> t (* space in between *)
    val <++> : t * t -> t (* newline in between *)

    (* Indentation: *)
    val nest : int -> t -> t
    val align : t -> t

    (* Punctuation: *)
    val comma : t
    val semi : t
    val punctuate : t -> t vector -> t

    (* Delimiters: *)
    val lParen : t
    val rParen : t
    val parens : t -> t
    val lBracket : t
    val rBracket : t
    val brackets : t -> t
    val lBrace : t
    val rBrace : t
    val braces : t -> t

    (* Wrap basic types: *)
    val text : string -> t
    val int : int -> t
    val word : word -> t
    val real : real -> t
    val char : char -> t
   
    (* To a string that fits in `pageWidth` columns: *)
    val pretty : (* pageWidth: *) int -> t -> string
end

structure PPrint :> PPRINT = struct
    val inf = 99999999

    type state = { index: int
                 , col: int
                 , width: int
                 , effWidth: int }

    fun assocIndex {index = _, col = c, width = w, effWidth = ew} i =
        {index = i, col = c, width = w, effWidth = ew}

    fun mapIndex f {index = i, col = c, width = w, effWidth = ew} =
        {index = f i, col = c, width = w, effWidth = ew}

    fun assocCol {index = i, col = _, width = w, effWidth = ew} c =
        {index = i, col = c, width = w, effWidth = ew}

    fun assocEffWidth {index = i, col = c, width = w, effWidth = _} ew =
        {index = i, col = c, width = w, effWidth = ew}

    type t = { minWidth: int
             , minWidthWNL: int
             , run: state -> int * string }

    fun isEmpty {minWidth = mwo, minWidthWNL = mw, ...} =
        mwo = 0 andalso mw = inf

    fun mapRun f {minWidth = mwo, minWidthWNL = mw, run = run} =
        {minWidth = mwo, minWidthWNL = mw, run = f run}

    fun strMul 0 s = ""
      | strMul n s = s ^ strMul (n - 1) s

    fun text s = { minWidth = String.size s
                 , minWidthWNL = inf
                 , run = (fn ({col = c, ...}: state) => (c + size s, s)) }

    val empty = text ""

    val space = text " "
    val comma = text ","
    val semi = text ";"
    val lParen = text "("
    val rParen = text ")"
    val lBracket = text "["
    val rBracket = text "]"
    val lBrace = text "{"
    val rBrace = text "}"

    val newline = { minWidth = 0
                  , minWidthWNL = 0
                  , run = (fn ({index = i, ...}: state) => (i, "\n" ^ strMul i " ")) }

    fun nest n doc =
            mapRun (fn run => fn st => run (mapIndex (fn i => i + n) st)) doc

    fun {minWidth = mwo, minWidthWNL = mw, run = run} <>
        {minWidth = mwo', minWidthWNL = mw', run = run'} =
            let val mwo'' = Int.min (mw, mwo + mwo')
                val mw'' = Int.min (mw, mwo + mw')
                fun run'' (st as {index = i, col = c, width = w, effWidth = ew}) =
                        let val ew' = Int.max(w - mw', ew - mwo')
                            val (c', s) = run (assocEffWidth st ew')
                            val (c'', s') = run' (assocCol st c')
                        in (c'', s ^ s') end
            in {minWidth = mwo'', minWidthWNL = mw'', run = run''} end

    fun parens doc = lParen <> doc <> rParen
    fun brackets doc = lBracket <> doc <> rBracket
    fun braces doc = lBrace <> doc <> rBrace

    fun align doc =
        mapRun (fn run => fn st => run (assocIndex st (#col st))) doc

    fun l <+> r = if isEmpty l then r
                  else if isEmpty r then l
                  else l <> space <> r

    fun l <++> r = if isEmpty l then r
                   else if isEmpty r then l
                   else l <> newline <> r

    fun punctuate sep docs =
        case Vector.length docs
        of 0 => empty
         | 1 => Vector.sub (docs, 0)
         | _ =>
           let fun step (acc, doc) = doc <> sep <> acc
           in VectorSlice.foldl step (Vector.sub (docs, 0)) (VectorSlice.slice (docs, 1, NONE))
           end

    val int = text o Int.toString
    val word = text o Word.toString
    val real = text o Real.toString
    val char = text o Char.toString

    fun pretty pageWidth (doc: t) =
        #2 (#run doc { index = 0, col = 0,
                       width = pageWidth, effWidth = pageWidth }) ^ "\n"
end

signature TO_DOC = sig
    type t
    val toDoc : t -> PPrint.t
end

functor ToDocFromToString (ToString: TO_STRING) :> TO_DOC where type t = ToString.t = struct
    type t = ToString.t
    val toDoc = PPrint.text o ToString.toString
end

functor ToStringFromToDoc (ToDoc: TO_DOC) :> TO_STRING where type t = ToDoc.t = struct
    type t = ToDoc.t
    val toString = PPrint.pretty 80 o ToDoc.toDoc
end

