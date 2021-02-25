signature TWOBIT_MAP = sig
    type t
  
    val pack : Word8Vector.vector -> t
    val unpack : t -> Word8Vector.vector
    val bytes : t -> Word8Vector.vector
    val toDoc : t -> PPrint.t
end

structure TwobitMap :> TWOBIT_MAP = struct
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    structure Word2 :> sig
        type word

        val fromWord8 : Word8.word -> word
        val toWord8 : word -> Word8.word
    end = struct
        type word = Word8.word

        val max = Word8.fromLargeWord 0w3

        fun fromWord8 n = if n <= max then n else raise Domain

        val toWord8 = Fn.identity
    end

    structure QuadWord2 :> sig
        type t

        val length : int
        val fromWord8 : Word8.word -> t
        val toWord8 : t -> Word8.word
        val sub : t * int -> Word2.word
        val update : t * int * Word2.word -> t
    end = struct
        type t = Word8.word

        val length = 4
        val maxIndex = length - 1
        val mask = Word8.fromLargeWord 0w3

        val fromWord8 = Fn.identity
        val toWord8 = Fn.identity

        fun indexShift i = Word.fromInt (maxIndex - i) * 0w2

        fun sub (vs, i) =
            if i < length
            then let val shift = indexShift i
                 in Word2.fromWord8 (Word8.andb (Word8.>> (vs, shift), mask))
                 end
            else raise Subscript

        fun update (vs, i, v) =
            if i < length
            then let val shift = indexShift i
                     val vs = Word8.andb (vs, Word8.notb (Word8.<< (mask, shift)))
                 in Word8.orb (vs, Word8.<< (Word2.toWord8 v, shift))
                 end
            else raise Subscript
    end

    type t = {bytes : Word8Vector.vector, len : int}

    fun ceilDiv (a, b) =
        let val quotient = a div b
            val remainder = a mod b
            (* OPTIMIZE: Remove branch: *)
        in  if remainder > 0 then quotient + 1 else quotient
        end

    fun sub ({bytes, len}, i) =
        if i < len
        then let val majorIndex = i div QuadWord2.length
                 val minorIndex = i mod QuadWord2.length
                 val quad = QuadWord2.fromWord8 (Word8Vector.sub (bytes, majorIndex))
             in Word2.toWord8 (QuadWord2.sub (quad, minorIndex))
             end
        else raise Subscript

    fun pack vs =
        let val len = Word8Vector.length vs
            val byteCount = ceilDiv (len, QuadWord2.length)

            fun step byteIndex =
                let val i = byteIndex * QuadWord2.length
                    fun loop j quad =
                        if j < QuadWord2.length andalso i + j < len
                        then loop (j + 1)
                                  (QuadWord2.update (quad, j, Word2.fromWord8 (Word8Vector.sub (vs, i + j))))
                        else quad
                in QuadWord2.toWord8 (loop 0 (QuadWord2.fromWord8 0w0))
                end
            val bytes = Word8Vector.tabulate (byteCount, step)
        in {bytes, len}
        end

    fun unpack (vs as {bytes = _, len}) =
        Word8Vector.tabulate (len, fn i => sub (vs, i))

    val bytes : t -> Word8Vector.vector = #bytes

    fun toDoc (vs : t) =
        let val doc =
                if #len vs = 0
                then PPrint.empty
                else let val vs = unpack vs
                         fun step (v, acc) =
                             acc <> PPrint.comma <+> PPrint.text (Word8.toString v)
                     in Word8VectorSlice.foldl step
                                               (PPrint.text (Word8.toString (Word8Vector.sub (vs, 0))))
                                               (Word8VectorSlice.slice (vs, 1, NONE))
                     end
        in PPrint.brackets doc
        end
end

