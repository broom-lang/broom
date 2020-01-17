structure Label = struct
    structure Super = Id(struct end)
    open Super

    fun toDoc id = PPrint.<> (PPrint.text "$", Super.toDoc id)
end

