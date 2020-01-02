structure X64Register :> REGISTER = struct
    (* Using DWARF register number mapping. *)

    type t = int

    val toString =
        fn 0 => "%rax"
         | 1 => "%rdx"
         | 2 => "%rcx"
         | 3 => "%rbx"
         | 4 => "%rsi"
         | 5 => "%rdi"
         | 6 => "%rbp"
         | 7 => "%rsp"
         | 8 => "%r8"
         | 9 => "%r9"
         | 10 => "%r10"
         | 11 => "%r11"
         | 12 => "%r12"
         | 13 => "%r13"
         | 14 => "%r14"
         | 15 => "%r15"
         | 16 => "%rip"

    val toDoc = PPrint.text o toString
end

