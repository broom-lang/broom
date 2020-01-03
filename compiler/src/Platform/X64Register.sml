structure X64Register = struct
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

    val eq = op=

    val rax = 0
    val rdx = 1
    val rcx = 2
    val rbx = 3
    val rsi = 4
    val rdi = 5
    val rbp = 6
    val rsp = 7
    val r8 = 8
    val r9 = 9
    val r10 = 10
    val r11 = 11
    val r12 = 12
    val r13 = 13
    val r14 = 14
    val r15 = 15
    val rip = 16
end

