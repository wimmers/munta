theory UPPAAL_Asm_Test
  imports UPPAAL_Asm_AbsInt
begin

definition myprog :: "instr list" where "myprog \<equiv> [
PUSH 3,
PUSH 42,
LT
]"

find_consts "('a \<Rightarrow> bool) \<Rightarrow> 'a set"

find_consts "nat \<Rightarrow> nat list"

fun assemble :: "instr list \<Rightarrow> spaced_program" where
  "assemble listing = SpacedProgram
    (set (upt 0 (length listing)))
    (\<lambda>pc. if pc < length listing then Some (listing ! pc) else None)"

class assembly =
  fixes disassemble :: "'a \<Rightarrow> (addr * instr) list"

instantiation spaced_program :: assembly
begin
fun disassemble_spaced_program :: "spaced_program \<Rightarrow> (addr * instr) list" where
  "disassemble_spaced_program (SpacedProgram space prog) =
    map (\<lambda>pc. (pc, the (prog pc))) (sorted_list_of_set space)"
instance proof
qed
end

value "disassemble (assemble myprog)"

abbreviation init where "init \<equiv> (0, [], [], False, [])"

value "case assemble myprog of (SpacedProgram space prog) \<Rightarrow> step (the (prog (state_pc init))) init"

end