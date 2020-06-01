theory UPPAAL_Asm_Test
  imports UPPAAL_Asm_AbsInt "HOL-IMP.AExp"
begin

definition myprog :: "instr list" where "myprog \<equiv> [
PUSH 3,
PUSH 42,
instr.LT
]"

definition empty_state :: "cpstate" where "empty_state = ([], [], False, [])"

find_consts "('a \<Rightarrow> bool) \<Rightarrow> 'a set"

find_consts "nat \<Rightarrow> nat list"

fun assemble :: "instr list \<Rightarrow> spaced_program" where
  "assemble listing = SpacedProgram
    (set (upt 0 (length listing)))
    (\<lambda>pc. if pc < length listing then Some (listing ! pc) else None)"

fun spprog :: "spaced_program \<Rightarrow> program" where
  "spprog (SpacedProgram _ prog) = prog"

value "
  let prog = spprog (assemble myprog) in
  let entry = update (0::addr) [empty_state] empty in
  collect_loop prog 2 entry"

class display =
  fixes display :: "'a \<Rightarrow> string"

instantiation nat :: display
begin
fun display_nat :: "nat \<Rightarrow> string" where
  "display_nat n = ''nat''"
instance proof qed
end

instantiation int :: display
begin
fun display_int :: "int \<Rightarrow> string" where
  "display_int n = ''int''"
instance proof qed
end

instantiation bool :: display
begin
fun display_bool :: "bool \<Rightarrow> string" where
  "display_bool True = ''True''" |
  "display_bool False = ''False''"
instance proof qed
end

instantiation instr :: display
begin
fun display_instr :: "instr \<Rightarrow> string" where
  "display_instr (JMPZ a) = ''JMPZ '' @ (display a)" |
  "display_instr ADD = ''ADD''" |
  "display_instr NOT = ''NOT''" |
  "display_instr AND = ''AND''" |
  "display_instr instr.LT = ''LT''" |
  "display_instr instr.LE = ''LE''" |
  "display_instr instr.EQ = ''EQ''" |
  "display_instr (PUSH imm) = ''PUSH '' @ (display imm)" |
  "display_instr POP = ''POP''" |
  "display_instr (LID r) = ''LID '' @ (display r)"|
  "display_instr STORE = ''STORE''" |
  "display_instr (STOREI r imm) = ''STOREI '' @ (display r) @ '' '' @ (display imm)"|
  "display_instr COPY = ''COPY''" |
  "display_instr CALL = ''CALL''" |
  "display_instr RETURN = ''RETURN''" |
  "display_instr HALT = ''HALT''" |
  "display_instr (STOREC n i) = ''STOREC '' @ (display n) @ '' '' @ (display i)" |
  "display_instr (SETF b) = ''SETF '' @ (display b)"
instance proof qed
end

instantiation spaced_program :: display
begin
fun display_spaced_program :: "spaced_program \<Rightarrow> string" where
  "display_spaced_program (SpacedProgram space prog) =
    concat (map (\<lambda>pc. (display pc) @ '' '' @ (display (the (prog pc))) @ [char_of (10::nat)]) (sorted_list_of_set space))"
instance proof qed

definition make_string :: "spaced_program \<Rightarrow> string" where
  "make_string p \<equiv> display p"

value "display (SpacedProgram {0, 1, 2} (\<lambda>a. Some (myprog ! a)))"

typ "spaced_program"

abbreviation init where "init \<equiv> (0, [], [], False, [])"

value "case assemble myprog of (SpacedProgram space prog) \<Rightarrow> step (the (prog (state_pc init))) init"

(*theory Scratch
imports \<comment> \<open>HOL.Archimedean_Field "HOL-Library.Stream"\<close> "HOL-IMP.AExp"
begin*)

value "(\<lambda>_::nat. 3::nat)(5:= 4)"
value "<''y'' := 7::nat>"
value [simp] "map (<''y'' := 7::nat>) [''x'', ''y'']"
definition "my_string \<equiv> STR ''a \<newline> b''"
ML \<open>val str = @{code my_string}
val _ = writeln str
\<close>

end