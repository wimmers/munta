theory UPPAAL_Asm_Clocks
  imports Timed_Automata Normalized_Zone_Semantics UPPAAL_Asm Complex_Main
begin

abbreviation conv_cc :: "('a, int) cconstraint \<Rightarrow> ('a, real) cconstraint" where
  "conv_cc \<equiv> map (map_acconstraint id real_of_int)"

datatype instrc =
  INSTR instr |
  CEXP "(nat, int) cconstraint"

fun stepc :: "instrc \<Rightarrow> (nat, real) cval \<Rightarrow> state \<Rightarrow> state option" where
  "stepc (INSTR instr) u s =
    (case step instr s of
       Some s' \<Rightarrow> Some s'
     | None \<Rightarrow> None)" |
  "stepc (CEXP cc) u (rs, pc, st, m, f) = Some (rs, pc, int_of (u \<turnstile> conv_cc cc) # st, m, f)"

type_synonym programc = "addr \<Rightarrow> instrc option"

fun stepsc :: "programc \<Rightarrow> fuel \<Rightarrow> (nat, real) cval \<Rightarrow> state \<Rightarrow> state option" where
  "stepsc _ 0 _ _ = None" |
  "stepsc prog (Suc n) u (pc, st, m, f, rs) =
    (case prog pc of
       Some instr \<Rightarrow>
         if instr = INSTR HALT
         then Some (pc, st, m, f, rs)
         else
           case stepc instr u (pc, st, m, f, rs) of
             Some s \<Rightarrow> stepsc prog n u s
           | None \<Rightarrow> None
     | None \<Rightarrow> None)"

fun strip :: "instrc \<Rightarrow> instr" where
  "strip (INSTR instr) = instr" |
  "strip _ = HALT"

fun stripf :: "instrc \<Rightarrow> instr" where
  "stripf (INSTR instr) = instr" |
  "stripf _ = SETF False"

fun stript :: "instrc \<Rightarrow> instr" where
  "stript (INSTR instr) = instr" |
  "stript _ = SETF True"

end