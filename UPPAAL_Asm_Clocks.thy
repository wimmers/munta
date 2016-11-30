theory UPPAAL_Asm_Clocks
  imports Timed_Automata Normalized_Zone_Semantics UPPAAL_Asm Complex_Main
begin

abbreviation conv_cc :: "('a, int) cconstraint \<Rightarrow> ('a, real) cconstraint" where
  "conv_cc \<equiv> map (map_acconstraint id real_of_int)"

datatype instrc =
  INSTR instr |
  STOREC nat int |
  CEXP "(nat, int) cconstraint"

type_synonym cstate = "rstate \<times> state"

fun stepc :: "instrc \<Rightarrow> (nat, real) cval \<Rightarrow> cstate \<Rightarrow> cstate option" where
  "stepc (INSTR instr) u (rs, s) =
    (case step instr s of
       Some s' \<Rightarrow> Some (rs, s')
     | None \<Rightarrow> None)" |
  "stepc (STOREC c d) u (rs, s) = Some (rs(c := Some d), s)" |
  "stepc (CEXP cc) u (rs, pc, st, m, f) = Some (rs, pc, int_of (u \<turnstile> conv_cc cc) # st, m, f)"

type_synonym programc = "addr \<Rightarrow> instrc option"

fun stepsc :: "programc \<Rightarrow> fuel \<Rightarrow> (nat, real) cval \<Rightarrow> cstate \<Rightarrow> cstate option" where
  "stepsc _ 0 _ _ = None" |
  "stepsc prog (Suc n) u (rs, pc, st, m, f) =
    (case prog pc of
       Some instr \<Rightarrow>
         if instr = INSTR HALT
         then Some (rs, pc, st, m, f)
         else
           case stepc instr u (rs, pc, st, m, f) of
             Some s \<Rightarrow> stepsc prog n u s
           | None \<Rightarrow> None
     | None \<Rightarrow> None)"

end