theory UPPAAL_Asm_Clocks
  imports Timed_Automata Normalized_Zone_Semantics UPPAAL_Asm Complex_Main
begin

(*
abbreviation conv_ac :: "('a, int) acconstraint \<Rightarrow> ('a, real) acconstraint" where
  "conv_ac \<equiv> map_acconstraint id real_of_int"
*)

datatype 't instrc =
  INSTR instr |
  CEXP "(nat, 't) acconstraint"

fun stepc :: "'t instrc \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state option" where
  "stepc (INSTR instr) u s =
    (case step instr s of
       Some s' \<Rightarrow> Some s'
     | None \<Rightarrow> None)" |
  "stepc (CEXP cc) u (pc, st, m, f, rs) = Some (pc + 1, st, m, u \<turnstile>\<^sub>a cc, rs)"

type_synonym 't programc = "addr \<Rightarrow> 't instrc option"

(*
fun stepsc :: "'t programc \<Rightarrow> fuel \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state option" where
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
*)

inductive stepsc :: "'t programc \<Rightarrow> fuel \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "stepsc prog (Suc n) u start start" | (*
  "stepsc prog (Suc n) u s s'" if
    "stepc cmd u (pc, st, m, f, rs) = Some s'"
    "stepsc prog n u s (pc, st, m, f, rs)"
    "prog pc = Some cmd" *)
  "stepsc prog (Suc n) u (pc, st, m, f, rs) s'" if
    "stepc cmd u (pc, st, m, f, rs) = Some s"
    "prog pc = Some cmd"
    "stepsc prog n u s s'"

inductive visitedc :: "'t programc \<Rightarrow> fuel \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state \<Rightarrow> addr list \<Rightarrow> bool" where
  "visitedc prog (Suc n) u start start []" | (*
  "stepsc prog (Suc n) u s s'" if
    "stepc cmd u (pc, st, m, f, rs) = Some s'"
    "stepsc prog n u s (pc, st, m, f, rs)"
    "prog pc = Some cmd" *)
  "visitedc prog (Suc n) u (pc, st, m, f, rs) s' (pcs @ [pc])" if
    "stepc cmd u (pc, st, m, f, rs) = Some s"
    "prog pc = Some cmd"
    "visitedc prog n u s s' pcs"

(*
inductive visited :: "'t programc \<Rightarrow> fuel \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state \<Rightarrow> (nat, 't) cconstraint \<Rightarrow> bool" where
  "visited prog (Suc n) u start start []" | (*
  "stepsc prog (Suc n) u s s'" if
    "stepc cmd u (pc, st, m, f, rs) = Some s'"
    "stepsc prog n u s (pc, st, m, f, rs)"
    "prog pc = Some cmd" *)
  "visited prog (Suc n) u (pc, st, m, f, rs) s' (ac # cc)" if
    "stepc (CEXP ac) u (pc, st, m, f, rs) = Some s"
    "prog pc = Some (CEXP ac)"
    "visited prog n u s s' S" |
  "visited prog (Suc n) u (pc, st, m, f, rs) s' cc" if
    "stepc (INSTR instr) u (pc, st, m, f, rs) = Some s"
    "prog pc = Some (INSTR instr)"
    "visited prog n u s s' cc"
*)

definition "stepst prog n u start \<equiv> \<lambda> (pc, st, m, f, rs).
  stepsc prog n u start (pc, st, m, f, rs) \<and> prog pc = Some (INSTR HALT)"

(*
inductive stepsc :: "'t programc \<Rightarrow> fuel \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
  "stepsc prog (Suc n) u (pc, st, m, f, rs) (pc, st, m, f, rs)" if "prog pc = Some (INSTR HALT)" |
  "stepsc prog (Suc n) u start end" if
    "stepsc prog n u start (pc, st, m, f, rs)"
    "prog pc = Some cmd" "cmd \<noteq> INSTR HALT" "stepc cmd u (pc, st, m, f, rs) = Some end"
*)

fun strip :: "'t instrc \<Rightarrow> instr" where
  "strip (INSTR instr) = instr" |
  "strip _ = HALT"

fun stripf :: "'t instrc \<Rightarrow> instr" where
  "stripf (INSTR instr) = instr" |
  "stripf _ = SETF False"

fun stript :: "'t instrc \<Rightarrow> instr" where
  "stript (INSTR instr) = instr" |
  "stript _ = SETF True"

end