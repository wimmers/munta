theory More_Methods
  imports Main Reordering_Quantifiers "HOL-Eisbach.Eisbach" ML_Util
begin

ML \<open>fun mini_ex ctxt = SIMPLE_METHOD (mini_ex_tac ctxt 1)\<close>
ML \<open>fun defer_ex ctxt = SIMPLE_METHOD (defer_ex_tac ctxt 1)\<close>

method_setup mini_existential =
  \<open>Scan.succeed mini_ex\<close> \<open>Miniscope existential quantifiers\<close>
method_setup defer_existential =
  \<open>Scan.succeed defer_ex\<close> \<open>Rotate first conjunct under existential quantifiers to last position\<close>

method mini_ex = ((simp only: ex_simps[symmetric])?, mini_existential, (simp)?)
method defer_ex = ((simp only: ex_simps[symmetric])?, defer_existential, (simp)?)
method defer_ex' = (defer_existential, (simp)?)

method solve_triv =
  fo_assumption | refl_match | simp; fail | assumption | (erule image_eqI[rotated], solve_triv)

method solve_ex_triv2 = (((rule exI)+)?, (rule conjI)+, solve_triv)

method solve_conj_triv = solve_triv | (rule conjI, solve_conj_triv)

method solve_conj_triv2 =
  (match conclusion in
    "_ \<and> _" \<Rightarrow> \<open>rule conjI, solve_conj_triv2\<close>
  \<bar> _ \<Rightarrow> solve_triv)

method solve_ex_triv = (((rule exI)+)?, solve_conj_triv)

named_theorems intros
named_theorems elims

lemmas [intros] =
  allI ballI exI bexI[rotated] conjI impI
and [elims] =
  bexE exE bexE conjE impE

method intros uses add  = (intro add intros)
method elims  uses add  = (elim  add elims)

text \<open>Test case\<close>
lemma all_mp:
  "\<forall> x. P x \<longrightarrow> R x" if "\<forall> x. P x \<longrightarrow> Q x" "\<And> x. P x \<Longrightarrow> Q x \<Longrightarrow> R x"
  using that by (intros; elims add: allE)

method rprem =
  (match premises in R: _ \<Rightarrow> \<open>rule R\<close>)

text \<open>Test case for @{method rprem}.\<close>
lemma
  "A \<Longrightarrow> (A \<Longrightarrow> C) \<Longrightarrow> (A \<Longrightarrow> B) \<Longrightarrow> B"
  by rprem

end (* Theory *)