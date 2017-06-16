theory TA_More
  imports Timed_Automata DBM_Operations "IICF/IICF"
begin

text \<open>
  Additional Lemmas on Timed Automata that do not belong to a particular other part of the
  formalization.
\<close>

fun extend_cc where
  "extend_cc cc [] = cc"
| "extend_cc cc (c # cs) = GE c 0 # extend_cc cc cs"

lemma collect_clock_pairs_extend_cc:
  "collect_clock_pairs (extend_cc cc cs) = collect_clock_pairs cc \<union> {(c, 0) | c. c \<in> set cs}"
  by (induction cs) (auto simp: collect_clock_pairs_def)

definition
  "extend_ta A xs \<equiv> (trans_of A, \<lambda> l. extend_cc (inv_of A l) xs)"

(* XXX Interestingly, this does not go through without the IICF simpset *)
lemma clk_set_extend_ta:
  "clk_set (extend_ta A xs) = clk_set A \<union> set xs"
  unfolding extend_ta_def clkp_set_def inv_of_def trans_of_def
  by (auto simp: collect_clki_def collect_clock_pairs_extend_cc)

lemma extend_cc_iff:
  "u \<turnstile> extend_cc cc cs \<longleftrightarrow> u \<turnstile> cc" if "\<forall> c. u c \<ge> 0"
  using that by (induction cs) force+

lemma [simp]:
  "trans_of (extend_ta A cs) = trans_of A"
  unfolding extend_ta_def trans_of_def by simp

lemma [simp]:
  "inv_of (extend_ta A cs) l = extend_cc (inv_of A l) cs"
  unfolding extend_ta_def inv_of_def by simp

lemma reset_V:
  "\<forall> c. ([r\<rightarrow>0]u) c \<ge> 0" if "\<forall> c. u c \<ge> 0"
  using that apply safe
  subgoal for c
    by (cases "c \<in> set r") (auto simp add: reset_set1 reset_set11)
  done

lemma delay_V:
  "\<forall> c. (u \<oplus> d) c \<ge> 0" if "\<forall> c. u c \<ge> 0" "(d :: 't :: time) \<ge> 0"
  using that unfolding cval_add_def by auto

lemma extend_ta_iff:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<longleftrightarrow> extend_ta A cs \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" if "\<forall> c. u c \<ge> 0"
  using that apply safe
     apply (force simp: extend_cc_iff reset_V intro: step_a.intros elim!: step_a.cases)
    apply (force simp add: extend_cc_iff delay_V)
  apply (cases rule: step_a.cases, assumption)
   apply (auto simp add: reset_V extend_cc_iff intro: step_a.intros)
  using extend_cc_iff delay_V by fast

lemma steps_iffI:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<longleftrightarrow> A' \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" if
  "\<And> l u l' u'. P u \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<longleftrightarrow> A' \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  "\<And> (A :: ('a, 'c, 't :: time, 's) ta) l u l' u'. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> P u \<Longrightarrow> P u'" "P u" for
  A A' :: "('a, 'c, 't :: time, 's) ta"
  apply standard
  apply (insert that(3))
  subgoal
    by (induction A\<equiv> A _ _ _ _ rule: steps.induct) (auto simp: that(1,2))
   by (induction A\<equiv> A' _ _ _ _ rule: steps.induct) (auto simp: that(2) that(1)[symmetric])

lemma step_V:
  "\<forall> c. u' c \<ge> 0" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" "\<forall> c. u c \<ge> 0"
  using that by (auto simp: reset_V delay_V elim: step_a.cases)

lemma extend_ta_iff_steps:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<longleftrightarrow> extend_ta A cs \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" if "\<forall> c. u c \<ge> 0"
  apply (intro steps_iffI extend_ta_iff)
    apply assumption
   by (rule step_V, assumption+, rule that)

end