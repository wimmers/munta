theory TA_More
  imports TA.Timed_Automata TA.DBM_Operations Refine_Imperative_HOL.IICF "library/Graphs"
begin

chapter \<open>Mixed Additional Material on Timed Automata\<close>

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
  using that by (induction cs) (force simp: clock_val_def)+

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

context
  notes [elim!]  = step.cases step'.cases step_t.cases step_z.cases
begin

lemma extend_ta_iff:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<longleftrightarrow> extend_ta A cs \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" if "\<forall> c. u c \<ge> 0"
  using that apply safe
     apply (force simp: extend_cc_iff reset_V intro: step_a.intros elim!: step_a.cases)
    apply (force simp add: extend_cc_iff delay_V)
   apply (cases rule: step_a.cases, assumption)
   apply (rule step.intros, rule step_a.intros)
  unfolding extend_ta_def apply (force simp: trans_of_def)
     apply assumption+
  prefer 2
  apply assumption
  subgoal
    by (metis extend_cc_iff inv_of_def prod.sel(2) reset_V)
  subgoal
    by (metis delay_V extend_cc_iff inv_of_def prod.sel(2) step_t step_t.intros)
  done
    (*  apply simp
apply (force simp add: extend_cc_iff)
   apply (auto simp add: reset_V extend_cc_iff intro: step_a.intros)
  using extend_cc_iff delay_V by fas *)

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

end (* End of context for aggressive elimination rules *)

lemma extend_ta_iff_steps:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<longleftrightarrow> extend_ta A cs \<turnstile> \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" if "\<forall> c. u c \<ge> 0"
  apply (intro steps_iffI extend_ta_iff)
    apply assumption
  by (rule step_V, assumption+, rule that)



lemma collect_clkvt_alt_def:
  "collect_clkvt T = \<Union>((set o fst \<circ> snd \<circ> snd \<circ> snd) ` T)"
unfolding collect_clkvt_def by fastforce

lemma ta_collect_clkt_alt_def:
  "collect_clkt S = \<Union> (collect_clock_pairs ` (fst o snd) ` S)"
unfolding Timed_Automata.collect_clkt_def by fastforce

lemma ta_collect_clki_alt_def:
  "collect_clki I = \<Union> (collect_clock_pairs ` I ` UNIV)"
unfolding Timed_Automata.collect_clki_def by auto

lemma constraint_clk_constraint_pair:
  "constraint_clk ac = fst (constraint_pair ac)"
by (cases ac) auto

lemma collect_clks_inv_clk_set:
  "collect_clks (inv_of A l) \<subseteq> clk_set A"
  unfolding
    clkp_set_def collect_clki_def collect_clks_def collect_clock_pairs_def
  by (auto simp: constraint_clk_constraint_pair) blast

lemma collect_clocks_clk_set:
  assumes
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows
    "collect_clks g \<subseteq> clk_set A"
  using assms unfolding clkp_set_def collect_clks_id collect_clkt_def by fastforce

lemma reset_clk_set:
  assumes
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  shows
    "set r \<subseteq> clk_set A"
using assms by (fastforce simp: clkp_set_def collect_clkvt_def)

lemma ac_iff:
  "u1 \<turnstile>\<^sub>a ac \<longleftrightarrow> u2 \<turnstile>\<^sub>a ac" if
  "u1 (fst (constraint_pair ac)) = u2 (fst (constraint_pair ac))"
  using that by (cases ac) auto

lemma ac_iff':
  "u1 \<turnstile>\<^sub>a ac \<longleftrightarrow> u2 \<turnstile>\<^sub>a ac" if
  "u1 (constraint_clk ac) = u2 (constraint_clk ac)"
  using that by (cases ac) auto

lemma cc_iff:
  "u1 \<turnstile> cc \<longleftrightarrow> u2 \<turnstile> cc" if "\<forall> (c, d) \<in> collect_clock_pairs cc. u1 c = u2 c"
  using that
  by (auto 4 3 simp: ac_iff[of u1 _ u2] list_all_iff collect_clock_pairs_def clock_val_def)

lemma cc_iff':
  "u1 \<turnstile> cc \<longleftrightarrow> u2 \<turnstile> cc" if "\<forall> c \<in> collect_clks cc. u1 c = u2 c"
  using that
  by (auto simp: ac_iff'[of u1 _ u2] list_all_iff collect_clks_def clock_val_def)

lemma step_t_bisim:
  "\<exists> u2'. A \<turnstile> \<langle>l, u2\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u2'\<rangle> \<and> (\<forall> c. c \<in> clk_set A \<longrightarrow> u1' c = u2' c)"
  if assms: "A \<turnstile> \<langle>l, u1\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u1'\<rangle>" "\<forall> c. c \<in> clk_set A \<longrightarrow> u1 c = u2 c"
  using that(1)
  apply cases
  apply (subst (asm) cc_iff'[of _ _ "u2 \<oplus> d"])
  subgoal
    using collect_clks_inv_clk_set[of A l] assms(2) by (auto simp: cval_add_def)
  using assms(2) by (force simp: cval_add_def)

lemma step_a_bisim:
  "\<exists> u2'. A \<turnstile> \<langle>l, u2\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u2'\<rangle> \<and> (\<forall> c. c \<in> clk_set A \<longrightarrow> u1' c = u2' c)"
  if assms: "A \<turnstile> \<langle>l, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u1'\<rangle>" "\<forall> c. c \<in> clk_set A \<longrightarrow> u1 c = u2 c"
  using that(1)
  apply cases
  subgoal for g r
    apply (subst (asm) cc_iff'[of _ _ "u2"])
    subgoal
      using assms(2) by (force dest: collect_clocks_clk_set)
    apply (subst (asm) (2) cc_iff'[of _ _ "[r\<rightarrow>0]u2"])
    subgoal
      apply rule
      subgoal for c
        using collect_clks_inv_clk_set[of A l'] assms(2) by (cases "c \<in> set r"; force)
      done
    apply (intro exI conjI)
     apply (rule, assumption+)
     apply (simp; fail)
    apply rule
    subgoal for c
      using collect_clks_inv_clk_set[of A l'] assms(2) by (cases "c \<in> set r"; force)
    done
  done

lemma step'_bisim:
  "\<exists> u2'. A \<turnstile>' \<langle>l, u2\<rangle> \<rightarrow> \<langle>l', u2'\<rangle> \<and> (\<forall> c. c \<in> clk_set A \<longrightarrow> u1' c = u2' c)"
  if assms: "A \<turnstile>' \<langle>l, u1\<rangle> \<rightarrow> \<langle>l', u1'\<rangle>" "\<forall> c. c \<in> clk_set A \<longrightarrow> u1 c = u2 c"
  using that(1)
  apply cases
  apply (drule step_t_bisim[OF _ that(2)])
  apply clarify
  apply (drule step_a_bisim, assumption)
  apply auto
  done

lemma ta_bisimulation:
  "Bisimulation_Invariant
  (\<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
  (\<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
  (\<lambda> (l, u) (l', u'). l' = l \<and> (\<forall> c. c \<in> clk_set A \<longrightarrow> u c = u' c))
  (\<lambda> _. True) (\<lambda> _. True)
  "
  apply standard
  subgoal for a b a'
    by clarify (drule step'_bisim; auto)
  subgoal for a b a'
    by clarify (drule step'_bisim; auto)
  ..

end (* Theory *)
