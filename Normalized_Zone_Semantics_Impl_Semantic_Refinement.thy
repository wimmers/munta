theory Normalized_Zone_Semantics_Impl_Semantic_Refinement
  imports TA_Impl_Misc TA.Floyd_Warshall
    FW_More
    Normalized_Zone_Semantics_Impl
    "Worklist_Algorithms/Liveness_Subsumption"
begin

chapter \<open>Semantic Refinement of the Reachability Checker\<close>

no_notation Ref.update ("_ := _" 62)

hide_const D

hide_fact upd_def


lemma FWI'_characteristic:
  "canonical_subs n (I \<union> {a::nat}) (curry (FWI' M n a)) \<or> check_diag n (FWI' M n a)" if
  "canonical_subs n I (curry M)" "I \<subseteq> {0..n}" "a \<le> n"
  using fwi_characteristic[of n I "curry M", OF that]
  unfolding check_diag_def neutral FWI'_def by simp

lemma FWI'_check_diag_preservation:
  "check_diag n (FWI' M n a)" if "check_diag n M"
  using that fwi_mono[of _ n _ "curry M" a n n] unfolding check_diag_def FWI'_def FWI_def by force

lemma diag_conv_M:
  "\<forall>i\<le>n. conv_M D (i, i) \<le> 0" if "\<forall>i\<le>n. D (i, i) \<le> 0"
  using that by auto (metis DBMEntry.simps(15) conv_dbm_entry_mono neutral of_int_0)

lemma conv_M_diag:
  "\<forall>i\<le>n. D (i, i) \<le> 0" if "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
  using that by (simp add: conv_dbm_entry_mono_rev neutral)

lemma curry_conv_M_swap:
  "(map_DBMEntry real_of_int \<circ>\<circ>\<circ> curry) M = curry (conv_M M)"
  by (intro ext; simp)

lemma canonical_subs_subset:
  "canonical_subs n I' M" if "canonical_subs n I M" "I' \<subseteq> I"
  using that unfolding canonical_subs_def by auto

lemma n_eq_equiv:
  "[M1]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>" if "M1 =\<^sub>n M2"
  using that unfolding DBM_zone_repr_def n_eq_def DBM_val_bounded_def by auto

definition
  "repair_pair n M a b = FWI' (FWI' M n b) n a"

context Reachability_Problem_Defs
begin

definition
  "abstra_repair ac M = repair_pair n (abstra_upd ac M) 0 (constraint_clk ac)"

definition
  "filter_diag f M \<equiv> if check_diag n M then M else f M"

definition abstr_repair where
  "abstr_repair = fold (\<lambda> ac M. abstra_repair ac M)"

definition
  "E_op l r g l' M \<equiv>
    let
      M' = FW' (abstr_upd (inv_of A l) (up_canonical_upd M n)) n;
      M'' = FW' (abstr_upd (inv_of A l') (reset'_upd (FW' (abstr_upd g M') n) n r 0)) n;
      M''' = FW' (norm_upd M'' (k' l') n) n
    in M'''"

definition
  "E_op' l r g l' M \<equiv>
    let
      M' = abstr_repair (inv_of A l) (up_canonical_upd M n);
      M'' = abstr_repair (inv_of A l') (reset'_upd (abstr_repair g M') n r 0);
      M''' = FW' (norm_upd M'' (k' l') n) n
    in M'''"

definition
  "E_op'' l r g l' M \<equiv>
    let
      M1 = abstr_repair (inv_of A l) (up_canonical_upd M n);
      M2 = filter_diag (\<lambda> M. abstr_repair g M) M1;
      M3 = filter_diag (\<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0)) M2;
      M4 = filter_diag (\<lambda> M. FW' (norm_upd M (k' l') n) n) M3
    in M4"

lemma E_op''_alt_def:
  "E_op'' l r g l' M \<equiv>
    let
      M' = abstr_repair (inv_of A l) (up_canonical_upd M n);
      f1 = \<lambda> M. abstr_repair g M;
      f2 = \<lambda> M. abstr_repair (inv_of A l') (reset'_upd M n r 0);
      f3 = \<lambda> M. FW' (norm_upd M (k' l') n) n
    in filter_diag (filter_diag f3 o filter_diag f2 o f1) M'"
  unfolding E_op''_def filter_diag_def by (rule HOL.eq_reflection) (auto simp: Let_def)

end (* End of context for reachability problem defs *)

(* XXX Move? *)
lemma Bisimulation_Invariant_simulation_strengthen:
  assumes "Bisimulation_Invariant A B sim PA PB"
          "\<And> a b. sim a b \<Longrightarrow> PA a \<Longrightarrow> PB b \<Longrightarrow> R a b"
    shows "Bisimulation_Invariant A B (\<lambda> a b. sim a b \<and> R a b) PA PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB by (rule assms)
  show ?thesis
    by (standard; (blast dest: A_B_step intro: assms(2) | blast dest: B_A_step intro: assms(2)))
qed

context Reachability_Problem
  begin

context
  fixes E\<^sub>1 :: "'s \<times> _ \<Rightarrow> 's \<times> _ \<Rightarrow> bool"
  assumes E_E\<^sub>1_step: "E a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E\<^sub>1 a c \<and> b \<sim> c)"
  assumes E\<^sub>1_E_step: "E\<^sub>1 a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E a c \<and> b \<sim> c)"
  assumes E\<^sub>1_wf_state[intro]: "wf_state a \<Longrightarrow> E\<^sub>1 a b \<Longrightarrow> wf_state b"
begin

lemma E\<^sub>1_steps_wf_state[intro]:
  "wf_state b" if "E\<^sub>1\<^sup>*\<^sup>* a b" "wf_state a"
  using that by (induction rule: rtranclp_induct) auto

lemma E_E\<^sub>1_step':
  "(\<exists> b'. E\<^sub>1 b b' \<and> a' \<sim> b')" if "E a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that E_equiv[OF that] by (blast dest: E_E\<^sub>1_step)

lemma E\<^sub>1_E_step':
  "(\<exists> b'. E b b' \<and> a' \<sim> b')" if "E\<^sub>1 a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that
  apply -
  apply (drule E\<^sub>1_E_step, assumption)
  apply safe
  by (drule E_equiv; blast)

lemma E_E\<^sub>1_steps:
  "\<exists> b'. E\<^sub>1\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "E\<^sup>*\<^sup>* a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that
  apply (induction rule: rtranclp_induct)
   apply blast
  apply clarsimp
  apply (drule E_E\<^sub>1_step')
     apply blast
    prefer 2
    apply blast
   apply blast
  by (auto intro: rtranclp.intros(2))

lemma E\<^sub>1_E_steps:
  "\<exists> b'. E\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "E\<^sub>1\<^sup>*\<^sup>* a a'" "wf_state a" "wf_state b" "a \<sim> b"
  using that
  apply (induction rule: rtranclp_induct)
   apply blast
  apply clarsimp
  apply (drule E\<^sub>1_E_step')
     apply blast
    prefer 2
    apply blast
   apply blast
  by (auto intro: rtranclp.intros(2))

lemma E_E\<^sub>1_steps_empty:
  "(\<exists> l' M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {}) \<longleftrightarrow>
   (\<exists> l' M'. E\<^sub>1\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {})"
  by (auto 4 4 simp: state_equiv_def dbm_equiv_def dest: E_E\<^sub>1_steps E\<^sub>1_E_steps)

lemma E_E\<^sub>1_bisim:
  "Bisimulation_Invariant E E\<^sub>1 op \<sim> wf_state wf_state"
  by standard (blast intro: state_equiv_sym dest: E\<^sub>1_E_step' intro: E_E\<^sub>1_step')+

context
  fixes P :: "'s \<times> _ \<Rightarrow> bool"
    assumes P: "P a \<Longrightarrow> a \<sim> b \<Longrightarrow> wf_state a \<Longrightarrow> wf_state b \<Longrightarrow> P b"
  begin

lemma E_E\<^sub>1_steps_equiv:
  "(\<exists> l' M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> P (l', M')) \<longleftrightarrow>
   (\<exists> l' M'. E\<^sub>1\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> P (l', M'))"
  apply safe
  subgoal
    by (frule E_E\<^sub>1_steps, safe; blast intro: P)
  subgoal
    by (frule E\<^sub>1_E_steps, safe; blast intro: P)
  done

lemma E_E\<^sub>1_bisim':
  "Bisimulation_Invariant E E\<^sub>1 (\<lambda> a b. a \<sim> b \<and> (P a \<longleftrightarrow> P b)) wf_state wf_state"
  by (rule Bisimulation_Invariant_simulation_strengthen; blast intro: state_equiv_sym P E_E\<^sub>1_bisim)

end

lemma E\<^sub>1_mono:
  assumes "E\<^sub>1 (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E\<^sub>1 (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  using assms
  apply -
  apply (drule E\<^sub>1_E_step)
   apply (simp add: wf_state_def; fail)
  apply safe
  apply (drule E_mono[where M = M], assumption+)
  apply safe
  by (drule E_E\<^sub>1_step; force simp: wf_state_def state_equiv_def dbm_equiv_def)

lemma E\<^sub>1_wf_dbm[intro]:
  "wf_dbm M \<Longrightarrow> E\<^sub>1 (l, M) (l', M') \<Longrightarrow> wf_dbm M'"
  using E\<^sub>1_wf_state unfolding wf_state_def by auto

(* XXX Duplication (E_mono') *)
lemma E\<^sub>1_mono':
  assumes "E\<^sub>1 (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E\<^sub>1 (l,M) (l',M') \<and> dbm_subset n D' M'"
  using assms
  apply -
  apply (frule E\<^sub>1_mono[where M = M], assumption+)
   apply (subst dbm_subset_correct'', assumption+)
   apply (rule dbm_subset_conv, assumption)
  apply safe
  apply (subst (asm) dbm_subset_correct'')
    apply (blast intro: dbm_subset_conv_rev)+
  done

end (* End of anonymous context *)

lemma canonical'_up_canonical_upd:
  assumes "canonical' M"
  shows "canonical' (up_canonical_upd M n)"
  using
    up_canonical_preservation[OF assms] up_canonical_eq_up[OF assms]
    up_canonical_upd_up_canonical'[of M n]
  unfolding curry_def n_eq_def by auto

lemma check_diag_up_canonical_upd:
  "check_diag n (up_canonical_upd M n)" if "check_diag n M"
  unfolding up_canonical_upd_def
  apply (rule fold_acc_preserv'[where P = "check_diag n"])
  using that by (auto simp: check_diag_def)

lemma canonical_diag'_up_canonical_upd:
  "canonical_diag' (up_canonical_upd M n)" if "canonical_diag' M"
  using that by (blast dest: canonical'_up_canonical_upd check_diag_up_canonical_upd)

lemma canonical_subs'_upd:
  "canonical_subs' (I - {a, b}) (M((a, b) := c))" if "canonical_subs' I M" "c \<le> M (a, b)"
  using that unfolding canonical_subs_def by (auto 4 4)

lemma canonical'_conv_M_iff:
  "canonical' (conv_M D) \<longleftrightarrow> canonical' D"
  by (metis canonical_conv canonical_conv_rev)

lemma canonical_subs'_subset:
  "canonical_subs' I' M" if "canonical_subs' I M" "I' \<subseteq> I"
  using that by (rule canonical_subs_subset)

lemma wf_dbm_altD:
  "canonical' D \<or> check_diag n D"
  "\<forall>i\<le>n. D (i, i) \<le> 0"
  "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V"
  if "wf_dbm D"
  using that
    apply -
    apply (drule wf_dbm_D, simp only: canonical'_conv_M_iff; fail)
   apply (drule wf_dbm_D, auto intro!: conv_M_diag; fail)
  apply (drule wf_dbm_D, erule valid_dbm.cases, simp; fail)
  done

lemmas valid_dbm_convI = valid_dbm.intros[OF _ dbm_int_conv]
thm diag_conv
lemmas wf_dbm_altI = wf_dbm_I[OF _ diag_conv_M valid_dbm_convI]
(* XXX Why do we have two notions here? *)
thm valid_dbm_def

lemma wf_dbm_rule:
  assumes "wf_dbm D"
  assumes canonical:
    "canonical' D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> 0 \<Longrightarrow> \<forall>i\<le>n. D (i, i) = 0 \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> canonical' (f D) \<or> check_diag n (f D)
    "
  assumes diag:
    "check_diag n D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> 0 \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> check_diag n (f D)
    "
  assumes diag_le:
    "canonical' D \<or> check_diag n D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> 0 \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> \<forall>i\<le>n. f D (i, i) \<le> 0
    "
  assumes V:
    "canonical' D \<Longrightarrow> \<forall>i\<le>n. D (i, i) \<le> 0 \<Longrightarrow> [curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V
    \<Longrightarrow> [curry (conv_M (f D))]\<^bsub>v,n\<^esub> \<subseteq> V
    "
  shows "wf_dbm (f D)"
proof -
  from wf_dbm_altD[OF assms(1)] have facts:
    "canonical' D \<or> check_diag n D" "\<forall>i\<le>n. D (i, i) \<le> 0" "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> V"
    .
  from this(1) consider "canonical' D \<and> \<not> check_diag n D" | "check_diag n D"
    by auto
  then show ?thesis
  proof cases
    assume A: "canonical' D \<and> \<not> check_diag n D"
    with facts(2) have "\<forall>i\<le>n. D (i, i) = 0"
      unfolding check_diag_def neutral[symmetric] by fastforce
    with A[THEN conjunct1] show ?thesis
      by (intro wf_dbm_altI[unfolded canonical'_conv_M_iff] canonical diag_le V facts)
  next
    assume "check_diag n D"
    then have "check_diag n (f D)" by (intro disjI2 diag facts)
    then have "[curry (conv_M (f D))]\<^bsub>v,n\<^esub> = {}" by (intro check_diag_conv_M check_diag_empty_spec)
    with \<open>check_diag n (f D)\<close> show ?thesis
      by - (rule wf_dbm_altI[unfolded canonical'_conv_M_iff];
           (intro diag_le diag facts; fail | blast)+)
  qed
qed

lemma canonical_subs'_abstra_upd:
  "canonical_subs' (I - {0, constraint_clk ac}) (abstra_upd ac M)" if
  "canonical_subs' I M" "constraint_clk ac > 0"
  using that
  apply (cases ac)
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Lt d" c 0] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Le d" c 0] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
    defer
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Lt (-d)" 0 c] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
  subgoal for c d
    by (force
        dest: canonical_subs'_upd[of I M "Le (-d)" 0 c] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
  subgoal for c d
    apply (auto simp: min_def Let_def)
       apply (force
        dest: canonical_subs'_upd[of I M "Le (-d)" 0 c] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
      apply (force
        dest: canonical_subs'_upd[of I M "Le d" c 0] simp: insert_commute min_def
        intro: canonical_subs'_subset
        )
    subgoal
      apply (drule canonical_subs'_upd[of I M "Le (-d)" 0 c])
      by simp (metis fun_upd_apply fun_upd_triv gr_implies_not_zero old.prod.inject)
    subgoal
      by (drule canonical_subs'_upd[of I M "Le (-d)" 0 c];
          force dest: canonical_subs'_upd[of _ _ "Le d" c 0])
    done
  done

lemmas FWI_zone_equiv_spec = FWI_zone_equiv[OF surj_numbering]

lemma repair_pair_equiv:
  "M \<simeq> repair_pair n M a b" if "a \<le> n" "b \<le> n"
  unfolding dbm_equiv_def repair_pair_def FWI'_def
  apply (subst FWI_zone_equiv_spec[of b], rule that)
  apply (subst FWI_zone_equiv_spec[of a], rule that)
  by (simp add: FWI_def fwi_conv_M' fwi_conv_M'' curry_conv_M_swap)

lemma repair_pair_canonical_diag_1:
  "canonical_diag (repair_pair n M a b)" if "canonical_subs' ({0..n} - {a, b}) M" "a \<le> n" "b \<le> n"
  using that
  unfolding canonical'_conv_M_iff
  unfolding repair_pair_def
  apply -
  apply (drule FWI'_characteristic[where a = b], force, assumption)
  apply (erule disjE)
   apply (drule FWI'_characteristic[where a = a], force, assumption)
  unfolding canonical_alt_def
  subgoal premises prems
  proof -
    have *: "{0..n} - {a, b} \<union> {b} \<union> {a} = {0..n}"
      using that(2,3) by fastforce
    with prems(3) show ?thesis by (simp only: *)
  qed
  by (auto intro: FWI'_check_diag_preservation)

lemma repair_pair_canonical_diag_2:
  "canonical_diag (repair_pair n M a b)" if "check_diag n M"
  unfolding repair_pair_def using that by (auto intro: FWI'_check_diag_preservation)

lemma repair_pair_diag_le:
  "\<forall>i\<le>n. repair_pair n M 0 c (i, i) \<le> 0" if "\<forall>i\<le>n. M (i, i) \<le> 0"
  using that
  unfolding repair_pair_def FWI'_def
  apply clarsimp
  apply (rule order.trans[OF FWI_mono], assumption, assumption)
  apply (rule order.trans[OF FWI_mono], assumption, assumption)
  by simp

lemma abstra_upd_conv_M_zone_equiv:
  assumes "constraint_clk ac > 0" "constraint_clk ac \<le> n"
  shows "[curry (conv_M (abstra_upd ac M))]\<^bsub>v,n\<^esub> = {u. u \<turnstile>\<^sub>a conv_ac ac} \<inter> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  apply (subst unused.conv_abstra_upd)
  apply (subst abstra_upd_eq_abstra')
   defer
   apply (subst abstra_abstra'[symmetric, where v = v])
    defer
    apply (subst dbm_abstra_zone_eq[OF clock_numbering(1)])
  using assms by (cases ac; auto simp: v_def)+

lemma abstra_upd_conv_M_V:
  assumes "[curry (conv_M M)]\<^bsub>v,n\<^esub> \<subseteq> V" "constraint_clk ac > 0" "constraint_clk ac \<le> n"
  shows "[curry (conv_M (abstra_upd ac M))]\<^bsub>v,n\<^esub> \<subseteq> V"
  using assms(1) by (auto simp: abstra_upd_conv_M_zone_equiv[OF assms(2-)])

lemma abstra_repair_check_diag_preservation:
  "check_diag n (abstra_repair ac M)" if "check_diag n M" "constraint_clk ac > 0"
proof -
  have "check_diag n (abstra_upd ac M)"
    using that unfolding check_diag_def by (auto simp: abstra_upd_diag_preservation)
  then show ?thesis
    unfolding abstra_repair_def repair_pair_def by (auto intro: FWI'_check_diag_preservation)
qed

lemma wf_dbm_abstra_repair:
  assumes "wf_dbm M" "constraint_clk ac > 0" "constraint_clk ac \<le> n"
  shows "wf_dbm (abstra_repair ac M)"
proof -
  note facts = wf_dbm_altD[OF assms(1)]
  let ?M = "abstra_upd ac M"
  let ?MM = "abstra_repair ac M"
  from assms(2) facts(2) have "\<forall>i\<le>n. ?M (i, i) \<le> 0"
    by (auto simp: abstra_upd_diag_preservation)
  then have diag: "\<forall>i\<le>n. ?MM (i, i) \<le> 0" unfolding abstra_repair_def by (rule repair_pair_diag_le)
  from assms(2,3) facts(3) have "[curry (conv_M ?M)]\<^bsub>v,n\<^esub> \<subseteq> V" by - (rule abstra_upd_conv_M_V)
  with repair_pair_equiv[of 0 "constraint_clk ac" ?M] assms(3) have V:
    "[curry (conv_M ?MM)]\<^bsub>v,n\<^esub> \<subseteq> V"
    unfolding dbm_equiv_def abstra_repair_def by simp
  from facts(1) have "canonical_diag ?MM"
  proof
    assume "canonical' M"
    from canonical_subs'_abstra_upd[OF this[unfolded canonical_alt_def] assms(2)] show
      "canonical_diag ?MM"
      unfolding abstra_repair_def by (intro repair_pair_canonical_diag_1 assms; simp)
  next
    assume "check_diag n M"
    then have "check_diag n ?M"
      unfolding check_diag_def using assms(2) by (auto simp: abstra_upd_diag_preservation)
    then show "canonical_diag ?MM"
      unfolding abstra_repair_def by (rule repair_pair_canonical_diag_2)
  qed
  with diag V show ?thesis by (intro wf_dbm_altI)
qed

lemma wf_dbm_abstra_repair_equiv:
  assumes "constraint_clk ac \<le> n"
  shows "abstra_repair ac M \<simeq> abstra_upd ac M"
  by (simp add: abstra_repair_def assms dbm_equiv_sym repair_pair_equiv)

lemma abstra_upd_equiv:
  assumes "constraint_clk ac > 0" "constraint_clk ac \<le> n" "M \<simeq> M'"
  shows "abstra_upd ac M \<simeq> abstra_upd ac M'"
  using assms(3) abstra_upd_conv_M_zone_equiv[OF assms(1,2)] unfolding dbm_equiv_def by auto

lemma wf_dbm_abstra_repair_equiv':
  assumes "constraint_clk ac > 0" "constraint_clk ac \<le> n" "M \<simeq> M'"
  shows "abstra_repair ac M \<simeq> abstra_upd ac M'"
  using wf_dbm_abstra_repair_equiv[OF assms(2)] abstra_upd_equiv[OF assms] by blast

lemma abstr_repair_check_diag_preservation:
  "check_diag n (abstr_repair cc M)" if "check_diag n M" "\<forall> c \<in> constraint_clk ` set cc. c > 0"
  using that unfolding abstr_repair_def
  by (induction cc arbitrary: M) (auto intro!: abstra_repair_check_diag_preservation)

lemma wf_dbm_abstr_repair_equiv:
  assumes "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n" "M \<simeq> M'"
  shows "abstr_repair cc M \<simeq> abstr_upd cc M'"
  using assms unfolding abstr_repair_def abstr_upd_def
  by (induction cc arbitrary: M M') (auto dest!: wf_dbm_abstra_repair_equiv')

lemma wf_dbm_abstr_repair_equiv':
  assumes "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n" "M \<simeq> M'"
  shows "abstr_repair cc M \<simeq> abstr_repair cc M'"
  using assms by (meson wf_dbm_abstr_repair_equiv dbm_equiv_sym dbm_equiv_trans dbm_equiv_refl)

lemma wf_dbm_abstr_repair:
  assumes "wf_dbm M" "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n"
  shows "wf_dbm (abstr_repair cc M)"
  using assms unfolding abstr_repair_def
  by (induction cc arbitrary: M) (auto intro: wf_dbm_abstra_repair)

lemma abstr_upd_conv_M_V:
  assumes "[curry (conv_M M)]\<^bsub>v,n\<^esub> \<subseteq> V" "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n"
  shows "[curry (conv_M (abstr_upd cc M))]\<^bsub>v,n\<^esub> \<subseteq> V"
  using assms
  unfolding abstr_upd_def
  apply (induction cc arbitrary: M)
   apply simp
  subgoal premises prems
    apply simp
    apply (intro prems(1)[simplified] abstra_upd_conv_M_V[simplified])
    using prems(2-) by auto
  done

lemma wf_dbm_FW'_abstr_upd:
  "wf_dbm (FW' (abstr_upd cc M) n)" if "wf_dbm M" "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n"
  apply (rule wf_dbm_rule[OF that(1)])
  subgoal
    unfolding check_diag_def neutral[symmetric] by (rule FW'_canonical)
  subgoal
    unfolding check_diag_def neutral[symmetric]
    using that(2)
    apply safe
    apply (subst (asm) (2) abstr_upd_diag_preservation[symmetric, where M = M and cc = cc])
    by (auto dest: FW'_neg_diag_preservation simp: collect_clks_def)
  subgoal
    apply (drule abstr_upd_diag_preservation'[where cc = cc])
    by (simp add: FW'_diag_preservation collect_clks_def that(2))+
  subgoal
    by (subst FW'_zone_equiv) (intro abstr_upd_conv_M_V that)
  done

lemma up_canonical_upd_V:
  "[curry (up_canonical_upd M n)]\<^bsub>v,n\<^esub> \<subseteq> V" if "canonical' M" "[curry M]\<^bsub>v,n\<^esub> \<subseteq> V"
  apply (subst n_eq_equiv[OF up_canonical_upd_up_canonical'])
  apply (subst up_canonical_equiv_up[OF that(1)])
  apply (subst up_correct)
   apply (rule clock_numbering(1))
    by (rule up_V[OF that(2)])

lemma n_eq_transfer[transfer_rule]: "eq_onp (\<lambda>x. x = n) n n"
  by (simp add: eq_onp_def)

lemma RI_up_canonical_upd:
  "RI n (up_canonical_upd Mr n) (up_canonical_upd Mi n)" if "RI n Mr Mi"
  supply [transfer_rule] = that
  by transfer_prover

lemma wf_dbm_up_canonical_upd:
  "wf_dbm (up_canonical_upd M n)" if "wf_dbm M"
  apply (rule wf_dbm_rule[OF that])
  subgoal
    by (intro canonical_diag'_up_canonical_upd disjI1)
  subgoal
    by (simp add: check_diag_def up_canonical_upd_diag_preservation)
  subgoal
    by (simp add: up_canonical_upd_diag_preservation)
  subgoal
    unfolding canonical'_conv_M_iff[symmetric]
    apply (drule up_canonical_upd_V, assumption)
    by (subst (asm) RI_zone_equiv[OF RI_up_canonical_upd[OF RI_conv_M]])
  done

lemma reset_resets_spec:
  "[reset M n i d]\<^bsub>v,n\<^esub> = {u(i := d) |u. u \<in> [M]\<^bsub>v,n\<^esub>}" if "i > 0" "i \<le> n" "0 \<le> d"
proof -
  from that have v_i[simp]: "v i = i" by (simp add: v_def)
  show ?thesis
    apply (subst reset_resets[OF _ clock_numbering(1), of i, unfolded v_i])
    using clock_numbering(2) that by fastforce+
qed

lemma reset_canonical_n_eq_reset_canonical_upd:
  "reset_canonical (curry M) i d =\<^sub>n curry (reset_canonical_upd M n i d)" if "i > 0"
  using that unfolding n_eq_def by (auto simp: reset_canonical_upd_reset_canonical')

lemma RI_reset_canonical_upd:
  "RI n (reset_canonical_upd Mr n i (real_of_int d)) (reset_canonical_upd Mi n i d)" if
  "RI n Mr Mi" "i \<le> n"
proof -
  have [transfer_rule]: "ri (real_of_int d) d"
    by (simp only: ri_def)
  from that have [transfer_rule]: "eq_onp (\<lambda>x. x < Suc n) i i" by (simp add: eq_onp_def)
  note [transfer_rule] = that(1)
  show ?thesis by transfer_prover
qed

lemma reset_canonical_upd_correct:
  "[curry (reset_canonical_upd D n i d)]\<^bsub>v,n\<^esub> = {u(i := d) |u. u \<in> [curry D]\<^bsub>v,n\<^esub>}" if
  "canonical' D" "i > 0" "i \<le> n" "0 \<le> d"
  apply (subst n_eq_equiv[OF reset_canonical_n_eq_reset_canonical_upd, symmetric])
  defer
   apply (subst reset_reset_canonical[symmetric])
      prefer 5
      apply (subst reset_resets_spec)
  using that clock_numbering(1) by auto

lemma reset_canonical_upd_correct_conv_M:
  "[curry ((map_DBMEntry real_of_int \<circ>\<circ>\<circ> reset_canonical_upd M n) i d)]\<^bsub>v,n\<^esub> =
    {u(i := real_of_int d) |u. u \<in> [curry (conv_M M)]\<^bsub>v,n\<^esub>}"
  if "i > 0" "i \<le> n" "0 \<le> d" "canonical' M"
  apply (subst RI_zone_equiv[OF RI_reset_canonical_upd[OF RI_conv_M], symmetric], rule that)
  apply (subst reset_canonical_upd_correct)
  unfolding canonical'_conv_M_iff using that by auto

lemma wf_dbm_reset_canonical_upd:
  "wf_dbm (reset_canonical_upd M n i d)" if "wf_dbm M" "i > 0" "i \<le> n" "0 \<le> d"
  apply (rule wf_dbm_rule[OF that(1)])
  subgoal
    by (intro reset_canonical_upd_canonical disjI1 that)
  subgoal
    by (metis check_diag_def reset_canonical_upd_diag_preservation that(2))
  subgoal
    by (simp add: reset_canonical_upd_diag_preservation that(2))
  subgoal
    unfolding canonical'_conv_M_iff[symmetric]
    apply (subst RI_zone_equiv[OF RI_reset_canonical_upd[OF RI_conv_M], symmetric], rule that)
    apply (subst reset_canonical_upd_correct)
    using that unfolding V_def by auto
  done

lemma reset_canonical_upd_equiv':
  "reset_canonical_upd D n i d \<simeq> reset_canonical_upd M n i d" if
  "D \<simeq> M" "i > 0" "i \<le> n" "0 \<le> d" "canonical' D" "canonical' M"
  using that unfolding dbm_equiv_def
  apply (subst reset_canonical_upd_correct_conv_M)
      prefer 5
      apply (subst reset_canonical_upd_correct_conv_M)
  by auto

lemma reset_canonical_upd_check_diag_preservation:
  "check_diag n (reset_canonical_upd D n i d)" if "check_diag n D" "i > 0"
  by (metis check_diag_def reset_canonical_upd_diag_preservation that)

lemma reset_canonical_upd_equiv:
  "reset_canonical_upd D n i d \<simeq> reset_canonical_upd M n i d" if
  "D \<simeq> M" "i > 0" "i \<le> n" "0 \<le> d" "canonical_diag' D" "canonical_diag' M"
proof -
  have *: "check_diag n D \<longleftrightarrow> check_diag n M"
    using that unfolding dbm_equiv_def
      apply -
    apply (subst canonical_check_diag_empty_iff[symmetric], assumption)
    apply (subst canonical_check_diag_empty_iff[symmetric], assumption)
      by simp
  from that(5) consider "canonical' D" "\<not> check_diag n D" | "check_diag n D"
    by auto
  then show ?thesis
  proof cases
    case 1
    with * that(6) have "canonical' D" "canonical' M"
      by auto
    with that show ?thesis
      by (auto intro: reset_canonical_upd_equiv')
  next
    case 2
    then have "check_diag n D" "check_diag n M" unfolding * by assumption+
    then have
      "check_diag n (reset_canonical_upd D n i d)" "check_diag n (reset_canonical_upd M n i d)"
      by - (intro reset_canonical_upd_check_diag_preservation that(2), assumption)+
    then show ?thesis by (auto dest!: check_diag_empty_spec check_diag_conv_M simp: dbm_equiv_def)
  qed
qed

lemma reset'_upd_check_diag_preservation:
  "check_diag n (reset'_upd M n cs d)" if "check_diag n M" "\<forall> i \<in> set cs. i > 0"
  using that unfolding reset'_upd_def
  by (induction cs arbitrary: M) (auto intro: reset_canonical_upd_check_diag_preservation)

lemma wf_dbm_reset'_upd:
  "wf_dbm (reset'_upd M n cs d)" if "wf_dbm M" "\<forall> i \<in> set cs. i > 0 \<and> i \<le> n" "0 \<le> d"
  using that unfolding reset'_upd_def
  by (induction cs arbitrary: M) (auto intro: wf_dbm_reset_canonical_upd)

lemma reset'_upd_equiv:
  "reset'_upd D n cs d \<simeq> reset'_upd M n cs d" if
  "D \<simeq> M" "\<forall> i \<in> set cs. i > 0 \<and> i \<le> n" "0 \<le> d" "wf_dbm M" "wf_dbm D"
  using that unfolding reset'_upd_def
  apply (induction cs arbitrary: D M)
   apply (simp; fail)
  subgoal premises prems for c cs D M
    apply simp
    apply (rule prems(1))
        apply (rule reset_canonical_upd_equiv)
    using prems(2-)
    by (auto intro: wf_dbm_reset_canonical_upd dest: wf_dbm_altD)
  done

lemma E_E_op: "E = (\<lambda> (l, M) (l', M'''). \<exists> g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_op l r g l' M)"
  unfolding E_op_def E_alt_def by simp

end (* End of locale for Reachability Problem *)

locale E_From_Op_Defs = Reachability_Problem_Defs l\<^sub>0 for l\<^sub>0 :: "'s" +
  fixes f :: "'s
   \<Rightarrow> nat list
      \<Rightarrow> (nat, int) acconstraint list
         \<Rightarrow> 's
            \<Rightarrow> (nat \<times> nat \<Rightarrow> int DBMEntry)
               \<Rightarrow> nat \<times> nat \<Rightarrow> int DBMEntry"
begin

definition "E_from_op = (\<lambda> (l, M) (l', M'''). \<exists> g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = f l r g l' M)"

end

locale E_From_Op = Reachability_Problem + E_From_Op_Defs

locale E_From_Op_Bisim = E_From_Op +
  assumes op_bisim:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> f l r g l' M \<simeq> E_op l r g l' M"
    and op_wf:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> wf_dbm M \<Longrightarrow> wf_dbm (f l r g l' M)"
begin

lemma E_E_from_op_step:
  "E a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E_from_op a c \<and> b \<sim> c)"
  unfolding E_E_op E_from_op_def wf_state_def state_equiv_def
  by (blast intro: op_bisim dbm_equiv_sym)

lemma E_from_op_E_step:
  "E_from_op a b \<Longrightarrow> wf_state a \<Longrightarrow> (\<exists> c. E a c \<and> b \<sim> c)"
  unfolding E_E_op E_from_op_def wf_state_def state_equiv_def by (blast intro: op_bisim)

lemma E_from_op_wf_state:
  "wf_state a \<Longrightarrow> E_from_op a b \<Longrightarrow> wf_state b"
  unfolding E_E_op E_from_op_def wf_state_def state_equiv_def by (blast intro: op_wf)

lemma E_E_from_op_steps_empty:
  "(\<exists>l' M'. E\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {}) \<longleftrightarrow>
   (\<exists>l' M'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', M') \<and> [curry (conv_M M')]\<^bsub>v,n\<^esub> = {})"
  by (rule E_E\<^sub>1_steps_empty[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state])

theorem E_from_op_reachability_check:
  "(\<exists> l' D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))
  \<longleftrightarrow> (\<exists> l' D'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))"
  apply (rule E_E\<^sub>1_steps_equiv[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state])
  by
    (auto
      simp: F_rel_def state_equiv_def wf_state_def dbm_equiv_def
      dest!:
        check_diag_empty_spec[OF check_diag_conv_M]
        canonical_check_diag_empty_iff[OF wf_dbm_altD(1)]
    )

lemma E_from_op_mono:
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub>"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M')]\<^bsub>v,n\<^esub>"
  using assms by - (rule E\<^sub>1_mono[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]; blast)

lemma E_from_op_mono':
  assumes "E_from_op (l,D) (l',D')"
    and   "wf_dbm D" "wf_dbm M"
    and "dbm_subset n D M"
  shows "\<exists> M'. E_from_op (l,M) (l',M') \<and> dbm_subset n D' M'"
  using assms by - (rule E\<^sub>1_mono'[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state]; blast)

lemma E_from_op_bisim:
  "Bisimulation_Invariant E E_from_op op \<sim> wf_state wf_state"
  by (rule E_E\<^sub>1_bisim[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state])

end (* End of context for bisimilarity *)

locale E_From_Op_Finite = E_From_Op +
  assumes step_FW_norm:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> dbm_default (curry M) n \<Longrightarrow> dbm_int (curry M) n
    \<Longrightarrow> \<not> check_diag n (f l r g l' M)
    \<Longrightarrow> \<exists> M'.
      f l r g l' M = FW' (norm_upd M' (k' l') n) n
      \<and> dbm_default (curry M') n \<and> dbm_int (curry M') n"
  and check_diag:
    "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> check_diag n M \<Longrightarrow> check_diag n (f l r g l' M)"
begin

(* XXX Duplication *)
lemma steps_FW_norm:
  assumes "E_from_op\<^sup>*\<^sup>* (l, D) (l', D')"
    and "dbm_default (curry D) n"
    and "dbm_int (curry D) n"
  shows "l' = l \<and> D' = D \<or> check_diag n D' \<or> (\<exists>M. D' = FW' (norm_upd M (k' l') n) n \<and>
             ((\<forall>i>n. \<forall>j. curry M i j = 0) \<and> (\<forall>j>n. \<forall>i. curry M i j = 0)) \<and> dbm_int (curry M) n)"
using assms proof (induction "(l', D')" arbitrary: l' D')
  case base then show ?case by auto
next
  case (step y)
  obtain l'' D'' where [simp]: "y = (l'', D'')"
    by force
  from step.hyps(3)[OF this] step.prems have "
    l'' = l \<and> D'' = D \<or>
    check_diag n D'' \<or>
    (\<exists>M. D'' = FW' (norm_upd M (k' l'') n) n \<and>
         ((\<forall>i>n. \<forall>j. curry M i j = 0) \<and> (\<forall>j>n. \<forall>i. curry M i j = 0)) \<and> dbm_int (curry M) n)"
    by auto
  then show ?case
  proof (standard, goal_cases)
    case 1
    with step_FW_norm[OF _ step.prems(1,2)] step.hyps(2) show ?thesis
      unfolding E_from_op_def by auto
  next
    case 2
    then show ?case
    proof (standard, goal_cases)
      case 1
      with step.hyps(2) show ?case
        unfolding E_from_op_def by (auto simp: check_diag)
    next
      case 2
      then obtain M where M:
        "D'' = FW' (norm_upd M (k' l'') n) n" "dbm_default (curry M) n" "dbm_int (curry M) n"
        by auto
      from step.hyps(2) show ?case
        unfolding E_from_op_def
        apply simp
        apply (elim exE conjE)
        subgoal premises prems for g a r
        proof (cases "check_diag n (f l'' r g l' (FW' (norm_upd M (k' l'') n) n))")
          case False
          with prems show ?thesis
          using M
          apply -
          apply (drule
            step_FW_norm[
              of l'' g a r l',
              rotated,
              OF FW'_default[OF norm_upd_default]
                 FW'_int_preservation[OF norm_upd_int_preservation[where k =  "k' l''"]]
            ]
            , assumption)
          defer
            apply (rule length_k'; fail)
          apply (simp; fail)
          unfolding k'_def by auto
        next
          case True
          with \<open>D' = _\<close> \<open>D'' = _\<close> show ?thesis by auto
        qed
        done
    qed
  qed
qed

(* XXX Duplication *)
lemma E_closure_finite:
  "finite {x. E_from_op\<^sup>*\<^sup>* a\<^sub>0 x \<and> \<not> check_diag n (snd x)}"
proof -
  have k': "map int (map (k l) [0..<Suc n]) = k' l" for l unfolding k'_def by auto
  have *:
    "(l, M) = a\<^sub>0 \<or> check_diag n M
     \<or> (\<exists>M'. M = FW' (norm_upd M' (k' l) n) n \<and> dbm_default (curry M') n)"
    if "E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l, M)" for l M
    using that unfolding E_closure a\<^sub>0_def
    apply -
    apply (drule steps_FW_norm)
    unfolding init_dbm_def by (auto simp: neutral)
  moreover have **: "l \<in> locations" if "E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l, M)" for l M
    using that unfolding E_closure locations_def
    apply (induction "(l, M)")
     apply (simp add: a\<^sub>0_def; fail)
    by (force simp: E_from_op_def)
  have
    "{x. E_from_op\<^sup>*\<^sup>* a\<^sub>0 x \<and> \<not> check_diag n (snd x)} \<subseteq>
     {a\<^sub>0} \<union>
     (locations \<times> {FW' (norm_upd M (k' l) n) n | l M. l \<in> locations \<and> dbm_default (curry M) n})"
    (is "_ \<subseteq> _ \<union> ?S")
    apply safe
     apply (rule **, assumption)
    apply (frule *)
    by (auto intro: **)
  moreover have "finite ?S"
    using FW'_normalized_integral_dbms_finite' finite_locations
    using [[simproc add: finite_Collect]]
    by (auto simp: k'_def finite_project_snd)
  ultimately show ?thesis by (auto intro: finite_subset)
qed

end (* End of context for finiteness *)

locale E_From_Op_Bisim_Finite = E_From_Op_Bisim + E_From_Op_Finite
begin

  lemma E_from_op_check_diag:
    "check_diag n M'" if "check_diag n M" "E_from_op (l, M) (l', M')"
    using that unfolding E_from_op_def by (blast intro: check_diag)

  lemma reachable_wf_dbm:
    "wf_dbm M" if "E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l, M)"
  using that proof (induction "(l, M)" arbitrary: l M)
    case base
    then show ?case unfolding a\<^sub>0_def by simp
  next
    case (step y l' M')
    obtain l M where [simp]: "y = (l, M)" by force
    from E_from_op_wf_state[OF _ step(2)] step(1,3) show ?case
      unfolding wf_state_def by auto
  qed

  sublocale Search_Space E_from_op a\<^sub>0 F_rel "subsumes n" "\<lambda> (l, M). check_diag n M"
    apply standard
    subgoal for a
      apply (rule prod.exhaust[of a])
      by (auto simp add: subsumes_simp_1 dbm_subset_refl)
    subgoal for a b c
      apply (rule prod.exhaust[of a], rule prod.exhaust[of b], rule prod.exhaust[of c])
      subgoal for l1 M1 l2 M2 l3 M3
        apply simp
        apply (cases "check_diag n M1")
         apply (simp add: subsumes_def; fail)
        apply (simp add: subsumes_def)
        by (meson check_diag_subset dbm_subset_def dbm_subset_trans)
      done
    subgoal for a b a'
      apply (rule prod.exhaust[of a], rule prod.exhaust[of b], rule prod.exhaust[of a'])
      apply safe
      by (drule E_from_op_mono';
          fastforce simp: E_def subsumes_def dbm_subset_def Graph_Start_Defs.reachable_def
          intro!: reachable_wf_dbm)
    subgoal
      unfolding F_rel_def subsumes_def by auto
    subgoal
      using check_diag_subset unfolding subsumes_def dbm_subset_def by auto
    subgoal
      using E_from_op_check_diag by auto
    unfolding F_rel_def subsumes_def
    unfolding check_diag_def pointwise_cmp_def
    by fastforce

  sublocale Search_Space_finite E_from_op a\<^sub>0 F_rel "subsumes n" "\<lambda> (l, M). check_diag n M"
    by standard
       (auto intro: finite_subset[OF _ E_closure_finite] simp: Graph_Start_Defs.reachable_def)

  sublocale liveness_pre:
    Liveness_Search_Space_pre
    "\<lambda> (l, M) (l', M'). E_from_op (l, M) (l', M') \<and> F l \<and> F l' \<and> \<not> check_diag n M'" a\<^sub>0 "\<lambda> _. False"
    "subsumes n" "\<lambda> (l, M). \<not> check_diag n M \<and> reachable (l, M)"
    apply standard
        apply blast
       apply (blast intro: trans)
      apply safe
     apply (frule mono)
         apply assumption
        apply assumption
       apply assumption
      apply (simp; fail)
     apply safe
     apply (intro exI conjI)
       prefer 3
       apply assumption
      apply safe
    subgoal a
      using empty_mono by auto
    subgoal
      using reachable_step by blast
    subgoal
      by (metis subsumes_simp_2)
    subgoal
      by (metis subsumes_simp_2)
    subgoal
      by (rule a)
    subgoal
      using finite_reachable by (auto intro: finite_subset[rotated])
    done

end (* End of context for finiteness and bisimilarity *)

context Reachability_Problem
begin

lemma norm_step_dbm_equiv:
  "FW' (norm_upd D (k' l') n) n \<simeq> FW' (norm_upd M (k' l') n) n" if "D \<simeq> M" "wf_dbm D" "wf_dbm M"
  unfolding dbm_equiv_def
  apply (subst norm_step_correct'[OF that(2,3,1)])
  apply (subst norm_step_correct'[OF that(3,3)])
  by auto

lemma E_op'_wf: "wf_dbm (E_op' l r g l' M)" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  note wf_intros = norm_step_wf_dbm wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd
  show ?thesis unfolding E_op'_def by simp (intro wf_intros side_conds order.refl)
qed

lemma wf_dbm_abstr_repair_equiv_FW:
  assumes "\<forall> c \<in> constraint_clk ` set cc. c > 0 \<and> c \<le> n" "M \<simeq> M'"
  shows "abstr_repair cc M \<simeq> FW' (abstr_upd cc M') n"
  using wf_dbm_abstr_repair_equiv[OF assms] by (simp add: dbm_equiv_def FW'_zone_equiv)

lemma E_op'_bisim:
  "E_op' l r g l' M \<simeq> E_op l r g l' M" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  note intros =
    norm_step_dbm_equiv wf_dbm_abstr_repair_equiv_FW[rotated] reset'_upd_equiv dbm_equiv_refl
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  note wf_intros =
    norm_step_wf_dbm wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd
    wf_dbm_FW'_abstr_upd
  show ?thesis unfolding E_op'_def E_op_def by simp (intro intros wf_intros side_conds order.refl)
qed

lemma filter_diag_equiv:
  assumes "\<And> M. check_diag n M \<Longrightarrow> check_diag n (f M)"
  shows "filter_diag f M \<simeq> f M"
proof (cases "check_diag n M")
  case True
  then have "check_diag n (f M)" by (rule assms)
  with True show ?thesis
    unfolding filter_diag_def dbm_equiv_def by (auto dest: check_diag_conv_M check_diag_empty_spec)
next
  case False
  then show ?thesis by (auto simp: filter_diag_def)
qed

lemma filter_diag_wf_dbm:
  assumes "\<And> M. wf_dbm M \<Longrightarrow> wf_dbm (f M)" "wf_dbm M"
  shows "wf_dbm (filter_diag f M)"
  unfolding filter_diag_def using assms by auto

lemma E_op''_bisim:
  "E_op'' l r g l' M \<simeq> E_op' l r g l' M" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  note intros =
    norm_step_dbm_equiv dbm_equiv_refl dbm_equiv_trans[OF filter_diag_equiv, rotated]
    wf_dbm_abstr_repair_equiv' reset'_upd_equiv
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast+
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n" "\<forall>c\<in>constraint_clk ` set g. 0 < c"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast+
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n" "\<forall>i\<in>set r. 0 < i"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast+
  moreover note side_conds = calculation that(2)
  note wf_intros =
    wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd filter_diag_wf_dbm
  note check_diag_intros =
    norm_step_check_diag_preservation reset'_upd_check_diag_preservation
    abstr_repair_check_diag_preservation norm_step_check_diag_preservation
  show ?thesis unfolding E_op''_def E_op'_def
    by simp (intro intros check_diag_intros side_conds wf_intros order.refl)
qed

lemma E_op''_bisim':
  "E_op'' l r g l' M \<simeq> E_op l r g l' M" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
  using that by (blast intro: E_op''_bisim E_op'_bisim)

lemma E_op''_wf: "wf_dbm (E_op'' l r g l' M)" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "wf_dbm M"
proof -
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set (inv_of A l'). 0 < c \<and> c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. 0 < c \<and> c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. 0 < i \<and> i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  note wf_intros =
    norm_step_wf_dbm wf_dbm_abstr_repair wf_dbm_reset'_upd wf_dbm_up_canonical_upd
    filter_diag_wf_dbm
  show ?thesis unfolding E_op''_def by simp (intro wf_intros side_conds order.refl)
qed

lemma abstra_upd_default:
  assumes "dbm_default (curry M) n" "constraint_clk ac \<le> n"
  shows "dbm_default (curry (abstra_upd ac M)) n"
  using assms by (auto simp: abstra_upd_out_of_bounds1 abstra_upd_out_of_bounds2)

lemma FWI_default:
  assumes "dbm_default (curry M) n"
  shows "dbm_default (curry (FWI' M n i)) n"
  using assms unfolding FWI'_def FWI_def by (simp add: fwi_out_of_bounds1 fwi_out_of_bounds2)

lemma abstra_repair_default:
  assumes "dbm_default (curry M) n" "constraint_clk ac \<le> n"
  shows "dbm_default (curry (abstra_repair ac M)) n"
  using assms unfolding abstra_repair_def repair_pair_def by (intro abstra_upd_default FWI_default)

lemma abstr_repair_default:
  assumes "dbm_default (curry M) n" "\<forall>c\<in>collect_clks cc. c \<le> n"
  shows "dbm_default (curry (abstr_repair cc M)) n"
  using assms
  unfolding abstr_repair_def
  apply (induction cc arbitrary: M)
   apply (simp; fail)
  by (drule abstra_repair_default; auto)

lemma abstra_repair_int:
  assumes "dbm_int (curry M) n" "constraint_clk ac \<le> n" "snd (constraint_pair ac) \<in> \<int>"
  shows "dbm_int (curry (abstra_repair ac M)) n"
  using assms unfolding abstra_repair_def repair_pair_def FWI'_def FWI_def
  by simp (intro abstra_upd_int_preservation fwi_int_preservation; (assumption | simp))

(* XXX Unused *)
lemma abstr_repair_int:
  assumes
    "dbm_int (curry M) n" "\<forall>c\<in>collect_clks cc. c \<le> n" "\<forall> (_,d) \<in> collect_clock_pairs cc. d \<in> \<int>"
  shows "dbm_int (curry (abstr_repair cc M)) n"
  using assms
  unfolding abstr_repair_def
  apply (induction cc arbitrary: M)
   apply (simp; fail)
  by (drule abstra_repair_int; auto simp: collect_clock_pairs_def)

lemma E_op'_FW_norm:
  "\<exists> M'.
    E_op' l r g l' M = FW' (norm_upd M' (k' l') n) n
    \<and> dbm_default (curry M') n \<and> dbm_int (curry M') n"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "dbm_default (curry M) n"
proof -
  note default_intros = up_canonical_upd_default reset'_upd_default abstr_repair_default
  (* XXX Duplication *)
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  let ?M = "
    curry (
       abstr_repair (inv_of A l')
         (reset'_upd (abstr_repair g (abstr_repair (inv_of A l) (up_canonical_upd M n))) n r 0))"
  have "dbm_default ?M n"
    by (intro default_intros[unfolded collect_clks_def] side_conds)
  moreover have "dbm_int ?M n"
    by (auto simp: Ints_def)
  ultimately show ?thesis unfolding E_op'_def by auto
qed

lemma filter_diag_default:
  assumes "\<And> M. dbm_default (curry M) n \<Longrightarrow> dbm_default (curry (f M)) n" "dbm_default (curry M) n"
  shows "dbm_default (curry (filter_diag f M)) n"
  unfolding filter_diag_def using assms by auto

lemma E_op''_FW_norm:
  "\<exists> M'.
    E_op'' l r g l' M = FW' (norm_upd M' (k' l') n) n
    \<and> dbm_default (curry M') n \<and> dbm_int (curry M') n"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "dbm_default (curry M) n" "\<not> check_diag n (E_op'' l r g l' M)"
proof -
  note default_intros =
    filter_diag_default up_canonical_upd_default reset'_upd_default abstr_repair_default
  (* XXX Duplication *)
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  let ?M = "
    filter_diag (\<lambda>M. abstr_repair (inv_of A l') (reset'_upd M n r 0))
      (filter_diag (abstr_repair g) (abstr_repair (inv_of A l) (up_canonical_upd M n)))"
  have "dbm_default (curry ?M) n"
    by (intro default_intros[unfolded collect_clks_def] side_conds)
  moreover have "dbm_int (curry ?M) n"
    by (auto simp: Ints_def)
  ultimately show ?thesis
    using that(3) unfolding E_op''_def by (auto simp: Let_def filter_diag_def)
qed

lemma E_op''_check_diag_aux:
  "check_diag n (abstr_repair (inv_of A l) (up_canonical_upd M n))" if "check_diag n M"
  apply (intro abstr_repair_check_diag_preservation check_diag_up_canonical_upd)
  using that collect_clks_inv_clk_set[of A l] clock_range unfolding collect_clks_def by blast+

lemma E_op''_check_diag:
  "check_diag n (E_op'' l r g l' M)" if "check_diag n M"
  using that E_op''_check_diag_aux unfolding E_op''_def filter_diag_def by (auto simp: Let_def)

sublocale E_op'': E_From_Op_Bisim_Finite _ _ _ _ _ E_op''
  by standard (rule E_op''_bisim' E_op''_wf E_op''_FW_norm E_op''_check_diag; assumption)+

end (* End of context for reachability problem*)

end (* End of theory *)