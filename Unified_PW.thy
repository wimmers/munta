theory Unified_PW
  imports "$AFP/Refine_Imperative_HOL/Sepref" Worklist_Locales
begin

subsection \<open>Utilities\<close>

definition take_from_set where
  "take_from_set s = ASSERT (s \<noteq> {}) \<then> SPEC (\<lambda> (x, s'). x \<in> s \<and> s' = s - {x})"

lemma take_from_set_correct:
  assumes "s \<noteq> {}"
  shows "take_from_set s \<le> SPEC (\<lambda> (x, s'). x \<in> s \<and> s' = s - {x})"
using assms unfolding take_from_set_def by simp

lemmas [refine_vcg] = take_from_set_correct[THEN order.trans]



definition take_from_mset where
  "take_from_mset s = ASSERT (s \<noteq> {#}) \<then> SPEC (\<lambda> (x, s'). x \<in># s \<and> s' = s - {#x#})"

lemma take_from_mset_correct:
  assumes "s \<noteq> {#}"
  shows "take_from_mset s \<le> SPEC (\<lambda> (x, s'). x \<in># s \<and> s' = s - {#x#})"
using assms unfolding take_from_mset_def by simp

lemmas [refine_vcg] = take_from_mset_correct[THEN order.trans]


lemma set_mset_mp: "set_mset m \<subseteq> s \<Longrightarrow> n < count m x \<Longrightarrow> x\<in>s"
  by (meson count_greater_zero_iff le_less_trans subsetCE zero_le)

lemma pred_not_lt_is_zero: "(\<not> n - Suc 0 < n) \<longleftrightarrow> n=0" by auto


context Search_Space
begin

  lemma start_reachable[intro!, simp]:
    "reachable a\<^sub>0"
  unfolding reachable_def by simp

  lemma step_reachable:
    assumes "reachable a" "E a a'"
    shows "reachable a'"
  using assms unfolding reachable_def by simp


  lemma finitely_branching:
    assumes "reachable a"
    shows "finite (Collect (E a))"
    by (metis assms finite_reachable finite_subset mem_Collect_eq step_reachable subsetI)

end -- \<open>Search Space\<close>

subsection \<open>Worklist Algorithm\<close>

context Search_Space_Defs_Empty
begin
  definition "reachable_subsumed S = {x' | x x'. reachable x' \<and> x' \<preceq> x \<and> x \<in> S}"
  (* definition "worklist_var = inv_image (finite_psupset (Collect reachable) <*lex*> measure size) (\<lambda> (a, b,c). (a,b))" *)
  definition
    "pw_var =
      inv_image (
      {(b, b'). b \<and> \<not> b'}
        <*lex*>
      {(passed', passed).
        passed' \<subseteq> Collect reachable \<and> passed \<subseteq> Collect reachable \<and>
        reachable_subsumed passed \<subset> reachable_subsumed passed'}
        <*lex*>
      measure size
      )
      (\<lambda> (a, b, c). (c, a, b))
      "

  definition "pw_inv_frontier passed wait =
    (\<forall> a \<in> passed. (\<exists> a' \<in> set_mset wait. a \<preceq> a') \<or>
    (\<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set_mset wait. a' \<preceq> b')))"

  definition "start_subsumed passed wait = (\<exists> a \<in> passed \<union> set_mset wait. a\<^sub>0 \<preceq> a)"

  definition "pw_inv \<equiv> \<lambda> (passed, wait, brk).
    (brk \<longrightarrow> (\<exists> f. reachable f \<and> F f)) \<and>
    (\<not> brk \<longrightarrow>
      passed \<subseteq> Collect reachable
    \<and> pw_inv_frontier passed wait
    \<and> (\<forall> a \<in> passed \<union> set_mset wait. \<not> F a)
    \<and> start_subsumed passed wait
    \<and> set_mset wait \<subseteq> Collect reachable)
    "

  definition "add_pw_spec passed wait a \<equiv> SPEC (\<lambda>(passed',wait',brk).
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set_mset wait' \<subseteq> set_mset wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set_mset wait. \<exists> s' \<in> set_mset wait'. s \<preceq> s') \<and>
      (\<forall> s \<in> {a' . E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait' \<union> passed. s \<preceq> s') \<and>
      (\<forall> s \<in> passed \<union> {a}. \<exists> s' \<in> passed'. s \<preceq> s') \<and>
      (passed' \<subseteq> passed \<union> {a} \<union> {a' . E a a'} \<and>
      ((\<exists> x \<in> passed'. \<not> (\<exists> x' \<in> passed. x \<preceq> x')) \<or> wait' \<subseteq># wait \<and> passed = passed')
      )
  )"

  definition "init_pw_spec \<equiv> SPEC (\<lambda> (passed, wait). wait = {#a\<^sub>0#} \<and> passed \<subseteq> {a\<^sub>0})"

  abbreviation subsumed_elem :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
    where "subsumed_elem a M \<equiv> \<exists> a'. a' \<in> M \<and> a \<preceq> a'"

  notation
    subsumed_elem  ("op \<in>'") and
    subsumed_elem  ("(_/ \<in>' _)" [51, 51] 50)

    definition "pw_inv_frontier' passed wait =
      (\<forall> a. a \<in> passed \<longrightarrow>
        (a \<in>' set_mset wait)
      \<or> (\<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (a' \<in>' passed \<union> set_mset wait)))"

  lemma pw_inv_frontier_frontier':
    "pw_inv_frontier' passed wait" if
    "pw_inv_frontier passed wait" "passed \<subseteq> Collect reachable"
    using that unfolding pw_inv_frontier'_def pw_inv_frontier_def by (blast intro: trans)

  lemma
    "pw_inv_frontier passed wait" if "pw_inv_frontier' passed wait"
    using that
    unfolding pw_inv_frontier_def
    apply safe
    using that
    unfolding pw_inv_frontier'_def
    by blast

  definition pw_algo where
    "pw_algo = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          (passed, wait) \<leftarrow> init_pw_spec;
          (passed, wait, brk) \<leftarrow> WHILEIT pw_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_mset wait;
                ASSERT (reachable a);
                add_pw_spec passed wait a
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

end

subsubsection \<open>Correctness Proof\<close>

context Search_Space begin

  lemma wf_worklist_var_aux:
    "wf {(passed', passed).
      passed' \<subseteq> Collect reachable \<and> passed \<subseteq> Collect reachable \<and>
      reachable_subsumed passed \<subset> reachable_subsumed passed'}"
  proof (rule finite_acyclic_wf, goal_cases)
    case 1
    have "{(passed', passed).
        passed' \<subseteq> Collect reachable \<and> passed \<subseteq> Collect reachable \<and>
        reachable_subsumed passed \<subset> reachable_subsumed passed'}
        \<subseteq> {(passed', passed). passed \<subseteq> Collect reachable \<and> passed' \<subseteq> Collect reachable}"
      unfolding reachable_subsumed_def by auto
    moreover have "finite \<dots>" using finite_reachable using [[simproc add: finite_Collect]] by simp
    ultimately show ?case by (rule finite_subset)
  next
    case 2
    show ?case
    proof (rule acyclicI_order[where f = "\<lambda> a. card (reachable_subsumed a)"], rule psubset_card_mono)
      fix a
      have "reachable_subsumed a \<subseteq> Collect reachable" unfolding reachable_subsumed_def by blast
      then show "finite (reachable_subsumed a)" using finite_reachable by (rule finite_subset)
    qed auto
  qed

  lemma wf_worklist_var:
    "wf pw_var"
    unfolding pw_var_def
    apply (auto intro: wf_worklist_var_aux)
    by (auto intro!: finite_acyclic_wf acyclicI_order[where f = id])

  context
  begin

  private lemma aux5:
    assumes
      "a' \<in> passed'"
      "a \<in># wait"
      "a \<preceq> a'"
      "start_subsumed passed wait"
      "\<forall>s\<in>passed. \<exists>x\<in>passed'. s \<preceq> x"
      "\<forall>s\<in>#wait - {#a#}. Multiset.Bex wait' (op \<preceq> s)"
    shows "start_subsumed passed' wait'"
      using assms unfolding start_subsumed_def apply clarsimp
    by (metis Un_iff insert_DiffM2 local.trans mset_right_cancel_elem)

  lemma aux3_aux:
    assumes "pw_inv_frontier' passed wait"
      "\<not> b \<in>' set_mset wait"
      "E b b'"
      "\<not> empty b" "\<not> empty b'"
      "b \<in>' passed"
      "reachable b" "passed \<subseteq> Collect reachable"
    shows "b' \<in>' passed \<union> set_mset wait"
  proof -
    from \<open>b \<in>' _\<close> obtain b1 where b1: "b \<preceq> b1" "b1 \<in> passed"
      by blast
    with mono[OF this(1) \<open>E b b'\<close>] \<open>passed \<subseteq> _\<close> \<open>reachable b\<close> \<open>\<not> empty b\<close> obtain b1' where
      "E b1 b1'" "b' \<preceq> b1'"
      by auto
    moreover then have "\<not> empty b1'"
      using assms(5) empty_mono by blast
    moreover from assms b1 have "\<not> b1 \<in>' set_mset wait"
      by (blast intro: trans)
    ultimately show ?thesis
      using assms(1) b1
      unfolding pw_inv_frontier'_def
      by (blast intro: trans)
  qed


  private lemma aux3:
    assumes
      "set_mset wait \<subseteq> Collect reachable"
      "a \<in># wait"
      "\<forall> s \<in> set_mset (wait - {#a#}). \<exists> s' \<in> set_mset wait'. s \<preceq> s'"
      "\<forall> s \<in> {a'. E a a' \<and> \<not> empty a'}. \<exists> s' \<in> passed \<union> set_mset wait'. s \<preceq> s'"
      "\<forall> s \<in> passed \<union> {a}. \<exists> s' \<in> passed'. s \<preceq> s'"
      "passed' \<subseteq> passed \<union> {a} \<union> {a' . E a a'}"
      "pw_inv_frontier passed wait"
      "passed \<subseteq> Collect reachable"
    shows "pw_inv_frontier passed' wait'"
  proof -
    from assms(1,2) have "reachable a"
      by (simp add: subset_iff)
    from assms have assms':
      "set_mset wait \<subseteq> Collect reachable"
      "a \<in># wait"
      "\<forall> s. s \<in>' set_mset (wait - {#a#}) \<longrightarrow> s \<in>' set_mset wait'"
      "\<forall> s \<in> {a'. E a a' \<and> \<not> empty a'}. s \<in>' passed \<union> set_mset wait'"
      "\<forall> s. s \<in>' passed \<union> {a} \<longrightarrow> s \<in>' passed'"
      "passed' \<subseteq> passed \<union> {a} \<union> {a' . E a a'}"
      "pw_inv_frontier' passed wait"
      "passed \<subseteq> Collect reachable"
      by (blast intro: trans pw_inv_frontier_frontier')+

    show ?thesis unfolding pw_inv_frontier_def
      apply safe
      unfolding Bex_def
      subgoal for b b'
      proof (goal_cases)
        case A: 1
        from A(1) assms(6) consider "b \<in> passed" | "a = b" | "E a b"
          by auto
        note cases = this
        from cases \<open>\<not> b \<in>' set_mset wait'\<close> assms'(4) \<open>reachable a\<close> \<open>passed \<subseteq> _\<close> have "reachable b"
          by cases (auto intro: step_reachable)
        with A(3,4) have "\<not> empty b" by (auto simp: empty_E)
        from cases this \<open>reachable b\<close> consider "a = b" | "a \<noteq> b" "b \<in>' passed" "reachable b"
          apply cases
          using \<open>\<not> b \<in>' set_mset wait'\<close> assms'(4)
          by (fastforce intro: step_reachable)+
        then consider "b \<preceq> a" "reachable b" | "\<not> b \<preceq> a" "b \<in>' passed" "reachable b"
          apply cases
          using \<open>\<not> b \<in>' set_mset wait'\<close> assms'(4) \<open>reachable a\<close> by fastforce+
        then show ?case
        proof cases
          case 1
          with A(3,4) have "\<not> empty b"
            by (auto simp: empty_E)
          with mono[OF 1(1) \<open>E b b'\<close> 1(2) \<open>reachable a\<close>] obtain b1' where
            "E a b1'" "b' \<preceq> b1'"
            by auto
          with \<open>\<not> empty b'\<close> have "b1' \<in>' passed \<union> set_mset wait'"
            using assms'(4) by (auto dest: empty_mono)
          with \<open>b' \<preceq> _\<close> assms'(5) show ?thesis
            by (auto intro: trans)
        next
          case 2
          with A(3,4) have "\<not> empty b"
            by (auto simp: empty_E)
          from 2 \<open>\<not> b \<in>' set_mset wait'\<close> assms'(2,3) have "\<not> b \<in>' set_mset wait"
            by (metis insert_DiffM2 mset_right_cancel_elem)
          from
            aux3_aux[OF assms'(7) this \<open>E b b'\<close> \<open>\<not> empty b\<close> \<open>\<not> empty b'\<close> \<open>b \<in>' passed\<close> \<open>reachable b\<close> assms'(8)]
          have "b' \<in>' passed \<union> set_mset wait" .
          with assms'(2,3,5) show ?thesis
            by auto (metis insert_DiffM insert_noteq_member)
        qed
      qed
      done
  qed

  private lemma aux6:
    assumes
      "a \<in># wait"
      "start_subsumed passed wait"
      "\<forall> s \<in> set_mset (wait - {#a#}) \<union> {a'. E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait'. s \<preceq> s'"
    shows "start_subsumed (insert a passed) wait'"
    using assms unfolding start_subsumed_def
    apply clarsimp
    apply (erule disjE)
     apply blast
    subgoal premises prems for x
    proof (cases "a = x")
      case True
      with prems show ?thesis by simp
    next
      case False
      with \<open>x \<in># wait\<close> have "x \<in> set_mset (wait - {#a#})"
        by (metis insert_DiffM insert_noteq_member prems(1))
      with prems(2,4) \<open>_ \<preceq> x\<close> show ?thesis
        by (auto dest: trans)
    qed
  done

  lemma empty_E_star:
    "empty x'" if "E\<^sup>*\<^sup>* x x'" "reachable x" "empty x"
    using that unfolding reachable_def
    by (induction rule: converse_rtranclp_induct)
       (blast intro: empty_E[unfolded reachable_def] rtranclp.rtrancl_into_rtrancl)+

  lemma aux4:
    assumes "pw_inv_frontier passed {#}" "reachable x" "start_subsumed passed {#}"
            "passed \<subseteq> Collect reachable"
    shows "\<exists> x' \<in> passed. x \<preceq> x'"
  proof -
    from \<open>reachable x\<close> have "E\<^sup>*\<^sup>* a\<^sub>0 x" by (simp add: reachable_def)
    from assms(3) obtain b where "a\<^sub>0 \<preceq> b" "b \<in> passed" unfolding start_subsumed_def by auto
    have "\<exists>x'. \<exists> x''. E\<^sup>*\<^sup>* b x' \<and> x \<preceq> x' \<and> x' \<preceq> x'' \<and> x'' \<in> passed" if
                     "E\<^sup>*\<^sup>* a x"  "a \<preceq> b"   "b \<preceq> b'"   "b' \<in> passed"
                     "reachable a" "reachable b" for a b b'
    using that proof (induction arbitrary: b b' rule: converse_rtranclp_induct)
      case base
      then show ?case by auto
    next
      case (step a a1 b b')
      show ?case
      proof (cases "empty a")
        case True
        with step.prems step.hyps have "empty x" by - (rule empty_E_star, auto)
        with step.prems show ?thesis by (auto intro: empty_subsumes)
      next
        case False
        with \<open>E a a1\<close> \<open>a \<preceq> b\<close> \<open>reachable a\<close> \<open>reachable b\<close> obtain b1 where
          "E b b1" "a1 \<preceq> b1"
          using mono by blast
        show ?thesis
        proof (cases "empty b1")
          case True
          with empty_mono \<open>a1 \<preceq> b1\<close> have "empty a1" by blast
          with step.prems step.hyps have "empty x" by - (rule empty_E_star, auto simp: reachable_def)
          with step.prems show ?thesis by (auto intro: empty_subsumes)
        next
          case False
          from \<open>E b b1\<close> \<open>a1 \<preceq> b1\<close> obtain b1' where "E b' b1'" "b1 \<preceq> b1'"
            using \<open>\<not> empty a\<close> empty_mono assms(4) mono step.prems by blast
          from empty_mono[OF \<open>\<not> empty b1\<close> \<open>b1 \<preceq> b1'\<close>] have "\<not> empty b1'"
            by auto
          with \<open>E b' b1'\<close> \<open>b' \<in> passed\<close> assms(1) obtain b1'' where "b1'' \<in> passed" "b1' \<preceq> b1''"
            unfolding pw_inv_frontier_def by auto
          with \<open>b1 \<preceq> _\<close> have "b1 \<preceq> b1''" using trans by blast
          with step.IH[OF \<open>a1 \<preceq> b1\<close> this \<open>b1'' \<in> passed\<close>] \<open>reachable a\<close> \<open>E a a1\<close> \<open>reachable b\<close> \<open>E b b1\<close>
          obtain x' x'' where
            "E\<^sup>*\<^sup>* b1 x'" "x \<preceq> x'" "x' \<preceq> x''" "x'' \<in> passed"
            by (auto intro: step_reachable)
          moreover from \<open>E b b1\<close> \<open>E\<^sup>*\<^sup>* b1 x'\<close> have "E\<^sup>*\<^sup>* b x'" by auto
          ultimately show ?thesis by auto
        qed
      qed
    qed
    from this[OF \<open>E\<^sup>*\<^sup>* a\<^sub>0 x\<close> \<open>a\<^sub>0 \<preceq> b\<close> refl \<open>b \<in> _\<close>] assms(4) \<open>b \<in> passed\<close> show ?thesis
      by (auto intro: trans)
  qed

  lemmas [intro] = step_reachable

  lemma aux7:
    assumes
      "a \<in># wait"
      "set_mset wait \<subseteq> Collect reachable"
      "set_mset wait' \<subseteq> set_mset (wait - {#a#}) \<union> Collect (E a)"
      "x \<in># wait'"
    shows "reachable x"
    using assms by (auto dest: in_diffD)

  lemma aux8:
    "x \<in> reachable_subsumed S'"  if "x \<in> reachable_subsumed S" "\<forall>s\<in>S. \<exists>x\<in>S'. s \<preceq> x"
    using that unfolding reachable_subsumed_def by (auto intro: trans)

  lemma aux9:
    assumes
      "set_mset wait' \<subseteq> set_mset (wait - {#a#}) \<union> Collect (E a)"
      "x \<in># wait'" "\<forall>a'. E a a' \<longrightarrow> \<not> F a'" "F x"
      "\<forall>a\<in>passed \<union> set_mset wait. \<not> F a"
    shows False
  proof -
    from assms(1,2) have "x \<in> set_mset wait \<or> x \<in> Collect (E a)"
      by (meson UnE in_diffD subsetCE)
    with assms(3,4,5) show ?thesis
      by auto
  qed

  theorem pw_algo_correct:
    "pw_algo \<le> SPEC (\<lambda> brk. brk \<longleftrightarrow> F_reachable)"
  proof -
    note [simp] = size_Diff_submset pred_not_lt_is_zero
    note [dest] = set_mset_mp
    show ?thesis
    unfolding pw_algo_def init_pw_spec_def add_pw_spec_def F_reachable_def
      apply (refine_vcg wf_worklist_var)
      (* F a\<^sub>0*)
      apply (auto; fail)
      (* Invar start*)
      apply (auto simp: pw_inv_def pw_inv_frontier_def start_subsumed_def; fail)
      (* Precondition for take-from-set *)
      apply (simp; fail)
      (* State is subsumed by passed*)
        (* Assertion *)
        apply (auto simp: pw_inv_def; fail)
        (*Invariant*)
      subgoal for _ passed _ wait brk _ a wait'
      apply (clarsimp simp: pw_inv_def split: if_split_asm)
      apply safe
        apply (auto dest: in_diffD; fail)+
          subgoal
            by (rule aux3; auto)
          subgoal
            by (auto dest: in_diffD; fail)
          subgoal
            by (auto intro: aux9)
          subgoal
            by (rule aux5; auto)
          subgoal
            by (rule aux7; auto)
          subgoal
            by (rule aux3; auto)
          subgoal
            by (auto dest: in_diffD; fail)
          subgoal
            by (auto intro: aux9)
          subgoal
            by (rule aux5; auto)
          apply (simp add: aux7)
          subgoal
            by (auto dest: in_diffD; fail)
          done
        (*Variant*)
        subgoal for  _ _ _ _ passed _ wait brk _ a wait'
          apply (clarsimp simp: pw_inv_def split: if_split_asm)
          apply safe
            apply (auto; fail)
          subgoal premises prems for passed' wait'' brk' a' a''
          proof -
            have "passed' \<subseteq> Collect reachable"
              using prems by auto
            moreover have "reachable_subsumed passed \<subset> reachable_subsumed passed'"
              unfolding reachable_subsumed_def apply auto
              subgoal
                using \<open>\<forall>s\<in>passed. \<exists>x\<in>passed'. s \<preceq> x\<close> by (auto intro: trans)
              using prems(22-) \<open>passed' \<subseteq> Collect reachable\<close> by auto
            ultimately show ?thesis
              using \<open>passed \<subseteq> _\<close> unfolding pw_var_def by auto
          qed
          subgoal premises prems for passed' wait'' brk'
            unfolding pw_var_def
            using \<open>wait'' \<subseteq># _\<close> Diff_eq_empty_iff_mset mset_subset_size prems(12) subset_mset_def
            by fastforce
          subgoal for passed' wait'' brk'
            unfolding pw_var_def by auto
          done
      (* I \<and> \<not> b \<longrightarrow> post *)
      using F_mono by (fastforce simp: pw_inv_def dest!: aux4)
  qed

  lemmas [refine_vcg] = pw_algo_correct[THEN order_trans]

  end -- \<open>Context\<close>

end -- \<open>Search Space\<close>

end -- \<open>End of Theory\<close>