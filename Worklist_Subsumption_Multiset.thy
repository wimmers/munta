(* Authors: Lammich, Wimmer *)
section \<open>Generic Worklist Algorithm with Subsumption\<close>
theory Worklist_Subsumption_Multiset
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

context Search_Space_Defs_Empty begin
  definition "worklist_var = inv_image (finite_psupset (Collect reachable) <*lex*> measure size) (\<lambda> (a, b,c). (a,b))"

  definition "worklist_inv_frontier passed wait =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set_mset wait. a' \<preceq> b'))"

  definition "start_subsumed passed wait = (\<exists> a \<in> passed \<union> set_mset wait. a\<^sub>0 \<preceq> a)"

  definition "worklist_inv \<equiv> \<lambda> (passed, wait, brk).
    passed \<subseteq> Collect reachable \<and>
    (brk \<longrightarrow> (\<exists> f. reachable f \<and> F f)) \<and>
    (\<not> brk \<longrightarrow>
      worklist_inv_frontier passed wait
    \<and> (\<forall> a \<in> passed \<union> set_mset wait. \<not> F a)
    \<and> start_subsumed passed wait
    \<and> set_mset wait \<subseteq> Collect reachable)
    "

  definition "add_succ_spec wait a \<equiv> SPEC (\<lambda>(wait',brk).
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set_mset wait' \<subseteq> set_mset wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set_mset wait \<union> {a' . E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait'. s \<preceq> s')
  )"

  definition worklist_algo where
    "worklist_algo = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = {#a\<^sub>0#};
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_mset wait;
                ASSERT (reachable a);
                if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ_spec wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
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

  lemma wf_worklist_var:
    "wf worklist_var"
  unfolding worklist_var_def by (auto simp: finite_reachable)

  context
  begin

  private lemma aux1:
    assumes "\<forall>x\<in>passed. \<not> a \<preceq> x"
        and "passed \<subseteq> Collect reachable"
        and "reachable a"
    shows "
    ((insert a passed, wait', brk'),
     passed, wait, brk)
    \<in> worklist_var"
  proof -
    from assms have "a \<notin> passed" by auto
    with assms(2,3) show ?thesis
    by (auto simp: worklist_inv_def worklist_var_def finite_psupset_def)
  qed

  private lemma aux2:
    assumes
      "a' \<in> passed"
      "a \<preceq> a'"
      "a \<in># wait"
      "worklist_inv_frontier passed wait"
    shows "worklist_inv_frontier passed (wait - {#a#})"
    using assms unfolding worklist_inv_frontier_def
    using trans
    apply clarsimp
    by (metis (no_types, lifting) Un_iff count_eq_zero_iff count_single mset_contains_eq mset_un_cases)

  private lemma aux5:
    assumes
      "a' \<in> passed"
      "a \<preceq> a'"
      "a \<in># wait"
      "start_subsumed passed wait"
    shows "start_subsumed passed (wait - {#a#})"
    using assms unfolding start_subsumed_def apply clarsimp
    by (metis Un_iff insert_DiffM2 local.trans mset_right_cancel_elem)

  (* XXX Move to misc *)
  lemma mset_remove_member:
    "x \<in># A - B" if "x \<in># A" "x \<notin># B"
    using that
    by (metis count_greater_zero_iff in_diff_count not_in_iff)

  private lemma aux3:
    assumes
      "set_mset wait \<subseteq> Collect reachable"
      "a \<in># wait"
      "\<forall> s \<in> set_mset (wait - {#a#}) \<union> {a'. E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait'. s \<preceq> s'"
      "worklist_inv_frontier passed wait"
    shows "worklist_inv_frontier (insert a passed) wait'"
  proof -
    from assms(1,2) have "reachable a"
      by (simp add: subset_iff)
    with finitely_branching have [simp, intro!]: "finite (Collect (E a))" .

    show ?thesis unfolding worklist_inv_frontier_def
      apply safe
      subgoal
        using assms by auto
      subgoal for b b'
      proof -
        assume A: "E b b'" "\<not> empty b'" "b \<in> passed"
        with assms obtain b'' where b'': "b'' \<in> passed \<union> set_mset wait" "b' \<preceq> b''"
          unfolding worklist_inv_frontier_def by blast
        from this(1) show ?thesis
          apply standard
          subgoal
            using \<open>b' \<preceq> b''\<close> by auto
          subgoal
            apply (cases "a = b''")
            subgoal
              using b''(2) by blast
            subgoal premises prems
            proof -
              from prems have "b'' \<in># wait - {#a#}"
                by (auto simp: mset_remove_member)
              with assms prems \<open>b' \<preceq> b''\<close> show ?thesis
                by (blast intro: local.trans)
            qed
            done
          done
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
    assumes "worklist_inv_frontier passed {#}" "reachable x" "start_subsumed passed {#}"
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
            unfolding worklist_inv_frontier_def by auto
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

  theorem worklist_algo_correct:
    "worklist_algo \<le> SPEC (\<lambda> brk. brk \<longleftrightarrow> F_reachable)"
  proof -
    note [simp] = size_Diff_submset pred_not_lt_is_zero
    note [dest] = set_mset_mp
    show ?thesis
    unfolding worklist_algo_def add_succ_spec_def F_reachable_def
      apply (refine_vcg wf_worklist_var)
      (* F a\<^sub>0*)
      apply (auto; fail)
      (* Invar start*)
      apply (auto simp: worklist_inv_def worklist_inv_frontier_def start_subsumed_def; fail)
      (* Precondition for take-from-set *)
      apply (simp; fail)
      (* State is subsumed by passed*)
        (* Assertion *)
        apply (auto simp: worklist_inv_def; fail)
        (*Invariant*)
        apply (auto simp: worklist_inv_def aux2 aux5
              dest: in_diffD
              split: if_split_asm; fail)
        (*Variant*)
        apply (auto simp: worklist_inv_def worklist_var_def intro: finite_subset[OF _ finite_reachable]; fail)

      (* Insert successors to wait *)
        (*Invariant*)
        apply (clarsimp split: if_split_asm) (* Split on F in successors *)
          (* Found final state *)
          apply (clarsimp simp: worklist_inv_def; blast intro: step_reachable; fail)
          (* No final state *)
      apply (auto
        simp: worklist_inv_def aux3 aux6 finitely_branching
        dest: in_diffD)[]
       apply (metis Un_iff in_diffD insert_subset mem_Collect_eq mset_add set_mset_add_mset_insert)
    subgoal for ab aaa baa aba aca _ x
    proof -
      (* s/h alternative: *)
      (* by (metis (mono_tags, hide_lams) Un_iff in_diffD mem_Collect_eq step_reachable subsetCE *)
      assume
        "reachable aba"
        "set_mset aca \<subseteq> set_mset (aaa - {#aba#}) \<union> Collect (E aba)"
        "set_mset aaa \<subseteq> Collect reachable"
        "x \<in># aca"
      then show ?thesis
        by (auto intro: step_reachable dest: in_diffD)
    qed
        apply (auto simp: worklist_inv_def aux1; fail)
      (* I \<and> \<not> b \<longrightarrow> post *)
      using F_mono by (fastforce simp: worklist_inv_def dest!: aux4)
  qed

  lemmas [refine_vcg] = worklist_algo_correct[THEN order_trans]

  end -- \<open>Context\<close>

end -- \<open>Search Space\<close>


context Search_Space''_Defs
begin

  definition "worklist_inv_frontier' passed wait =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set_mset wait. a' \<preceq> b'))"

  definition "start_subsumed' passed wait = (\<exists> a \<in> passed \<union> set_mset wait. a\<^sub>0 \<preceq> a)"

definition "worklist_inv' \<equiv> \<lambda> (passed, wait, brk).
  worklist_inv (passed, wait, brk) \<and> (\<forall> a \<in> passed. \<not> empty a) \<and> (\<forall> a \<in> set_mset wait. \<not> empty a)
    "

  (*
  definition "add_succ_spec' wait a \<equiv> SPEC (\<lambda>(wait',brk).
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set_mset wait' \<subseteq> set_mset wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set_mset wait \<union> {a' . E a a'}. \<not> empty s \<longrightarrow> (\<exists> s' \<in> set_mset wait'. s \<preceq> s')) \<and>
      (\<forall> s \<in> set_mset wait'. \<not> empty s)
  )"

  definition "add_succ_spec wait a \<equiv> SPEC (\<lambda>(wait',brk).
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set_mset wait' \<subseteq> set_mset wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set_mset wait \<union> {a' . E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait'. s \<preceq> s')
  )"
*)

definition "add_succ_spec' wait a \<equiv> SPEC (\<lambda>(wait',brk).
  (
  if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set_mset wait' \<subseteq> set_mset wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set_mset wait \<union> {a' . E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait'. s \<preceq> s')
  ) \<and> (\<forall> s \<in> set_mset wait'. \<not> empty s)
  )"

  definition worklist_algo' where
    "worklist_algo' = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = {#a\<^sub>0#};
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv' (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_mset wait;
                ASSERT (reachable a);
                if (\<exists> a' \<in> passed. a \<unlhd> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ_spec' wait a;
                    let passed = insert a passed;
                    RETURN (passed, wait, brk)
                  }
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

end -- \<open>Search Space'' Defs\<close>


context Search_Space''_start
begin

lemma worklist_algo_list_inv_ref[refine]:
    fixes x x'
    assumes
      "\<not> F a\<^sub>0" "\<not> F a\<^sub>0"
      "(x, x') \<in> {((passed,wait,brk), (passed',wait',brk')). passed = passed' \<and> wait = wait' \<and> brk = brk' \<and> (\<forall> a \<in> passed. \<not> empty a) \<and> (\<forall> a \<in> set_mset wait. \<not> empty a)}"
      "worklist_inv x'"
    shows "worklist_inv' x"
    using assms
    unfolding worklist_inv'_def worklist_inv_def
    by auto

lemma [refine]:
  "take_from_mset wait \<le> \<Down> {((x, wait), (y, wait')). x = y \<and> wait = wait' \<and> \<not> empty x \<and> (\<forall> a \<in> set_mset wait. \<not> empty a)} (take_from_mset wait')"
  if "wait = wait'" "\<forall> a \<in> set_mset wait. \<not> empty a" "wait \<noteq> {#}"
  using that
  by (auto 4 5 simp: pw_le_iff refine_pw_simps dest: in_diffD dest!: take_from_mset_correct)

lemma [refine]:
  "add_succ_spec' wait x \<le> \<Down> ({(wait, wait'). wait = wait' \<and> (\<forall> a \<in> set_mset wait. \<not> empty a)} \<times>\<^sub>r bool_rel) (add_succ_spec wait' x')"
  if "wait = wait'" "x = x'" "\<forall> a \<in> set_mset wait. \<not> empty a"
  using that
  unfolding add_succ_spec'_def add_succ_spec_def
  by (auto simp: pw_le_iff refine_pw_simps)

lemma worklist_algo'_ref[refine]: "worklist_algo' \<le> \<Down>Id worklist_algo"
  using [[goals_limit=15]]
    unfolding worklist_algo'_def worklist_algo_def
    apply (refine_rcg)
               prefer 3
      apply assumption
                  apply refine_dref_type
      by (auto simp: empty_subsumes')

end -- \<open>Search Space'' Start\<close>


context Search_Space''_Defs
begin

definition worklist_algo'' where
  "worklist_algo'' \<equiv>
    if empty a\<^sub>0 then RETURN False else worklist_algo'
  "

end -- \<open>Search Space'' Defs\<close>


context Search_Space''
begin

lemma worklist_algo''_correct:
  "worklist_algo'' \<le> SPEC (\<lambda> brk. brk \<longleftrightarrow> F_reachable)"
proof (cases "empty a\<^sub>0")
  case True
  then show ?thesis
    unfolding worklist_algo''_def F_reachable_def reachable_def
    using empty_E_star final_non_empty by auto
next
  case False
  interpret Search_Space''_start
    by standard (rule \<open>\<not> empty _\<close>)
  note worklist_algo'_ref
  also note worklist_algo_correct
  finally show ?thesis
    using False unfolding worklist_algo''_def by simp
qed

end -- \<open>Search Space''\<close>


end -- \<open>End of Theory\<close>