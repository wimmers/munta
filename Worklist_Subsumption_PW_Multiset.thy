(* Authors: Lammich, Wimmer *)
section \<open>Generic Worklist Algorithm with Subsumption\<close>
theory Worklist_Subsumption_PW_Multiset
  imports "$AFP/Refine_Imperative_HOL/Sepref" Unified_PW
begin

subsection \<open>Worklist Algorithm\<close>

(* XXX Move to misc *)
lemma mset_remove_member:
  "x \<in># A - B" if "x \<in># A" "x \<notin># B"
  using that
  by (metis count_greater_zero_iff in_diff_count not_in_iff)

context Search_Space_Defs_Empty begin

  definition "worklist_inv_frontier passed wait =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set_mset wait. a' \<preceq> b'))"

  definition "add_succ_spec wait a \<equiv> SPEC (\<lambda>(wait',brk).
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set_mset wait' \<subseteq> set_mset wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set_mset wait \<union> {a' . E a a' \<and> \<not> empty a'}. \<exists> s' \<in> set_mset wait'. s \<preceq> s')
  )"

  definition "worklist_inv \<equiv> \<lambda> (passed, wait, brk).
    pw_inv (passed, wait, brk) \<and>
    \<not> brk \<longrightarrow> worklist_inv_frontier passed wait (* \<and>
    (\<forall> a \<in> set_mset wait. \<not> empty a) *)
    "

  definition worklist_algo where
    "worklist_algo = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          (passed, wait) \<leftarrow> RETURN ({}, {#a\<^sub>0#});
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

context Search_Space' begin

  lemma add_succs_ref_aux_1:
    "(if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
        do
          {
            (wait,brk) \<leftarrow> add_succ_spec wait a;
            let passed = insert a passed;
            RETURN (passed, wait, brk)
          }
      ) \<le> \<Down> Id (add_pw_spec passed' wait' a')"
    if "(\<forall> a \<in> passed \<union> set_mset wait. \<not> F a)" "worklist_inv_frontier passed (wait + {#a#})"
    "reachable a" "passed \<union> set_mset wait \<subseteq> Collect reachable" "\<not> brk" "\<not> F a"
    "(wait, wait') \<in> Id" "(passed, passed') \<in> Id" "(a, a') \<in> Id"
    unfolding add_pw_spec_def using that
    apply auto
    subgoal for b a'
      unfolding worklist_inv_frontier_def
      apply (frule final_non_empty)
      apply clarsimp
      apply (drule mono, assumption, simp, blast, blast dest: empty_E)
      by (blast intro: F_mono trans dest: empty_mono)
    subgoal
      unfolding add_succ_spec_def by (auto simp: pw_le_iff refine_pw_simps)
    subgoal premises prems for a'' b
    proof -
      from prems obtain b' where b': "E a'' b'" "b \<preceq> b'"
        by (metis (mono_tags, lifting) empty_E mono subset_Collect_conv)
      with prems have "\<not> empty b'" by - (rule empty_mono)
      with b' prems(2) \<open>a'' \<in> passed'\<close> consider "b' \<preceq> a'" | "\<exists>x\<in>passed' \<union> set_mset wait'. b' \<preceq> x"
        unfolding worklist_inv_frontier_def by auto
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          by (meson b'(2) local.trans prems(12) prems(13) subsetCE sup.cobounded2)
      next
        case 2
        with b'(2) show ?thesis by (auto intro: trans)
      qed
    qed
    unfolding add_succ_spec_def by (auto simp: pw_le_iff refine_pw_simps)

context
begin

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

lemma multiset_add_remove:
  "ms + {#a#} - {#a#} = ms"
  by simp

lemma multiset_add_remove:
  "ms \<union># {#a#} - {#a#} = ms"
  oops

  lemma add_succs_ref_aux_2:
    "(if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
        do
          {
            (wait,brk) \<leftarrow> add_succ_spec wait a;
            let passed = insert a passed;
            RETURN (passed, wait, brk)
          }
      ) \<le> SPEC (\<lambda> (passed, wait, brk). (\<not> brk \<longrightarrow> worklist_inv_frontier passed wait))"
    if "worklist_inv_frontier passed (wait + {#a#})" "reachable a"
       "passed \<union> set_mset wait \<subseteq> Collect reachable"
    using that
    apply clarsimp
    apply safe
    subgoal
      unfolding worklist_inv_frontier_def by (auto intro: trans)
    subgoal
      unfolding add_succ_spec_def
      apply (auto simp add: pw_le_iff refine_pw_simps)
      apply (rule aux3)
         prefer 4
         apply assumption
      defer
        apply (simp; fail)
        (* s/h *)
        apply (simp add: worklist_inv_frontier_def)
      by (simp add: multiset_add_remove; fail)
    done

end -- \<open>Private context\<close>

lemma add_succs_ref[refine]:
  "(if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
      do
        {
          (wait,brk) \<leftarrow> add_succ_spec wait a;
          let passed = insert a passed;
          RETURN (passed, wait, brk)
        }
    ) \<le>
    \<Down> {((passed, wait, brk),(passed', wait',brk')).
        passed = passed' \<and> wait = wait' \<and> brk = brk' \<and>
        (\<not> brk \<longrightarrow> worklist_inv_frontier passed wait)} (add_pw_spec passed' wait' a')"
  if "(\<forall> a \<in> passed \<union> set_mset wait. \<not> F a)" "worklist_inv_frontier passed (wait + {#a#})"
  "reachable a" "passed \<union> set_mset wait \<subseteq> Collect reachable" "\<not> brk" "\<not> F a"
  "(wait, wait') \<in> Id" "(passed, passed') \<in> Id" "(a, a') \<in> Id"
  using add_succs_ref_aux_1[OF that] add_succs_ref_aux_2[OF that(2-4)]
  by (simp add: pw_le_iff refine_pw_simps)

lemma [refine]:
  "take_from_mset wait \<le>
    \<Down> {((x, wait), (y, wait')).
      x = y \<and> wait = wait' \<and> (\<forall> a \<in> set_mset wait. \<not> F a) \<and> set_mset wait \<subseteq> Collect reachable \<and>
      worklist_inv_frontier passed (wait + {#x#}) \<and> \<not> F x} (take_from_mset wait')"
  if "wait = wait'" "wait \<noteq> {#}" "(\<forall> a \<in> set_mset wait. \<not> F a)" "set_mset wait \<subseteq> Collect reachable"
      "worklist_inv_frontier passed wait"
  using that
  by (auto 4 5 simp: pw_le_iff refine_pw_simps dest: in_diffD dest!: take_from_mset_correct)
    (*
  unfolding worklist_inv_frontier_def
  using take_from_mset_correct[OF \<open>wait \<noteq> _\<close>]
  apply (auto simp: pw_le_iff)
  apply (drule spec)
  apply (drule spec)
  apply (erule impE, assumption)
    (*
proof -
  fix a :: 'a and b :: "'a multiset" and aa :: 'a and a' :: 'a
  assume a1: "E aa a'"
  assume a2: "\<not> empty a'"
  assume a3: "\<forall>a\<in>passed. \<forall>a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists>x\<in>passed \<union> set_mset wait'. a' \<preceq> x)"
  assume a4: "aa \<in> passed"
  assume a5: "\<forall>x\<in>passed \<union> set_mset b. \<not> a' \<preceq> x"
  assume a6: "a \<in># wait' \<and> b = wait' - {#a#}"
  obtain aaa :: "'a \<Rightarrow> 'a" where
    "\<forall>x0. (x0 \<in>' passed \<union> set_mset wait') = (aaa x0 \<in> passed \<union> set_mset wait' \<and> x0 \<preceq> aaa x0)"
    by moura
  then have f7: "aaa a' \<in> passed \<union> set_mset wait' \<and> a' \<preceq> aaa a'"
    using a4 a3 a2 a1 by (simp add: Bex_def_raw)
  have "\<forall>a m. (a::'a) \<notin># m \<or> add_mset a (m - {#a#}) = m"
    by simp
  then show "a' \<preceq> a"
    using f7 a6 a5 by (metis (no_types) Un_insert_right insert_iff set_mset_add_mset_insert)
qed
*)
  by (metis Un_insert_right insert_DiffM insert_iff set_mset_add_mset_insert) *)

lemma [refine]:
  "RETURN ({}, {#a\<^sub>0#}) \<le> \<Down> (Id \<inter> {((p, w), (p', w')). worklist_inv (p, w, False)}) init_pw_spec"
  unfolding init_pw_spec_def worklist_inv_def pw_inv_def worklist_inv_frontier_def
  by (auto simp: pw_le_iff refine_pw_simps)

lemma worklist_algo_ref[refine]:
  "worklist_algo \<le> \<Down> Id pw_algo"
  unfolding worklist_algo_def pw_algo_def
    using [[goals_limit=20]]
    apply refine_rcg
   unfolding pw_inv_def worklist_inv_def worklist_inv_frontier_def pw_inv_frontier_def
      by auto (* slow *)

theorem worklist_algo_correct:
  "worklist_algo \<le> SPEC (\<lambda> brk. brk \<longleftrightarrow> F_reachable)"
proof -
  note worklist_algo_ref
  also note pw_algo_correct
  finally show ?thesis .
qed

end -- \<open>Search Space'\<close>


context Search_Space''_Defs
begin

  definition "worklist_inv_frontier' passed wait =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<and> \<not> empty a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set_mset wait. a' \<preceq> b'))"

  definition "start_subsumed' passed wait = (\<exists> a \<in> passed \<union> set_mset wait. a\<^sub>0 \<preceq> a)"

  definition "worklist_inv' \<equiv> \<lambda> (passed, wait, brk).
    worklist_inv (passed, wait, brk) \<and> (\<forall> a \<in> passed. \<not> empty a) \<and> (\<forall> a \<in> set_mset wait. \<not> empty a)
      "

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

end -- \<open>Search Space' Defs\<close>

context Search_Space''_start
begin

  lemma worklist_algo_list_inv_ref[refine]:
    fixes x x'
    assumes
      "\<not> F a\<^sub>0" "\<not> F a\<^sub>0"
      "(x, x') \<in> {
        ((passed,wait,brk), (passed',wait',brk')). passed = passed' \<and> wait = wait' \<and> brk = brk' \<and>
        (\<forall> a \<in> passed. \<not> empty a) \<and> (\<forall> a \<in> set_mset wait. \<not> empty a)}"
      "worklist_inv x'"
    shows "worklist_inv' x"
    using assms
    unfolding worklist_inv'_def worklist_inv_def
    by auto

  lemma [refine]:
    "take_from_mset wait \<le>
    \<Down> {((x, wait), (y, wait')). x = y \<and> wait = wait' \<and> \<not> empty x \<and>
        (\<forall> a \<in> set_mset wait. \<not> empty a)} (take_from_mset wait')"
    if "wait = wait'" "\<forall> a \<in> set_mset wait. \<not> empty a" "wait \<noteq> {#}"
    using that
    by (auto 4 5 simp: pw_le_iff refine_pw_simps dest: in_diffD dest!: take_from_mset_correct)

  lemma [refine]:
    "add_succ_spec' wait x \<le>
    \<Down> ({(wait, wait'). wait = wait' \<and>
        (\<forall> a \<in> set_mset wait. \<not> empty a)} \<times>\<^sub>r bool_rel) (add_succ_spec wait' x')"
    if "wait = wait'" "x = x'" "\<forall> a \<in> set_mset wait. \<not> empty a"
    using that
    unfolding add_succ_spec'_def add_succ_spec_def
    by (auto simp: pw_le_iff refine_pw_simps)

 lemma worklist_algo'_ref[refine]: "worklist_algo' \<le> \<Down>Id worklist_algo"
    using [[goals_limit=15]]
    unfolding worklist_algo'_def worklist_algo_def
    apply (refine_rcg)
                   prefer 4
                   apply assumption
                  apply refine_dref_type
    by (auto simp: empty_subsumes')

end -- \<open>Search Space' Start\<close>


context Search_Space''_Defs
begin

  definition worklist_algo'' where
    "worklist_algo'' \<equiv>
      if empty a\<^sub>0 then RETURN False else worklist_algo'
    "

end -- \<open>Search Space' Defs\<close>


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