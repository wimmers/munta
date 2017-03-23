(* Authors: Lammich, Wimmer *)
theory Worklist_Subsumption1
  imports Worklist_Subsumption_Multiset
begin

subsection \<open>From Multisets to Lists\<close>

subsubsection \<open>Utilities\<close>

definition take_from_list where
  "take_from_list s = ASSERT (s \<noteq> []) \<then> SPEC (\<lambda> (x, s'). s = x # s')"

lemma take_from_list_correct:
  assumes "s \<noteq> []"
  shows "take_from_list s \<le> SPEC (\<lambda> (x, s'). s = x # s')"
using assms unfolding take_from_list_def by simp

lemmas [refine_vcg] = take_from_list_correct[THEN order.trans]


context Search_Space_Defs
begin

  definition "worklist_inv_frontier_list passed wait =
    (\<forall> a \<in> passed. \<forall> a'. E a a' \<longrightarrow> (\<exists> b' \<in> passed \<union> set wait. a' \<preceq> b'))"

  definition "start_subsumed_list passed wait = (\<exists> a \<in> passed \<union> set wait. a\<^sub>0 \<preceq> a)"

  definition "worklist_inv_list \<equiv> \<lambda> (passed, wait, brk).
    passed \<subseteq> Collect reachable \<and>
    (brk \<longrightarrow> (\<exists> f. reachable f \<and> F f)) \<and>
    (\<not> brk \<longrightarrow>
      worklist_inv_frontier_list passed wait
    \<and> (\<forall> a \<in> passed \<union> set wait. \<not> F a)
    \<and> start_subsumed_list passed wait
    \<and> set wait \<subseteq> Collect reachable)
    "

  definition "add_succ_spec_list wait a \<equiv> SPEC (\<lambda>(wait',brk).
    if \<exists>a'. E a a' \<and> F a' then
      brk
    else
      \<not>brk \<and> set wait' \<subseteq> set wait \<union> {a' . E a a'} \<and>
      (\<forall> s \<in> set wait \<union> {a' . E a a'}. \<exists> s' \<in> set wait'. s \<preceq> s')
  )"

  definition worklist_algo_list where
    "worklist_algo_list = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = [a\<^sub>0];
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv_list (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_list wait;
                ASSERT (reachable a);
                if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ_spec_list wait a;
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

end -- \<open>Search Space Defs\<close>

context Search_Space
begin

  lemma worklist_algo_list_inv_ref:
    fixes x x'
    assumes
      "\<not> F a\<^sub>0" "\<not> F a\<^sub>0"
      "(x, x') \<in> {((passed,wait,brk), (passed',wait',brk')). passed = passed' \<and> mset wait = wait' \<and> brk = brk' }"
      "worklist_inv x'"
    shows "worklist_inv_list x"
    using assms
    unfolding worklist_inv_def worklist_inv_list_def
    unfolding worklist_inv_frontier_def worklist_inv_frontier_list_def
    unfolding start_subsumed_def start_subsumed_list_def
    by auto

  lemma take_from_list_take_from_mset_ref[refine]:
    "take_from_list xs \<le> \<Down> {((x, xs),(y, m)). x = y \<and> mset xs = m} (take_from_mset m)"
    if "mset xs = m"
    using that unfolding take_from_list_def take_from_mset_def
    by (clarsimp simp: pw_le_iff refine_pw_simps)

  lemma add_succ_spec_list_add_succ_spec_ref[refine]:
    "add_succ_spec_list xs b \<le> \<Down> {((xs, b), (m, b')). mset xs = m \<and> b = b'} (add_succ_spec m b')"
    if "mset xs = m" "b = b'"
    using that unfolding add_succ_spec_list_def add_succ_spec_def
    by (clarsimp simp: pw_le_iff refine_pw_simps)

  lemma worklist_algo_list_ref[refine]: "worklist_algo_list \<le> \<Down>Id worklist_algo"
    unfolding worklist_algo_list_def worklist_algo_def
    apply (refine_rcg)
               apply blast
              prefer 2
              apply (rule worklist_algo_list_inv_ref; assumption)
    by auto

end -- \<open>Search Space\<close>

subsection \<open>Towards an Implementation\<close>
locale Worklist1_Defs = Search_Space_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"

locale Worklist1 = Worklist1_Defs + Search_Space +
  assumes succs_correct: "reachable a \<Longrightarrow> set (succs a) = Collect (E a)"
begin

  definition
    "add_succ1 wait a \<equiv>
     nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
      (\<lambda>a (wait,brk).
        if F a then RETURN (wait,True) else RETURN (
          if \<exists> x \<in> set wait. a \<preceq> x \<and> \<not> x \<preceq> a
          then [x \<leftarrow> wait. \<not> x \<preceq> a]
          else a # [x \<leftarrow> wait. \<not> x \<preceq> a],False)
      )
      (wait,False)"

  definition
    "filter_insert_wait wait a \<equiv>
     if \<exists> x \<in> set wait. a \<preceq> x \<and> \<not> x \<preceq> a then [x \<leftarrow> wait. \<not> x \<preceq> a] else a # [x \<leftarrow> wait. \<not> x \<preceq> a]"

  lemma filter_insert_wait_alt_def:
    "filter_insert_wait wait a = (
     let
       (f, xs) =
         fold (\<lambda> x (f, xs). if x \<preceq> a then (f, xs) else (f \<or> a \<preceq> x, x # xs)) wait (False, [])
     in
      if f then rev xs else a # rev xs)
    "
  proof -
    have
      "fold (\<lambda> x (f, xs). if x \<preceq> a then (f, xs) else (f \<or> a \<preceq> x, x # xs)) wait (f, xs)
     = (f \<or> (\<exists> x \<in> set wait. a \<preceq> x \<and> \<not> x \<preceq> a), rev [x \<leftarrow> wait. \<not> x \<preceq> a] @ xs)" for f xs
      by (induction wait arbitrary: f xs; simp)
    then show ?thesis unfolding filter_insert_wait_def by simp
  qed

  lemma add_succ1_alt_def:
    "add_succ1 wait a \<equiv>
     nfoldli (succs a) (\<lambda>(_,brk). \<not>brk)
      (\<lambda>a (wait,brk).
        if F a then RETURN (wait, True) else RETURN (filter_insert_wait wait a, False)
      )
      (wait,False)"
    unfolding add_succ1_def filter_insert_wait_def by (intro HOL.eq_reflection HOL.refl)

  lemma add_succ1_ref[refine]:
    "add_succ1 wait a \<le> \<Down>(Id \<times>\<^sub>r bool_rel) (add_succ_spec_list wait' a')"
    if "(wait,wait')\<in>Id" "(a,a')\<in>b_rel Id reachable"
    using that
    apply simp
    unfolding add_succ_spec_list_def add_succ1_def
    apply (refine_vcg nfoldli_rule[where I =
      "\<lambda>l1 _ (wait',brk).
        if brk then \<exists>a'. E a a' \<and> F a'
        else set wait' \<subseteq> set wait \<union> set l1 \<and> set l1 \<inter> Collect F = {}
          \<and> (\<forall> x \<in> set wait \<union> set l1. \<exists> x' \<in> set wait'. x \<preceq> x')"]
      )
    apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    using succs_correct[of a]
      apply (clarsimp split: if_split_asm; auto 10 0 intro: trans simp: list_ex_iff; fail)
    apply (auto; fail)
    using succs_correct[of a] apply (auto; fail)
    done

  definition worklist_algo1 where
    "worklist_algo1 = do
      {
        if F a\<^sub>0 then RETURN True
        else do {
          let passed = {};
          let wait = [a\<^sub>0];
          (passed, wait, brk) \<leftarrow> WHILEIT worklist_inv_list (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_list wait;
                if (\<exists> a' \<in> passed. a \<preceq> a') then RETURN (passed, wait, brk) else
                do
                  {
                    (wait,brk) \<leftarrow> add_succ1 wait a;
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

  lemma worklist_algo1_list_ref[refine]: "worklist_algo1 \<le> \<Down>Id worklist_algo_list"
    unfolding worklist_algo1_def worklist_algo_list_def
    apply (refine_rcg)
    apply refine_dref_type
    unfolding worklist_inv_def
    apply auto
    done

  lemma worklist_algo1_ref[refine]: "worklist_algo1 \<le> \<Down>Id worklist_algo"
  proof -
    note worklist_algo1_list_ref
    also note worklist_algo_list_ref
    finally show ?thesis .
  qed

end -- \<open>Worklist1\<close>

end -- \<open>Theory\<close>
