theory Unified_PW_Hashing
  imports
    Unified_PW
    Refine_Imperative_HOL.IICF_List_Mset
    Worklist_Algorithms_Misc
    "../library/Tracing"
begin

subsection \<open>Towards an Implementation of the Unified Passed-Wait List\<close>

context Worklist1_Defs
begin

definition "add_pw_unified_spec passed wait a \<equiv> SPEC (\<lambda>(passed',wait',brk).
  if \<exists> x \<in> set (succs a). F x then brk
  else passed' \<subseteq> passed \<union> {x \<in> set (succs a). \<not> (\<exists> y \<in> passed. x \<preceq> y)}
      \<and> passed \<subseteq> passed'
      \<and> wait \<subseteq># wait'
      \<and> wait' \<subseteq># wait + mset ([x \<leftarrow> succs a. \<not> (\<exists> y \<in> passed. x \<preceq> y)])
      \<and> (\<forall> x \<in> set (succs a). \<exists> y \<in> passed'. x \<preceq> y)
      \<and> (\<forall> x \<in> set (succs a). \<not> (\<exists> y \<in> passed. x \<preceq> y) \<longrightarrow> (\<exists> y \<in># wait'. x \<preceq> y))
      \<and> \<not> brk)
"

definition "add_pw passed wait a \<equiv>
    nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
      (\<lambda>a (passed, wait, brk). RETURN (
        if F a then
          (passed, wait, True)
        else if \<exists> x \<in> passed. a \<preceq> x then
          (passed, wait, False)
        else (insert a passed, add_mset a wait, False)
      ))
      (passed, wait, False)
"

end \<comment> \<open>Worklist1 Defs\<close>

context Worklist1
begin

lemma add_pw_unified_spec_ref:
  "add_pw_unified_spec passed wait a \<le> add_pw_spec passed wait a"
  if "reachable a" "a \<in> passed"
  using succs_correct[OF that(1)] that(2)
  unfolding add_pw_unified_spec_def add_pw_spec_def
  apply simp
  apply safe
                      apply (all \<open>auto simp: empty_subsumes; fail | succeed\<close>)
  using mset_subset_eqD apply force
    using mset_subset_eqD apply force
  subgoal premises prems
    using prems
    by (auto 4 5 simp: filter_mset_eq_empty_iff intro: trans elim!: subset_mset.ord_le_eq_trans)
      (* s/h *)
  by (clarsimp, smt UnE mem_Collect_eq subsetCE)

lemma add_pw_ref:
  "add_pw passed wait a \<le> \<Down> Id (add_pw_unified_spec passed wait a)"
  unfolding add_pw_def add_pw_unified_spec_def
  apply (refine_vcg
      nfoldli_rule[where I =
        "\<lambda> l1 l2 (passed', wait', brk).
        if brk then \<exists> a' \<in> set (succs a). F a'
        else passed' \<subseteq> passed \<union> {x \<in> set l1. \<not> (\<exists> y \<in> passed. x \<preceq> y)}
           \<and> passed  \<subseteq> passed'
           \<and> wait \<subseteq># wait'
           \<and> wait' \<subseteq># wait + mset [x \<leftarrow> l1. \<not> (\<exists> y \<in> passed. x \<preceq> y)]
           \<and> (\<forall> x \<in> set l1. \<exists> y \<in> passed'. x \<preceq> y)
           \<and> (\<forall> x \<in> set l1. \<not> (\<exists> y \<in> passed. x \<preceq> y) \<longrightarrow> (\<exists> y \<in># wait'. x \<preceq> y))
           \<and> set l1 \<inter> Collect F = {}
      "
        ])
     apply (auto; fail)
    apply (clarsimp split: if_split_asm)
     apply safe[]
           apply (auto simp add: subset_mset.le_iff_add; fail)+
  subgoal premises prems
    using prems(4,9,11,12,14) by (blast intro: trans)
  by (auto simp: subset_mset.le_iff_add)

end \<comment> \<open>Worklist 1\<close>

context Worklist2_Defs
begin

definition "add_pw' passed wait a \<equiv>
    nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
      (\<lambda>a (passed, wait, brk). RETURN (
        if F a then
          (passed, wait, True)
        else if empty a then
          (passed, wait, False)
        else if \<exists> x \<in> passed. a \<unlhd> x then
          (passed, wait, False)
        else (insert a passed, add_mset a wait, False)
      ))
      (passed, wait, False)
"

definition pw_algo_unified where
    "pw_algo_unified = do
      {
        if F a\<^sub>0 then RETURN (True, {})
        else if empty a\<^sub>0 then RETURN (False, {})
        else do {
          (passed, wait) \<leftarrow> RETURN ({a\<^sub>0}, {#a\<^sub>0#});
          (passed, wait, brk) \<leftarrow> WHILEIT pw_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_mset wait;
                ASSERT (reachable a);
                if empty a then RETURN (passed, wait, brk) else add_pw' passed wait a
              }
            )
            (passed, wait, False);
            RETURN (brk, passed)
        }
      }
    "

end \<comment> \<open>Worklist 2 Defs\<close>

context Worklist2
begin

lemma empty_subsumes'2:
  "empty x \<or> x \<unlhd> y \<longleftrightarrow> x \<preceq> y"
  using empty_subsumes' empty_subsumes by auto

lemma bex_or:
  "P \<or> (\<exists> x \<in> S. Q x) \<longleftrightarrow> (\<exists> x \<in> S. P \<or> Q x)" if "S \<noteq> {}"
  using that by auto

lemma add_pw'_ref':
  "add_pw' passed wait a \<le> \<Down> (Id \<inter> {((p, w, _), _). p \<noteq> {} \<and> set_mset w \<subseteq> p}) (add_pw passed wait a)"
  if "passed \<noteq> {}" "set_mset wait \<subseteq> passed"
  unfolding add_pw'_def add_pw_def
  apply (rule nfoldli_refine)
     apply refine_dref_type
  using that apply (auto; fail)+
  apply refine_rcg
  apply rule
  unfolding z3_rule(44)
   apply (subst bex_or)
  by (auto simp add: empty_subsumes'2)

(* XXX Why is transitivity reasoning broken here? *)
lemma add_pw'_ref1[refine]:
  "add_pw' passed wait a \<le> \<Down> (Id \<inter> {((p, w, _), _). p \<noteq> {} \<and> set_mset w \<subseteq> p}) (add_pw_spec passed' wait' a')"
  if "passed \<noteq> {}" "set_mset wait \<subseteq> passed" "reachable a" "a \<in> passed"
     and [simp]: "passed = passed'" "wait = wait'" "a = a'"
proof -
  from add_pw_unified_spec_ref[OF that(3-4), of wait] add_pw_ref[of passed wait a] have
    "add_pw passed wait a \<le> \<Down> Id (add_pw_spec passed wait a)"
    by simp
  moreover note add_pw'_ref'[OF that(1,2), of a]
  ultimately show ?thesis
    by (auto simp add: pw_le_iff refine_pw_simps)
qed

lemma refine_weaken:
  "p \<le> \<Down> R p'" if "p \<le> \<Down> S p'" "S \<subseteq> R"
  using that
  by (auto simp: pw_le_iff refine_pw_simps; blast)

lemma add_pw'_ref:
  "add_pw' passed wait a \<le>
    \<Down> ({((p, w, b), (p', w', b')). p \<noteq> {} \<and> p = p' \<union> set_mset w \<and> w = w' \<and> b = b'})
      (add_pw_spec passed' wait' a')"
  if "passed \<noteq> {}" "set_mset wait \<subseteq> passed" "reachable a" "a \<in> passed"
     and [simp]: "passed = passed'" "wait = wait'" "a = a'"
  by (rule add_pw'_ref1[OF that, THEN refine_weaken]; auto)

lemma
  "(({a\<^sub>0}, {#a\<^sub>0#}, False), {}, {#a\<^sub>0#}, False)
  \<in> {((p, w, b), (p', w', b')). p = p' \<union> set_mset w' \<and> w = w' \<and> b = b'}"
  by auto

lemma [refine]:
  "RETURN ({a\<^sub>0}, {#a\<^sub>0#}) \<le> \<Down> (Id \<inter> {((p, w), (p', w')). p \<noteq> {} \<and> set_mset w \<subseteq> p}) init_pw_spec"
  if "\<not> empty a\<^sub>0"
  using that unfolding init_pw_spec_def by (auto simp: pw_le_iff refine_pw_simps)

lemma [refine]:
  "take_from_mset wait \<le>
    \<Down> {((x, wait), (y, wait')). x = y \<and> wait = wait' \<and> set_mset wait \<subseteq> passed \<and> x \<in> passed}
      (take_from_mset wait')"
  if "wait = wait'" "set_mset wait \<subseteq> passed" "wait \<noteq> {#}"
  using that
  by (auto 4 5 simp: pw_le_iff refine_pw_simps dest: in_diffD dest!: take_from_mset_correct)

lemma pw_algo_unified_ref:
  "pw_algo_unified \<le> \<Down> Id pw_algo"
  unfolding pw_algo_unified_def pw_algo_def
  by refine_rcg (auto simp: init_pw_spec_def)

end \<comment> \<open>Worklist 2\<close>

subsubsection \<open>Utilities\<close>

definition take_from_list where
  "take_from_list s = ASSERT (s \<noteq> []) \<then> SPEC (\<lambda> (x, s'). s = x # s')"

lemma take_from_list_correct:
  assumes "s \<noteq> []"
  shows "take_from_list s \<le> SPEC (\<lambda> (x, s'). s = x # s')"
using assms unfolding take_from_list_def by simp

lemmas [refine_vcg] = take_from_list_correct[THEN order.trans]

context Worklist_Map_Defs
begin

definition
  "map_set_rel =
    {(m, s).
      \<Union>(ran m) = s \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> x. key v = k)) \<and>
      finite (dom m) \<and> (\<forall> k S. m k = Some S \<longrightarrow> finite S)
    }"

definition
  "add_pw'_map passed wait a \<equiv>
   nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
    (\<lambda>a (passed, wait, _).
      do {
      RETURN (
        if F a then (passed, wait, True) else
        let k = key a; passed' = (case passed k of Some passed' \<Rightarrow> passed' | None \<Rightarrow> {})
        in
          if empty a then
            (passed, wait, False)
          else if \<exists> x \<in> passed'. a \<unlhd> x then
            (passed, wait, False)
          else
            (passed(k \<mapsto> (insert a passed')), a # wait, False)
        )
      }
    )
    (passed,wait,False)"

definition
  "pw_map_inv \<equiv> \<lambda> (passed, wait, brk).
    \<exists> passed' wait'.
      (passed, passed') \<in> map_set_rel \<and> (wait, wait') \<in> list_mset_rel \<and>
      pw_inv (passed', wait', brk)
  "

definition pw_algo_map where
  "pw_algo_map = do
    {
      if F a\<^sub>0 then RETURN (True, Map.empty)
      else if empty a\<^sub>0 then RETURN (False, Map.empty)
      else do {
        (passed, wait) \<leftarrow> RETURN ([key a\<^sub>0 \<mapsto> {a\<^sub>0}], [a\<^sub>0]);
        (passed, wait, brk) \<leftarrow> WHILEIT pw_map_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
          (\<lambda> (passed, wait, brk). do
            {
              (a, wait) \<leftarrow> take_from_list wait;
              ASSERT (reachable a);
              if empty a then RETURN (passed, wait, brk) else add_pw'_map passed wait a
            }
          )
          (passed, wait, False);
          RETURN (brk, passed)
      }
    }
  "

end \<comment> \<open>Worklist Map Defs\<close>

lemma ran_upd_cases:
  "(x \<in> ran m) \<or> (x = y)" if "x \<in> ran (m(a \<mapsto> y))"
  using that unfolding ran_def by (auto split: if_split_asm)

lemma ran_upd_cases2:
  "(\<exists> k. m k = Some x \<and> k \<noteq> a) \<or> (x = y)" if "x \<in> ran (m(a \<mapsto> y))"
  using that unfolding ran_def by (auto split: if_split_asm)

context Worklist_Map
begin

lemma add_pw'_map_ref[refine]:
  "add_pw'_map passed wait a \<le> \<Down> (map_set_rel \<times>\<^sub>r list_mset_rel \<times>\<^sub>r bool_rel) (add_pw' passed' wait' a')"
  if "(passed, passed') \<in> map_set_rel" "(wait, wait') \<in> list_mset_rel" "(a, a') \<in> Id"
  using that
  unfolding add_pw'_map_def add_pw'_def
  apply refine_rcg
     apply refine_dref_type
     apply (auto; fail)
    apply (auto; fail)
   apply (auto; fail)
  subgoal premises assms for a a' _ _ passed' _ wait' f' passed _ wait f
  proof -
    from assms have [simp]: "a' = a" "f = f'" by simp+
    from assms have rel_passed: "(passed, passed') \<in> map_set_rel" by simp
    then have union: "passed' = \<Union>(ran passed)"
      unfolding map_set_rel_def by auto
    from assms have rel_wait: "(wait, wait') \<in> list_mset_rel" by simp
    from rel_passed have keys[simp]: "key v = k" if "passed k = Some xs" "v \<in> xs" for k xs v
      using that unfolding map_set_rel_def by auto
    define k where "k \<equiv> key a"
    define xs where "xs \<equiv> case passed k of None \<Rightarrow> {} | Some p \<Rightarrow> p"
    have xs_ran: "x \<in> \<Union>(ran passed)" if "x \<in> xs" for x
      using that unfolding xs_def ran_def by (auto split: option.split_asm)
    have *:
      "(\<exists>x \<in> xs. a \<unlhd> x) \<longleftrightarrow> (\<exists>x\<in>passed'. a' \<unlhd> x)"
    proof (simp, safe, goal_cases)
      case (1 x)
      with rel_passed show ?case
        unfolding xs_def union by (auto intro: ranI split: option.split_asm)
    next
      case (2 x)
      with rel_passed show ?case unfolding xs_def union ran_def k_def map_set_rel_def
        using empty_subsumes'2 by force
    qed
    have "(passed(k \<mapsto> insert a xs), insert a' passed') \<in> map_set_rel"
      using \<open>(passed, passed') \<in> map_set_rel\<close>
      unfolding map_set_rel_def
      apply safe
      subgoal
        unfolding union by (auto dest!: ran_upd_cases xs_ran)
      subgoal
        unfolding ran_def by auto
      subgoal for a''
        unfolding union ran_def
        apply clarsimp
        subgoal for k'
          unfolding xs_def by (cases "k' = k") auto
        done
      by (clarsimp split: if_split_asm, safe,
          auto intro!: keys simp: xs_def k_def split: option.split_asm if_split_asm)
    with rel_wait rel_passed show ?thesis
      unfolding *[symmetric]
      unfolding xs_def k_def Let_def
      unfolding list_mset_rel_def br_def
      by auto
  qed
done

lemma init_map_ref[refine]:
  "(([key a\<^sub>0 \<mapsto> {a\<^sub>0}], [a\<^sub>0]), {a\<^sub>0}, {#a\<^sub>0#}) \<in> map_set_rel \<times>\<^sub>r list_mset_rel"
  unfolding map_set_rel_def list_mset_rel_def br_def by auto

lemma take_from_list_ref[refine]:
  "take_from_list xs \<le> \<Down> (Id \<times>\<^sub>r list_mset_rel) (take_from_mset ms)" if "(xs, ms) \<in> list_mset_rel"
  using that unfolding take_from_list_def take_from_mset_def list_mset_rel_def br_def
  by (clarsimp simp: pw_le_iff refine_pw_simps)

lemma pw_algo_map_ref:
  "pw_algo_map \<le> \<Down> (Id \<times>\<^sub>r map_set_rel) pw_algo_unified"
  unfolding pw_algo_map_def pw_algo_unified_def
  apply refine_rcg
  unfolding pw_map_inv_def list_mset_rel_def br_def map_set_rel_def by auto


end \<comment> \<open>Worklist Map\<close>

context Worklist_Map2_Defs
begin

definition
  "add_pw'_map2 passed wait a \<equiv>
   nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
    (\<lambda>a (passed, wait, _).
      do {
      RETURN (
        if empty a then
            (passed, wait, False)
        else if F' a then (passed, wait, True)
        else
          let k = key a; passed' = (case passed k of Some passed' \<Rightarrow> passed' | None \<Rightarrow> {})
          in
            if \<exists> x \<in> passed'. a \<unlhd> x then
              (passed, wait, False)
            else
              (passed(k \<mapsto> (insert a passed')), a # wait, False)
        )
      }
    )
    (passed,wait,False)"

definition pw_algo_map2 where
  "pw_algo_map2 = do
    {
      if F a\<^sub>0 then RETURN (True, Map.empty)
      else if empty a\<^sub>0 then RETURN (False, Map.empty)
      else do {
        (passed, wait) \<leftarrow> RETURN ([key a\<^sub>0 \<mapsto> {a\<^sub>0}], [a\<^sub>0]);
        (passed, wait, brk) \<leftarrow> WHILEIT pw_map_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
          (\<lambda> (passed, wait, brk). do
            {
              (a, wait) \<leftarrow> take_from_list wait;
              ASSERT (reachable a);
              if empty a
              then RETURN (passed, wait, brk)
              else do {
                TRACE (ExploredState); add_pw'_map2 passed wait a
              }
            }
          )
          (passed, wait, False);
          RETURN (brk, passed)
      }
    }
  "

end \<comment> \<open>Worklist Map 2 Defs\<close>

context Worklist_Map2
begin

lemma add_pw'_map2_ref[refine]:
  "add_pw'_map2 passed wait a \<le> \<Down> Id (add_pw'_map passed' wait' a')"
  if "(passed, passed') \<in> Id" "(wait, wait') \<in> Id" "(a, a') \<in> Id"
  using that
  unfolding add_pw'_map2_def add_pw'_map_def
  apply refine_rcg
     apply refine_dref_type
  by (auto simp: F_split)

lemma pw_algo_map2_ref[refine]:
  "pw_algo_map2 \<le> \<Down> Id pw_algo_map"
  unfolding pw_algo_map2_def pw_algo_map_def TRACE_bind
  apply refine_rcg
           apply refine_dref_type
  by auto

end \<comment> \<open>Worklist Map 2\<close>

lemma (in Worklist_Map2_finite) pw_algo_map2_correct:
  "pw_algo_map2 \<le> SPEC (\<lambda> (brk, passed).
    (brk \<longleftrightarrow> F_reachable) \<and>
    (\<not> brk \<longrightarrow>
      (\<exists> p.
        (passed, p) \<in> map_set_rel \<and> (\<forall>a. reachable a \<and> \<not> empty a \<longrightarrow> (\<exists>b\<in>p. a \<preceq> b))
        \<and> p \<subseteq> {a. reachable a \<and> \<not> empty a})
    )
   )"
proof -
  note pw_algo_map2_ref
  also note pw_algo_map_ref
  also note pw_algo_unified_ref
  also note pw_algo_correct
  finally show ?thesis
    unfolding conc_fun_def Image_def by (fastforce intro: order.trans) (* Slow *)
qed

end \<comment> \<open>End of Theory\<close>
