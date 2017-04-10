theory Unified_PW_Hashing
  imports Worklist_Subsumption_PW_Multiset DRAT_Misc
begin

subsection \<open>Towards an Implementation\<close>
locale Worklist1_Defs = Search_Space_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"
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

end -- \<open>Worklist1 Defs\<close>

locale Worklist1 = Worklist1_Defs + Search_Space +
  assumes succs_correct: "reachable a \<Longrightarrow> set (succs a) = Collect (E a)"
begin

lemma add_pw_unified_spec_ref:
  "add_pw_unified_spec passed wait a \<le> add_pw_spec passed wait a"
  if "reachable a" "a \<in> passed"
  using succs_correct[OF that(1)] that(2)
  unfolding add_pw_unified_spec_def add_pw_spec_def
  apply simp
  apply safe
                      apply (auto simp: empty_subsumes)
  using mset_subset_eqD apply force
    using mset_subset_eqD apply force
  subgoal premises prems
    using prems (1,6,7,11)
    by (subst (asm) filter_False; fastforce intro: trans)
      (* s/h *)
proof -
  fix aa :: "'a set" and aaa :: "'a multiset" and b :: bool and x :: 'a
  assume a1: "\<forall>x\<in>aa. \<exists>xa\<in>passed. x \<preceq> xa"
  assume a2: "x \<in> aa"
  assume a3: "aa \<subseteq> passed \<union> {x. E a x \<and> (\<forall>xa\<in>passed. \<not> x \<preceq> xa)}"
  obtain aab :: "'a \<Rightarrow> 'a" where
    "\<forall>a. a \<notin> aa \<or> aab a \<in> passed \<and> a \<preceq> aab a"
    using a1 by moura
  then show "x \<in> passed"
    using a3 a2 by blast
qed
  (* by (smt UnE mem_Collect_eq subsetCE) *)


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

end -- \<open>Worklist 1\<close>

locale Worklist2_Defs = Worklist1_Defs + Search_Space''_Defs
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
        if F a\<^sub>0 then RETURN True
        else do {
          (passed, wait) \<leftarrow> RETURN ({a\<^sub>0}, {#a\<^sub>0#});
          (passed, wait, brk) \<leftarrow> WHILEIT pw_inv (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> {#})
            (\<lambda> (passed, wait, brk). do
              {
                (a, wait) \<leftarrow> take_from_mset wait;
                ASSERT (reachable a);
                add_pw' passed wait a
              }
            )
            (passed, wait, False);
            RETURN brk
        }
      }
    "

end -- \<open>Worklist 2 Defs\<close>

locale Worklist2 = Worklist2_Defs + Worklist1 + Search_Space''_pre + Search_Space
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
  (* "add_pw' passed wait a \<le> \<Down> (Id \<inter> {((p, w, _), _). p \<noteq> {} \<and> set_mset w \<subseteq> p}) (add_pw_spec passed' wait' a')" *)
  "add_pw' passed wait a \<le> \<Down> ({((p, w, b), (p', w', b')). p \<noteq> {} \<and> p = p' \<union> set_mset w \<and> w = w' \<and> b = b'}) (add_pw_spec passed' wait' a')"
  if "passed \<noteq> {}" "set_mset wait \<subseteq> passed" "reachable a" "a \<in> passed"
     and [simp]: "passed = passed'" "wait = wait'" "a = a'"
  by (rule add_pw'_ref1[OF that, THEN refine_weaken]; auto)

lemma
  "(({a\<^sub>0}, {#a\<^sub>0#}, False), {}, {#a\<^sub>0#}, False) \<in> {((p, w, b), (p', w', b')). p = p' \<union> set_mset w' \<and> w = w' \<and> b = b'}"
  by auto

lemma [refine]:
  "RETURN ({a\<^sub>0}, {#a\<^sub>0#}) \<le> \<Down> (Id \<inter> {((p, w), (p', w')). p \<noteq> {} \<and> set_mset w \<subseteq> p}) init_pw_spec"
  unfolding init_pw_spec_def by (auto simp: pw_le_iff refine_pw_simps)

lemma [refine]:
  "take_from_mset wait \<le> \<Down> {((x, wait), (y, wait')). x = y \<and> wait = wait' \<and> set_mset wait \<subseteq> passed \<and> x \<in> passed} (take_from_mset wait')"
  if "wait = wait'" "set_mset wait \<subseteq> passed" "wait \<noteq> {#}"
  using that
  by (auto 4 5 simp: pw_le_iff refine_pw_simps dest: in_diffD dest!: take_from_mset_correct)

lemma pw_algo_unified_ref:
  "pw_algo_unified \<le> \<Down> Id pw_algo"
  unfolding pw_algo_unified_def pw_algo_def
  by refine_rcg (auto simp: init_pw_spec_def)

end -- \<open>Worklist 2\<close>

end -- \<open>End of Theory\<close>