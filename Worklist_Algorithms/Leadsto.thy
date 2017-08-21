theory Leadsto
  imports Liveness_Subsumption Unified_PW "../library/CTL"
begin

locale Leadsto_Search_Space =
  A: Search_Space'_finite E a\<^sub>0 _ "op \<preceq>" empty
  for E a\<^sub>0 Q_any empty V_any and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
  +
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes P_mono: "a \<preceq> a' \<Longrightarrow> P a \<Longrightarrow> P a'"
  assumes Q_mono: "a \<preceq> a' \<Longrightarrow> Q a \<Longrightarrow> Q a'"
  (*
  B: Search_Space_Nodes B a\<^sub>0 _ "op \<preceq>" V_any empty
  for A B a\<^sub>0 P Q_any empty V_any and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
  *)
begin

term A.pw_algo

term FOREACHc

interpretation A': Search_Space'_finite E a\<^sub>0 "\<lambda> _. False" "op \<preceq>" empty
  apply standard
          apply (rule A.refl A.trans A.mono A.empty_subsumes A.empty_mono A.empty_E; assumption)+
    apply assumption
   apply blast
  apply (rule A.finite_reachable)
  done

interpretation B:
  Search_Space_Nodes_finite_strict
  "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>0 "\<lambda> _. False" "op \<preceq>" "\<lambda> x. A.reachable x \<and> \<not> empty x"
  "\<lambda> _. False"
  apply standard
         apply (rule A.refl A.trans; assumption)+
  subgoal for a b a'
    by safe (drule A.mono; auto intro: Q_mono dest: A.mono A.empty_mono)
  by (auto intro: A.trans A.mono A.empty_subsumes A.empty_E A.finite_reachable dest: A.empty_mono)

context
  fixes a\<^sub>1 :: 'a
begin

interpretation B':
  Search_Space_Nodes_finite_strict
  "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>1 "\<lambda> _. False" "op \<preceq>" "\<lambda> x. A.reachable x \<and> \<not> empty x"
  "\<lambda> _. False"
  ..

definition has_cycle where
  "has_cycle = B'.dfs"

end (* Second start state *)

definition leadsto :: "bool nres" where
  "leadsto = do {
    (r, passed) \<leftarrow> A'.pw_algo;
    let P = {x. x \<in> passed \<and> P x \<and> Q x};
    (r, _) \<leftarrow>
              FOREACH\<^sub>C P (\<lambda>(b,_). \<not>b) (\<lambda>v' (_,P). has_cycle v' P) (False,{});
    RETURN r
  }"

thm A'.pw_algo_correct

definition
  "reaches_cycle a =
    (\<exists> b. (\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y)\<^sup>*\<^sup>* a b \<and> (\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y)\<^sup>+\<^sup>+ b b)"

definition leadsto_spec where
  "leadsto_spec =
    SPEC (\<lambda> r.
      r \<longleftrightarrow>
      (\<exists> a. A.reachable a \<and> P a \<and> Q a \<and> reaches_cycle a)
    )"

lemma
  "leadsto \<le> leadsto_spec"
proof -
  define inv where
    "inv \<equiv> \<lambda> passed it (r, passed').
       (r \<longrightarrow> (\<exists> a. A.reachable a \<and> \<not> empty a \<and> P a \<and> Q a \<and> reaches_cycle a))
     \<and> (\<not> r \<longrightarrow>
          (\<forall> a \<in> passed - it. \<not> reaches_cycle a)
         \<and> B.liveness_compatible passed'
         \<and> passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}
       )
    "

  have [simp, intro]:
    "\<not> A'.F_reachable"
    unfolding A'.F_reachable_def by simp

  have reaches_cycle_iff: "reaches_cycle a \<longleftrightarrow> (\<exists>x. B.G.G'.reaches a x \<and> B.G.G'.reaches1 x x)"
    if "A.reachable a" "\<not> empty a" for a
    unfolding reaches_cycle_def thm B.G.E'_def
    sorry

  have aux1:
    "(\<forall>a\<in>{x. A.reachable x \<and> P x \<and> Q x}. \<not> reaches_cycle a)"
    if
      "\<forall>a. A.reachable a \<and> \<not> empty a \<longrightarrow> (\<exists>x\<in>passed. a \<preceq> x)"
      "passed \<subseteq> {a. A.reachable a \<and> \<not> empty a}"
      "\<forall>x \<in> passed. P x \<and> Q x \<longrightarrow> \<not> reaches_cycle x"
    for passed
    sorry

  show ?thesis
    unfolding leadsto_def leadsto_spec_def
    apply (refine_rcg refine_vcg)
      subgoal for _ r passed
      thm FOREACHc_rule'
      apply (refine_vcg
            FOREACHc_rule'[where I = "inv {x \<in> passed. P x \<and> Q x}"]
            )

      (* Result of first reachability computation is finite *)
      subgoal
        by (auto intro: finite_subset[OF _ A.finite_reachable])

      (* Invariant holds initially *)
      subgoal
        unfolding inv_def B.liveness_compatible_def by auto

      (* Invariant is preserved *)
      subgoal for a\<^sub>1 it \<sigma> a passed'
        apply clarsimp
          subgoal premises prems
          proof -
            interpret B':
              Search_Space_Nodes_finite_strict
              "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>1 "\<lambda> _. False" "op \<preceq>" "\<lambda> x. A.reachable x \<and> \<not> empty x" "\<lambda> _. False"
              ..
            from \<open>inv _ _ _\<close> have
              "B'.liveness_compatible passed'" "passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}"
              unfolding inv_def by auto
            from B'.dfs_correct[OF _ _ this] \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>it \<subseteq> _\<close> have
              "B'.dfs passed' \<le> B'.dfs_spec"
              by auto
            then show ?thesis
              unfolding has_cycle_def
              apply (rule order.trans)
              unfolding B'.dfs_spec_def
              apply clarsimp
              subgoal for r passed'
                apply (cases r)
                 apply simp
                subgoal
                  unfolding inv_def
                  using \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>it \<subseteq> _\<close>
                  apply simp
                    apply (inst_existentials a\<^sub>1)
                  by (auto 4 3 simp: reaches_cycle_iff)
                  subgoal
                    using \<open>inv _ _ _\<close> \<open>passed \<subseteq> _\<close> reaches_cycle_iff unfolding inv_def by blast
                  done
                done
            qed
            done

          (* I \<and> \<not> b \<longrightarrow> post *)
          subgoal for \<sigma> a b
            unfolding inv_def by (auto dest: aux1)

          (* I \<and> b \<longrightarrow> post *)
          subgoal for it \<sigma> a b
            unfolding inv_def by auto
          done
        done
    qed

end (* Leadsto Search Space *)

end (* Theory *)