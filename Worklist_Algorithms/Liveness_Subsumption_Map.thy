theory Liveness_Subsumption_Map
  imports Liveness_Subsumption
begin

locale Liveness_Search_Space_Key_Defs =
  Liveness_Search_Space_Defs E for E :: "'v \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes key :: "'v \<Rightarrow> 'k"
  fixes subsumes' :: "'v \<Rightarrow> 'v \<Rightarrow> bool" (infix "\<unlhd>" 50)
begin

definition "check_loop_list v ST = (\<exists> v' \<in> set ST. v' \<preceq> v)"

definition "insert_map_set v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in S(k \<mapsto> (insert v S'))
"

definition "push_map_list v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> []) in S(k \<mapsto> v # S')
"

definition "check_subsumption_map_set v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in (\<exists> x \<in> S'. v \<unlhd> x)
"

definition "check_subsumption_map_list v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> []) in (\<exists> x \<in> set S'. x \<unlhd> v)
"

definition "pop_map_list v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> tl S | None \<Rightarrow> []) in S(k \<mapsto> S')
"

definition dfs_map :: "('k \<rightharpoonup> 'v set) \<Rightarrow> (bool \<times> ('k \<rightharpoonup> 'v set)) nres" where
  "dfs_map P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      if check_subsumption_map_list v ST then RETURN (P, ST, True)
      else do {
        if check_subsumption_map_set v P then
          RETURN (P, ST, False)
        else do {
            let ST = push_map_list v ST;
            (P, ST, r) \<leftarrow>
              nfoldli (succs v) (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
            let ST = pop_map_list v ST;
            let P = insert_map_set v P;
            RETURN (P, ST, r)
          }
      }
    ) (P,(Map.empty::('k \<rightharpoonup> 'v list)),a\<^sub>0);
    RETURN (r, P)
  }"

end (* Search Space Nodes Empty Key Defs *)

locale Liveness_Search_Space_Key =
  Liveness_Search_Space + Liveness_Search_Space_Key_Defs +
  assumes subsumes_key[intro, simp]: "a \<unlhd> b \<Longrightarrow> key a = key b"
  assumes V_subsumes': "V a \<Longrightarrow> a \<preceq> b \<longleftrightarrow> a \<unlhd> b"
begin

(* XXX Duplication *)
definition
  "map_set_rel =
    {(m, s).
      \<Union>(ran m) = s \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> x. key v = k)) \<and>
      finite (dom m) \<and> (\<forall> k S. m k = Some S \<longrightarrow> finite S)
    }"

definition
  "irrefl_trans_on R S \<equiv> (\<forall> x \<in> S. \<not> R x x) \<and> (\<forall> x \<in> S. \<forall> y \<in> S. \<forall> z \<in> S. R x y \<and> R y z \<longrightarrow> R x z)"

definition
  "map_list_rel =
    {(m, xs). \<Union> (set ` ran m) = set xs \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> set x. key v = k))
          \<and> (\<exists> R. irrefl_trans_on R (set xs)
              \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> sorted_wrt R x) \<and> sorted_wrt R xs)
          \<and> distinct xs
    }"

definition "list_set_hd_rel x \<equiv> {(l, s). set l = s \<and> distinct l \<and> l \<noteq> [] \<and> hd l = x}"

lemma empty_map_list_rel:
  "(Map.empty, []) \<in> map_list_rel"
  unfolding map_list_rel_def irrefl_trans_on_def by auto

lemma rel_start[refine]:
  "((P, Map.empty, a\<^sub>0), P', [], a\<^sub>0) \<in> map_set_rel \<times>\<^sub>r map_list_rel \<times>\<^sub>r Id" if "(P, P') \<in> map_set_rel"
  using that unfolding map_set_rel_def by (auto intro: empty_map_list_rel)

lemma refine_True:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> (x1c, x1a) \<in> map_list_rel
  \<Longrightarrow> ((x1b, x1c, True), x1, x1a, True) \<in> map_set_rel \<times>\<^sub>r map_list_rel \<times>\<^sub>r Id"
  by simp

lemma check_subsumption_ref[refine]:
  "V x2a \<Longrightarrow> (x1b, x1) \<in> map_set_rel \<Longrightarrow> check_subsumption_map_set x2a x1b = (\<exists>x\<in>x1. x2a \<preceq> x)"
  unfolding map_set_rel_def list_set_rel_def check_subsumption_map_set_def
  unfolding ran_def by (auto split: option.splits simp: V_subsumes')

lemma check_subsumption'_ref[refine]:
  "set xs \<subseteq> {x. V x} \<Longrightarrow> (m, xs) \<in> map_list_rel
  \<Longrightarrow> check_subsumption_map_list x m = check_loop x xs"
  unfolding map_list_rel_def list_set_rel_def check_subsumption_map_list_def check_loop_def
  unfolding ran_def apply (auto split: option.splits)
  subgoal for R x' xs'
    by (drule sym, drule sym, subst (asm) V_subsumes'[symmetric], auto)
  by (subst (asm) V_subsumes'; force)

lemma not_check_loop_non_elem:
  "x \<notin> set xs" if "\<not> check_loop_list x xs"
  using that unfolding check_loop_list_def by auto

lemma insert_ref[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> \<langle>Id\<rangle>list_set_rel \<Longrightarrow>
   \<not> check_loop_list x2a x1c \<Longrightarrow>
   ((x1b, x2a # x1c, False), x1, insert x2a x1a, False) \<in> map_set_rel \<times>\<^sub>r list_set_hd_rel x2a \<times>\<^sub>r Id"
  unfolding list_set_hd_rel_def list_set_rel_def
  by (auto dest: not_check_loop_non_elem simp: br_def)

lemma insert_map_set_ref:
  "(m, S) \<in> map_set_rel \<Longrightarrow> (insert_map_set x m, insert x S) \<in> map_set_rel"
  unfolding insert_map_set_def insert_def map_set_rel_def
  apply (auto split: option.splits)
  subgoal for x' S'
    unfolding ran_def Let_def
    apply (auto split: if_split_asm)
    apply (auto split: option.splits)
    done
  subgoal
    unfolding ran_def Let_def by (auto split: if_split_asm)
  subgoal
    unfolding ran_def Let_def
    apply (auto split: option.splits)
     apply (metis option.simps(3))
    by (metis insertCI option.inject)
  subgoal
    unfolding ran_def Let_def by (auto split: option.splits if_split_asm)
  by (auto simp: Let_def split: if_split_asm option.split)

lemma map_list_rel_memD:
  assumes "(m, xs) \<in> map_list_rel" "x \<in> set xs"
  obtains xs' where "x \<in> set xs'" "m (key x) = Some xs'"
  using assms unfolding map_list_rel_def ran_def by (auto 4 3 dest: sym)

lemma map_list_rel_memI:
  "(m, xs) \<in> map_list_rel \<Longrightarrow> m k = Some xs' \<Longrightarrow> x' \<in> set xs' \<Longrightarrow> x' \<in> set xs"
  unfolding map_list_rel_def ran_def by auto

lemma map_list_rel_grouped_by_key:
  "x' \<in> set xs' \<Longrightarrow> (m, xs) \<in> map_list_rel \<Longrightarrow> m k = Some xs' \<Longrightarrow> key x' = k"
  unfolding map_list_rel_def by auto

lemma map_list_rel_not_memI:
  "k \<noteq> key x \<Longrightarrow> m k = Some xs' \<Longrightarrow> (m, xs) \<in> map_list_rel \<Longrightarrow> x \<notin> set xs'"
  unfolding map_list_rel_def by auto

lemma map_list_rel_not_memI2:
  "x \<notin> set xs'" if "m a = Some xs'" "(m, xs) \<in> map_list_rel" "x \<notin> set xs"
  using that unfolding map_list_rel_def ran_def by auto

lemma push_map_list_ref:
  "x \<notin> set xs \<Longrightarrow> (m, xs) \<in> map_list_rel \<Longrightarrow> (push_map_list x m, x # xs) \<in> map_list_rel"
  unfolding push_map_list_def
  apply (subst map_list_rel_def)
  apply auto
  subgoal for x' xs'
    unfolding ran_def Let_def
    by (auto split: option.split_asm if_split_asm intro: map_list_rel_memI)
  subgoal
    unfolding ran_def Let_def by (auto 4 3 split: option.splits if_splits)
  subgoal for x'
    unfolding ran_def Let_def
    apply (erule map_list_rel_memD, assumption)
    apply (cases "key x = key x'")
    subgoal for xs'
      by auto
    subgoal for xs'
      apply (rule bexI[where x = xs'])
       apply safe
      apply (inst_existentials "key x'")
      apply force
      done
    done
  subgoal for k xs' x'
    unfolding Let_def
    by (auto split: option.split_asm if_split_asm dest: map_list_rel_grouped_by_key)
  subgoal
  proof -
    assume A: "x \<notin> set xs" "(m, xs) \<in> map_list_rel"
    then obtain R where *:
      "x \<notin> set xs"
      "(\<Union> x \<in> ran m. set x) = set xs"
      "\<forall>k x. m k = Some x \<longrightarrow> (\<forall>v\<in>set x. key v = k)"
      "distinct xs"
      "\<forall>k x. m k = Some x \<longrightarrow> sorted_wrt R x"
      "sorted_wrt R xs"
      "irrefl_trans_on R (set xs)"
      unfolding map_list_rel_def by auto
    have **: "sorted_wrt (\<lambda>a b. a = x \<and> b \<noteq> x \<or> a \<noteq> x \<and> b \<noteq> x \<and> R a b) xs" if
      "sorted_wrt R xs" "x \<notin> set xs" for xs
      using that by (induction xs) auto

    show ?thesis
      apply (inst_existentials "\<lambda> a b. a = x \<and> b \<noteq> x \<or> a \<noteq> x \<and> b \<noteq> x \<and> R a b")
         apply safe
      unfolding Let_def
         apply (auto split: option.split_asm if_split_asm)
      subgoal
        using \<open>irrefl_trans_on _ _\<close> unfolding irrefl_trans_on_def by blast
      subgoal for k xs'
        apply (drule map_list_rel_not_memI, assumption, rule A)
        using *(5)
        by (auto intro: **)
      using A(1) *(5) by (auto 4 3 intro: * ** A dest: map_list_rel_not_memI2)
  qed
  by (auto simp: map_list_rel_def)

lemma insert_map_set_ref'[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> map_set_rel \<Longrightarrow>
   \<not> check_subsumption' x2a x1c \<Longrightarrow>
   ((x1b, insert_map_set x2a x1c, False), x1, insert x2a x1a, False) \<in> map_set_rel \<times>\<^sub>r map_set_rel \<times>\<^sub>r Id"
  by (auto intro: insert_map_set_ref)

lemma map_list_rel_check_subsumption_map_list:
  "set xs \<subseteq> {x. V x} \<Longrightarrow> (m, xs) \<in> map_list_rel \<Longrightarrow> \<not> check_subsumption_map_list x m \<Longrightarrow> x \<notin> set xs"
  unfolding check_subsumption_map_list_def by (auto 4 3 elim!: map_list_rel_memD dest: V_subsumes')

lemma push_map_list_ref'[refine]:
  "set x1a \<subseteq> {x. V x} \<Longrightarrow>
   (x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> map_list_rel \<Longrightarrow>
   \<not> check_subsumption_map_list x2a x1c \<Longrightarrow>
   ((x1b, push_map_list x2a x1c, False), x1, x2a # x1a, False) \<in> map_set_rel \<times>\<^sub>r map_list_rel \<times>\<^sub>r Id"
  by (auto intro: push_map_list_ref dest: map_list_rel_check_subsumption_map_list)

lemma sorted_wrt_tl:
  "sorted_wrt R (tl xs)" if "sorted_wrt R xs"
  using that by (induction xs) auto

lemma irrefl_trans_on_mono:
  "irrefl_trans_on R S" if "irrefl_trans_on R S'" "S \<subseteq> S'"
  using that unfolding irrefl_trans_on_def by blast

lemma pop_map_list_ref[refine]:
  "(pop_map_list v m, S) \<in> map_list_rel" if "(m, v # S) \<in> map_list_rel"
  using that unfolding map_set_rel_def pop_map_list_def
  apply (auto split: option.splits if_split_asm simp: Let_def)
  subgoal premises prems
    using prems unfolding map_list_rel_def
    by clarsimp (rule map_list_rel_memD[OF prems(1), of v], simp, metis option.simps(3))
  subgoal premises prems for xs
    using prems unfolding map_list_rel_def
    apply auto
    subgoal for R x xs'
      unfolding ran_def
      apply (auto split: if_split_asm)
      subgoal bla premises prems
      proof -
        from prems have "sorted_wrt R xs"
          by auto
        from \<open>m (key v) = _\<close> have "v \<in> set xs"
          using map_list_rel_memD[OF \<open>(m, v # S) \<in> map_list_rel\<close>, of v] by auto
        have *: "R v x" if "x \<in> set xs" "v \<noteq> x" for x
          using that prems by - (drule map_list_rel_memI[OF \<open>_ \<in> map_list_rel\<close>], auto)
        have "v \<noteq> x"
        proof (rule ccontr, simp)
          assume "v = x"
          with \<open>x \<in> _\<close> obtain a as bs where
            "xs = a # as @ v # bs"
            unfolding in_set_conv_decomp by (cases xs) auto
          with \<open>sorted_wrt R xs\<close> have "a \<in> set xs" "R a v" "a \<in> insert v (set S)"
            using map_list_rel_memI[OF \<open>_ \<in> map_list_rel\<close> \<open>m _ = _\<close>, of a]
            by auto
          with * \<open>irrefl_trans_on _ _\<close> show False
            unfolding irrefl_trans_on_def by auto
        qed
        with prems show ?thesis
          by (auto elim: in_set_tlD dest: map_list_rel_memI[OF \<open>_ \<in> map_list_rel\<close>])
      qed
      subgoal
        by (metis map_list_rel_memI set_ConsD that)
      subgoal
        by (rule bla)
      done
    subgoal premises prems for R x
    proof -
      from map_list_rel_memD[OF \<open>_ \<in> map_list_rel\<close>, of x] \<open>x \<in> _\<close> obtain xs' where xs':
        "x \<in> set xs'" "m (key x) = Some xs'"
        by auto
      show ?thesis
      proof (cases "key x = key v")
        case True
        with prems xs' have [simp]: "xs' = xs"
          by auto
        from prems have "x \<noteq> v"
          by auto
        have "x \<in> set (tl xs)"
        proof (rule ccontr)
          assume "x \<notin> set (tl xs)"
          with xs' have "hd xs = x"
            by (cases xs) auto
          from prems have "sorted_wrt R xs"
            by auto
          from \<open>m (key v) = _\<close> have "v \<in> set xs"
            using map_list_rel_memD[OF \<open>(m, v # S) \<in> map_list_rel\<close>, of v] by auto
          have *: "R v x" if "x \<in> set xs" "v \<noteq> x" for x
            using that prems by - (drule map_list_rel_memI[OF \<open>_ \<in> map_list_rel\<close>], auto)
          with \<open>x \<in> set xs'\<close> \<open>x \<noteq> v\<close> have "R v x"
            by auto
          from \<open>v \<in> set xs\<close> \<open>hd xs = x\<close> \<open>x \<noteq> v\<close> have "R x v"
            unfolding in_set_conv_decomp
            apply auto
            using \<open>sorted_wrt R xs\<close>
            subgoal for ys
              by (cases ys) auto
            done
          with \<open>R v x\<close> \<open>irrefl_trans_on _ _\<close> \<open>x \<in> set S\<close> show False
            unfolding irrefl_trans_on_def by blast
        qed
        with xs' show ?thesis
          unfolding \<open>xs' = _\<close> ran_def by auto
      next
        case False
        with xs' show ?thesis
          unfolding ran_def by auto
      qed
    qed
    subgoal
      by (meson in_set_tlD)
    subgoal for R
      by (blast intro: irrefl_trans_on_mono sorted_wrt_tl)
    done
  done

lemma tl_list_set_ref:
  "(m, S) \<in> map_set_rel \<Longrightarrow>
   (st, ST) \<in> list_set_hd_rel x \<Longrightarrow>
   (tl st, ST - {x}) \<in> \<langle>Id\<rangle>list_set_rel"
  unfolding list_set_hd_rel_def list_set_rel_def
  by (auto simp: br_def distinct_hd_tl dest: in_set_tlD in_hd_or_tl_conv)

lemma succs_id_ref:
  "(succs x, succs x) \<in> \<langle>Id\<rangle> list_rel"
  by simp

lemma dfs_map_dfs_refine':
  "dfs_map P \<le> \<Down> (Id \<times>\<^sub>r map_set_rel) (dfs1 P')" if "(P, P') \<in> map_set_rel"
  using that
  unfolding dfs_map_def dfs1_def
  apply refine_rcg
    using [[goals_limit=1]]
             apply (clarsimp, rule check_subsumption'_ref; assumption)
            apply (clarsimp, rule refine_True; assumption)
          apply (clarsimp, rule check_subsumption_ref; assumption)
          apply (simp; fail)
         apply (clarsimp; rule succs_id_ref; fail)
        apply (clarsimp, rule push_map_list_ref'; assumption)
      by (auto intro: insert_map_set_ref pop_map_list_ref)

lemma dfs_map_dfs_refine:
  "dfs_map P \<le> \<Down> (Id \<times>\<^sub>r map_set_rel) (dfs P')" if "(P, P') \<in> map_set_rel" "V a\<^sub>0"
proof -
  note dfs_map_dfs_refine'[OF \<open>_ \<in> map_set_rel\<close>]
  also note dfs1_dfs_ref[OF \<open>V a\<^sub>0\<close>]
  finally show ?thesis .
qed

end (* Liveness Search Space Key *)

end (* Theory *)
