theory Liveness_Subsumption_Map
  imports Liveness_Subsumption "../library/DRAT_Misc"
begin

locale Liveness_Search_Space_Key_Defs =
  Liveness_Search_Space_Defs E for E :: "'v \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes key :: "'v \<Rightarrow> 'k"
begin

definition "check_loop_list v ST = (\<exists> v' \<in> set ST. v' \<preceq> v)"

definition "insert_map_set v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in S(k \<mapsto> (insert v S'))
"

definition "push_map_list v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> []) in S(k \<mapsto> v # S')
"

definition "check_subsumption_map_set v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in (\<exists> x \<in> S'. v \<preceq> x)
"

definition "check_subsumption_map_list v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> []) in (\<exists> x \<in> set S'. x \<preceq> v)
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
  assumes subsumes_key[intro, simp]: "a \<preceq> b \<Longrightarrow> key a = key b"
begin

(* XXX Duplication *)
definition
  "map_set_rel =
    {(m, s). \<Union> ran m = s \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> x. key v = k))}"

term sorted

definition
  "map_list_rel =
    {(m, xs). \<Union> (set ` ran m) = set xs \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> set x. key v = k))
          \<and> (\<exists> R. (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> sorted_by_rel R x) \<and> sorted_by_rel R xs)
          \<and> distinct xs
    }"

definition "list_set_rel \<equiv> {(l, s). set l = s \<and> distinct l}"

definition "list_set_hd_rel x \<equiv> {(l, s). set l = s \<and> distinct l \<and> l \<noteq> [] \<and> hd l = x}"

lemma
  "(Map.empty, []) \<in> map_list_rel"
  unfolding map_list_rel_def by auto

lemma rel_start[refine]:
  "((P, Map.empty, a\<^sub>0), P', [], a\<^sub>0) \<in> map_set_rel \<times>\<^sub>r map_list_rel \<times>\<^sub>r Id" if "(P, P') \<in> map_set_rel"
  using that unfolding map_set_rel_def map_list_rel_def by auto

lemma refine_True:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> (x1c, x1a) \<in> map_list_rel \<Longrightarrow> ((x1b, x1c, True), x1, x1a, True) \<in> map_set_rel \<times>\<^sub>r map_list_rel \<times>\<^sub>r Id"
  by simp

lemma refine_True':
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> (x1c, x1a) \<in> list_set_rel \<Longrightarrow> ((x1b, x1c, True), x1, x1a, True) \<in> map_set_rel \<times>\<^sub>r list_set_hd_rel x \<times>\<^sub>r Id"
  unfolding map_set_rel_def list_set_rel_def oops

lemma check_subsumption_ref[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> check_subsumption_map_set x2a x1b = (\<exists>x\<in>x1. x2a \<preceq> x)"
  unfolding map_set_rel_def list_set_rel_def check_subsumption_map_set_def
  unfolding ran_def by (auto split: option.splits)

lemma check_subsumption'_ref[refine]:
  "(m, xs) \<in> map_list_rel \<Longrightarrow> check_subsumption_map_list x m = check_loop x xs"
  unfolding map_list_rel_def list_set_rel_def check_subsumption_map_list_def check_loop_def
  unfolding ran_def apply (auto split: option.splits)
  subgoal for R x' xs'
    apply rule
     apply assumption
    sorry
  by force

lemma not_check_loop_non_elem:
  "x \<notin> set xs" if "\<not> check_loop_list x xs"
  using that unfolding check_loop_list_def by auto

lemma insert_ref[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> list_set_rel \<Longrightarrow>
   \<not> check_loop_list x2a x1c \<Longrightarrow>
   ((x1b, x2a # x1c, False), x1, insert x2a x1a, False) \<in> map_set_rel \<times>\<^sub>r list_set_hd_rel x2a \<times>\<^sub>r Id"
  unfolding list_set_hd_rel_def list_set_rel_def by (auto dest: not_check_loop_non_elem)

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
  done

lemma map_list_rel_memD:
  assumes "(m, xs) \<in> map_list_rel" "x \<in> set xs"
  obtains xs' where "x \<in> set xs'" "m (key x) = Some xs'"
  apply atomize_elim
  using assms
  unfolding map_list_rel_def
  apply auto
  unfolding ran_def
    sorry

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
          "UNION (ran m) set = set xs"
          "\<forall>k x. m k = Some x \<longrightarrow> (\<forall>v\<in>set x. key v = k)"
          "distinct xs"
          "\<forall>k x. m k = Some x \<longrightarrow> sorted_by_rel R x"
          "sorted_by_rel R xs"
          unfolding map_list_rel_def by auto
        have **: "sorted_by_rel (\<lambda>a b. a = x \<or> R a b) xs" if
          "sorted_by_rel R xs" "x \<notin> set xs" for xs
          using that by (induction xs) auto

        show ?thesis
          apply (inst_existentials "\<lambda> a b. a = x \<or> R a b")
              apply auto
            unfolding Let_def
             apply (auto split: option.split_asm if_split_asm)
            subgoal for k xs'
              apply (drule map_list_rel_not_memI, assumption, rule A)
              using *(5)
              by (auto intro: **)
            subgoal for xs'
              using A(1) *(5)
              by (auto intro: ** A dest: map_list_rel_not_memI2)
            subgoal for xs'
              using A(1) *(5)
              by (auto 4 3 intro: ** A dest: map_list_rel_not_memI2)
            subgoal
              using A by (auto intro: * **)
            done
        qed
        by (auto simp: map_list_rel_def)

lemma insert_map_set_ref'[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> map_set_rel \<Longrightarrow>
   \<not> check_subsumption' x2a x1c \<Longrightarrow>
   ((x1b, insert_map_set x2a x1c, False), x1, insert x2a x1a, False) \<in> map_set_rel \<times>\<^sub>r map_set_rel \<times>\<^sub>r Id"
  by (auto intro: insert_map_set_ref)

lemma push_map_list_ref'[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> map_list_rel \<Longrightarrow>
   \<not> check_subsumption_map_list x2a x1c \<Longrightarrow>
   ((x1b, push_map_list x2a x1c, False), x1, x2a # x1a, False) \<in> map_set_rel \<times>\<^sub>r map_list_rel \<times>\<^sub>r Id"
  by (auto intro: push_map_list_ref)

lemma pop_map_list_ref[refine]:
  "(pop_map_list v m, tl S) \<in> map_list_rel" if "(m, S) \<in> map_list_rel"
  using that unfolding map_set_rel_def delete_map_set_def
  apply (auto split: option.splits if_split_asm simp: Let_def)
  subgoal for X
    by (auto simp: ran_def)
  subgoal for X
    by (auto simp: ran_def split: if_split_asm)
  subgoal for X
    by (auto simp: ran_def split: if_split_asm)
  subgoal for x' x'' S'
    unfolding ran_def
      apply (auto split: option.splits if_split_asm)
    by (metis insertE insert_Diff option.inject set_minus_singleton_eq)
  done

thm pop_map_list_ref

lemma tl_list_set_ref:
  "(m, S) \<in> map_set_rel \<Longrightarrow>
   (st, ST) \<in> list_set_hd_rel x \<Longrightarrow>
   (tl st, ST - {x}) \<in> list_set_rel"
  unfolding list_set_hd_rel_def list_set_rel_def
  apply auto
    apply (blast dest: in_set_tlD)
  apply (simp add: distinct_hd_tl)
  by (meson in_hd_or_tl_conv)

lemma succs_id_ref:
  "(succs x, succs x) \<in> \<langle>Id\<rangle> list_rel"
  by simp

lemma dfs_map_dfs_refine:
  "dfs_map P \<le> \<Down> (Id \<times>\<^sub>r map_set_rel) (dfs P')" if "(P, P') \<in> map_set_rel"
  using that
  unfolding dfs_map_def dfs_def
  apply refine_rcg
    using [[goals_limit=1]]
            apply (clarsimp, rule check_subsumption'_ref, assumption)
           apply (clarsimp, rule refine_True; assumption)
          apply (clarsimp, rule check_subsumption_ref; assumption)
          apply (simp; fail)
         apply (clarsimp; rule succs_id_ref; fail)
      apply (clarsimp, rule push_map_list_ref'; assumption)
      by (auto intro: insert_map_set_ref pop_map_list_ref)

end (* Search Space Nodes Finite Strict Key *)

(*
locale Liveness_Search_Space_Key1_Defs =
  Liveness_Search_Space_Key_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"
begin

definition dfs_map1 :: "('b \<rightharpoonup> 'a set) \<Rightarrow> (bool \<times> ('b \<rightharpoonup> 'a set)) nres" where
  "dfs_map1 P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      if check_subsumption_map_list v ST then RETURN (P, ST, True)
      else do {
        if check_subsumption_map_set v P then
          RETURN (P, ST, False)
        else do {
            let ST = push_map_list v ST;
            ASSERT (reachable v);
            (P, ST, r) \<leftarrow>
              FOREACH\<^sub>C (set (succs v)) (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
            let ST = pop_map_list v ST;
            let P = insert_map_set v P;
            RETURN (P, ST, r)
          }
      }
    ) (P,Map.empty,a\<^sub>0);
    RETURN (r, P)
  }"

end (* Search Space Nodes Empty Key Defs 1 *)

locale Search_Space_Nodes_finite_strict_Key1 =
  Search_Space_Nodes_Empty_Key1_Defs +
  Search_Space_Nodes_finite_strict_Key +
  assumes succs_correct: "reachable a \<Longrightarrow> set (succs a) = {x. a \<rightarrow> x}"
begin

lemma init_ref:
  "((P, Map.empty, a\<^sub>0), P, Map.empty, a\<^sub>0) \<in> Id \<times>\<^sub>r Id \<times>\<^sub>r {(x,y). x = y \<and> reachable x}"
  by simp

lemma
  "dfs_map1 P \<le> \<Down> Id (dfs_map P)"
  unfolding dfs_map1_def dfs_map_def
  apply refine_rcg
              apply (rule init_ref; fail)
             apply refine_dref_type
             apply (simp; fail)+
         apply force
        apply (rule inj_on_id; fail)
  by (auto 4 3 dest: reachable_step succs_correct) (* XXX Add to automation? *)

end (* Search Space Nodes Finite Strict Key 1 *)
*)

end (* Theory *)