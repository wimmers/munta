theory Liveness_Subsumption_Map
  imports Liveness_Subsumption "../library/DRAT_Misc"
begin

locale Search_Space_Nodes_Empty_Key_Defs =
  Search_Space_Nodes_Empty_Defs E for E :: "'v \<Rightarrow> 'v \<Rightarrow> bool" +
  fixes key :: "'v \<Rightarrow> 'k"
begin

definition "check_loop_list v ST = (\<exists> v' \<in> set ST. v' \<preceq> v)"

definition "insert_map_set v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in S(k \<mapsto> (insert v S'))
"

definition "check_subsumption v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in (\<exists> x \<in> S'. v \<preceq> x)
"

definition "check_subsumption' v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in (\<exists> x \<in> S'. x \<preceq> v)
"

definition "delete_map_set v S \<equiv>
  let k = key v; S' = (case S k of Some S \<Rightarrow> S | None \<Rightarrow> {}) in S(k \<mapsto> (S' - {v}))
"

definition dfs_map :: "('k \<rightharpoonup> 'v set) \<Rightarrow> (bool \<times> ('k \<rightharpoonup> 'v set)) nres" where
  "dfs_map P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      if check_subsumption' v ST then RETURN (P, ST, True)
      else do {
        if check_subsumption v P then
          RETURN (P, ST, False)
        else do {
            let ST = insert_map_set v ST;
            (P, ST, r) \<leftarrow>
              FOREACH\<^sub>C {v' . v \<rightarrow> v'} (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
            let ST = delete_map_set v ST;
            let P = insert_map_set v P;
            RETURN (P, ST, r)
          }
      }
    ) (P,Map.empty,a\<^sub>0);
    RETURN (r, P)
  }"

end (* Search Space Nodes Empty Key Defs *)

locale Search_Space_Nodes_finite_strict_Key =
  Search_Space_Nodes_finite_strict + Search_Space_Nodes_Empty_Key_Defs +
  assumes subsumes_key[intro, simp]: "a \<preceq> b \<Longrightarrow> key a = key b"
begin

(* XXX Duplication *)
definition
  "map_set_rel =
    {(m, s). \<Union> ran m = s \<and> (\<forall> k. \<forall> x. m k = Some x \<longrightarrow> (\<forall> v \<in> x. key v = k))}"

definition "list_set_rel \<equiv> {(l, s). set l = s \<and> distinct l}"

definition "list_set_hd_rel x \<equiv> {(l, s). set l = s \<and> distinct l \<and> l \<noteq> [] \<and> hd l = x}"

lemma rel_start[refine]:
  "((P, Map.empty, a\<^sub>0), P', {}, a\<^sub>0) \<in> map_set_rel \<times>\<^sub>r map_set_rel \<times>\<^sub>r Id" if "(P, P') \<in> map_set_rel"
  using that unfolding map_set_rel_def list_set_rel_def by auto

lemma check_loop_ref[refine]:
  "check_loop_list x xs = check_loop x S" if "(xs, S) \<in> list_set_rel"
  using that unfolding check_loop_list_def check_loop_def list_set_rel_def by auto

lemma refine_True:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> (x1c, x1a) \<in> map_set_rel \<Longrightarrow> ((x1b, x1c, True), x1, x1a, True) \<in> map_set_rel \<times>\<^sub>r map_set_rel \<times>\<^sub>r Id"
  by simp

lemma refine_True':
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> (x1c, x1a) \<in> list_set_rel \<Longrightarrow> ((x1b, x1c, True), x1, x1a, True) \<in> map_set_rel \<times>\<^sub>r list_set_hd_rel x \<times>\<^sub>r Id"
  unfolding map_set_rel_def list_set_rel_def oops

lemma check_subsumption_ref[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> check_subsumption x2a x1b = (\<exists>x\<in>x1. x2a \<preceq> x)"
  unfolding map_set_rel_def list_set_rel_def check_subsumption_def
  unfolding ran_def by (auto split: option.splits)

lemma check_subsumption'_ref[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow> check_subsumption' x2a x1b = check_loop x2a x1"
  unfolding map_set_rel_def list_set_rel_def check_subsumption'_def check_loop_def
  unfolding ran_def by (force split: option.splits)

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
  "(m, S) \<in> map_set_rel \<Longrightarrow>
   (insert_map_set x m, insert x S) \<in> map_set_rel"
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

lemma insert_map_set_ref'[refine]:
  "(x1b, x1) \<in> map_set_rel \<Longrightarrow>
   (x1c, x1a) \<in> map_set_rel \<Longrightarrow>
   \<not> check_subsumption' x2a x1c \<Longrightarrow>
   ((x1b, insert_map_set x2a x1c, False), x1, insert x2a x1a, False) \<in> map_set_rel \<times>\<^sub>r map_set_rel \<times>\<^sub>r Id"
  by (auto intro: insert_map_set_ref)

lemma delete_map_set_ref[refine]:
  "(delete_map_set x m, S - {x}) \<in> map_set_rel" if "(m, S) \<in> map_set_rel"
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

lemma tl_list_set_ref:
  "(m, S) \<in> map_set_rel \<Longrightarrow>
   (st, ST) \<in> list_set_hd_rel x \<Longrightarrow>
   (tl st, ST - {x}) \<in> list_set_rel"
  unfolding list_set_hd_rel_def list_set_rel_def
  apply auto
    apply (blast dest: in_set_tlD)
  apply (simp add: distinct_hd_tl)
  by (meson in_hd_or_tl_conv)

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
        apply (rule inj_on_id; fail)
         apply (simp; fail)
      apply (clarsimp, rule insert_map_set_ref'; assumption)
      by (auto intro: insert_map_set_ref delete_map_set_ref)

end (* Search Space Nodes Finite Strict Key *)

locale Search_Space_Nodes_Empty_Key1_Defs =
  Search_Space_Nodes_Empty_Key_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"
begin

term succs

definition dfs_map1 :: "('b \<rightharpoonup> 'a set) \<Rightarrow> (bool \<times> ('b \<rightharpoonup> 'a set)) nres" where
  "dfs_map1 P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      if check_subsumption' v ST then RETURN (P, ST, True)
      else do {
        if check_subsumption v P then
          RETURN (P, ST, False)
        else do {
            let ST = insert_map_set v ST;
            ASSERT (reachable v);
            (P, ST, r) \<leftarrow>
              FOREACH\<^sub>C (set (succs v)) (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
            let ST = delete_map_set v ST;
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

end (* Theory *)