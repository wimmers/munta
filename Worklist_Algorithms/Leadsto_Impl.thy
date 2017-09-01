theory Leadsto_Impl
  imports Leadsto_Map Unified_PW_Impl Liveness_Subsumption_Impl
begin

(* XXX Move *)
definition
  "list_of_set S = SPEC (\<lambda>l. set l = S)"

(* XXX Move *)
lemma lso_id_hnr:
  "(return o id, list_of_set) \<in> (lso_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn A"
  unfolding list_of_set_def lso_assn_def hr_comp_def br_def by sepref_to_hoare sep_auto

sepref_register hm.op_hms_empty

context Worklist_Map2_Impl
begin

sepref_thm pw_algo_map2_impl is
  "uncurry0 (pw_algo_map2)" ::
  "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a (hm.hms_assn' id_assn (lso_assn A))"
  unfolding pw_algo_map2_def add_pw'_map2_alt_def PR_CONST_def
  supply [[goals_limit = 1]]
  supply conv_to_is_Nil[simp]
  unfolding fold_lso_bex
  unfolding take_from_list_alt_def
  apply (rewrite in "{a\<^sub>0}" lso_fold_custom_empty)
  unfolding hm.hms_fold_custom_empty
  apply (rewrite in "[a\<^sub>0]" HOL_list.fold_custom_empty)
   apply (rewrite in "{}" lso_fold_custom_empty)
  unfolding F_split (* XXX Why? F only appears in the invariant *)
  by sepref

concrete_definition (in -) pw_impl
for Lei a\<^sub>0i Fi succsi emptyi
uses Worklist_Map2_Impl.pw_algo_map2_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"

end (* Worklist Map 2 Impl *)

locale Leadsto_Search_Space_Key_Impl =
  Leadsto_Search_Space_Key a\<^sub>0 F _ empty _ E key F' _ _ P Q succs succs1 +
  Liveness_Search_Space_Key_Impl a\<^sub>0 F _ V empty succs E key A succsi a\<^sub>0i Lei keyi copyi
  for key :: "'v :: {heap} \<Rightarrow> 'k :: {hashable,heap}"
  and a\<^sub>0 F F' copyi P Q V empty succs succs1 E A succsi a\<^sub>0i Lei keyi +
  fixes succs1i and Lei' and Pi Qi
  assumes  succs1_impl: "(succs1i, (RETURN \<circ>\<circ> PR_CONST) succs1) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A"
    and Lei': "(uncurry Lei', uncurry ((RETURN \<circ>\<circ>\<circ> PR_CONST) op \<unlhd>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    and [sepref_fr_rules]: "(Pi,RETURN o P) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn" "(Qi,RETURN o Q) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
begin

sublocale Worklist_Map2_Impl _ _ "\<lambda> _. False" _ succs1 _ _ "(\<lambda>_. False)" _ succs1i _ _ Lei'
  by (standard; rule refinements Lei' succs1_impl)

sepref_register pw_algo_map2_copy
sepref_register P Q

lemmas [sepref_fr_rules] = lso_id_hnr ran_of_map_impl.refine[folded hm.hms_assn'_id_hms_assn]

lemma pw_algo_map2_copy_fold:
  "PR_CONST pw_algo_map2_copy = A'.pw_algo_map2"
  unfolding pw_algo_map2_copy_def by simp

lemmas [sepref_fr_rules] = pw_algo_map2_impl.refine_raw[folded pw_algo_map2_copy_fold]

definition "has_cycle_map_copy \<equiv> has_cycle_map"

lemma has_cycle_map_copy_fold:
  "PR_CONST has_cycle_map_copy = has_cycle_map"
  unfolding has_cycle_map_copy_def by simp

sepref_register has_cycle_map_copy

lemma has_cycle_map_fold:
  "has_cycle_map = dfs_map'"
  unfolding has_cycle_map_def dfs_map'_def
  by (subst Liveness_Search_Space_Key_Defs.dfs_map_alt_def) standard

lemmas [sepref_fr_rules] =
  dfs_map'_impl.refine_raw[folded has_cycle_map_fold, folded has_cycle_map_copy_fold]

sepref_definition leadsto_impl is
  "uncurry0 leadsto_map4'" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding leadsto_map4'_def
  unfolding pw_algo_map2_copy_def[symmetric]
  unfolding has_cycle_map_copy_def[symmetric]
  unfolding hm.hms_fold_custom_empty
  unfolding list_of_set_def[symmetric]
  by sepref

end (* Leadsto Search Space Key Impl *)

end (* End of theory *)