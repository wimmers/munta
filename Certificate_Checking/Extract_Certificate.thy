theory Extract_Certificate
  imports
    Worklist_Algorithms.Unified_PW_Impl
    Worklist_Algorithms.Next_Key
    DBM.DBM_Operations_Impl_Refine
    Worklist_Algorithms.Leadsto_Impl
begin

subsection \<open>Turning a map into a list\<close>

definition list_of_map where
  "list_of_map m \<equiv> do
      {
        (xs, m) \<leftarrow> WHILEIT
          (\<lambda> (xs, m'). finite (dom m') \<and> m = m' ++ map_of xs \<and> dom m' \<inter> dom (map_of xs) = {})
             (\<lambda> (_, m). Map.empty \<noteq> m)
            (\<lambda> (xs, m). do
              {
                k \<leftarrow> next_key m;
                let (x, m) = op_map_extract k m;
                ASSERT (x \<noteq> None);
                RETURN ((k, the x) # xs, m)
              }
            )
            ([], m);
        RETURN xs
      }
  "

context
begin

private definition
  "ran_of_map_var = (inv_image (measure (card o dom)) (\<lambda> (a, b). b))"

private lemma wf_ran_of_map_var:
  "wf ran_of_map_var"
  unfolding ran_of_map_var_def by auto

(* XXX Maybe move *)
private lemma insert_restrict_ran:
  "insert v (ran (m |` (- {k}))) = ran m " if "m k = Some v"
  using that unfolding ran_def restrict_map_def by force

private lemma 1:
  "(m |` (- {x}))(x \<mapsto> y) = m" if "m x = Some y"
  using that unfolding restrict_map_def by auto

private lemma 2:
  "(m1 ++ m2)(x \<mapsto> y) = m1(x \<mapsto> y) ++ m2" if "x \<notin> dom m2"
  using that by auto

lemma list_of_map_correct[refine]:
  "list_of_map m \<le> SPEC (\<lambda> r. map_of r = m)" if "finite (dom m)"
  using that unfolding list_of_map_def next_key_def
  apply (refine_vcg wf_ran_of_map_var)
         apply (clarsimp; fail)+
  subgoal for s xs m' x v xs' xs1 xs'1
    unfolding dom_def apply (clarsimp simp: map_upd_eq_restrict)
    apply (subst 2)
     apply auto
    apply (subst 1)
     apply auto
    done
  unfolding ran_of_map_var_def by (fastforce intro: card_Diff1_less split: if_split_asm)+

end \<comment> \<open>End of private context for auxiliary facts and definitions\<close>

context
  fixes K :: "_ \<Rightarrow> _ :: {hashable, heap} \<Rightarrow> assn"
  assumes is_pure_K[safe_constraint_rules]: "is_pure K"
  and left_unique_K[safe_constraint_rules]: "IS_LEFT_UNIQUE (the_pure K)"
  and right_unique_K[safe_constraint_rules]: "IS_RIGHT_UNIQUE (the_pure K)"
  notes [sepref_fr_rules] = hm_it_next_key_next_key''[OF is_pure_K]
begin

sepref_definition list_of_map_impl is
  "list_of_map" :: "(hm.hms_assn' K A)\<^sup>d \<rightarrow>\<^sub>a (list_assn (K \<times>\<^sub>a A))"
  unfolding list_of_map_def hm.hms_assn'_id_hms_assn[symmetric]
  unfolding op_map_is_empty_def[symmetric]
  unfolding hm.hms_fold_custom_empty HOL_list.fold_custom_empty
  by sepref

end (* Anonymous context for setup *)

lemmas list_of_map_impl_code[code] =
  list_of_map_impl_def[of "pure Id", simplified, OF Sepref_Constraints.safe_constraint_rules(41)]

context
  notes [sepref_fr_rules] = hm_it_next_key_next_key'[folded hm.hms_assn'_id_hms_assn]
begin

sepref_definition list_of_map_impl' is
  "list_of_map" :: "(hm.hms_assn A)\<^sup>d \<rightarrow>\<^sub>a (list_assn (id_assn \<times>\<^sub>a A))"
  unfolding list_of_map_def hm.hms_assn'_id_hms_assn[symmetric]
  unfolding op_map_is_empty_def[symmetric]
  unfolding hm.hms_fold_custom_empty HOL_list.fold_custom_empty
  by sepref

end (* Anonymous context for setup *)

context Worklist_Map2_Impl
begin

definition extract_certificate :: "_ nres" where
  "extract_certificate = do {
   (_, passed) \<leftarrow> pw_algo_map2;
   list_of_map passed
  }"

context
begin

private definition
  "pw_algo_map2_copy = pw_algo_map2"

sepref_register pw_algo_map2_copy

lemma pw_algo_map2_copy_fold:
  "PR_CONST pw_algo_map2_copy = pw_algo_map2"
  unfolding pw_algo_map2_copy_def by simp

lemmas [sepref_fr_rules] =
  pw_algo_map2_impl.refine_raw[folded pw_algo_map2_copy_fold]
  list_of_map_impl.refine[OF pure_K left_unique_K right_unique_K]

sepref_thm extract_certificate_impl is
  "uncurry0 extract_certificate" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a (list_assn (K \<times>\<^sub>a lso_assn A))"
  unfolding extract_certificate_def pw_algo_map2_copy_def[symmetric] by sepref

end

end

concrete_definition extract_certificate_impl
  uses Worklist_Map2_Impl.extract_certificate_impl.refine_raw

print_theorems

end