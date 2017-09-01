theory Next_Key
  imports Heap_Hash_Map
begin

section \<open>A next-key operation for hashmaps\<close>

subsection \<open>Definition and key properties\<close>

definition
  "hm_it_next_key ht = do {
    n\<leftarrow>Array.len (the_array ht);
    if n = 0 then raise ''Map is empty!''
    else do {
      i\<leftarrow>hm_it_adjust (n - 1) ht;
      l\<leftarrow>Array.nth (the_array ht) i;
      case l of
        [] \<Rightarrow> raise ''Map is empty!''
      | (x # _) \<Rightarrow> return (fst x)
    }
  }
"

lemma hm_it_next_key_rule:
  "<is_hashmap m ht> hm_it_next_key ht <\<lambda>r. is_hashmap m ht * \<up> (r \<in> dom m)>"
  if "m \<noteq> Map.empty"
  using that
  unfolding hm_it_next_key_def
  unfolding is_hashmap_def unfolding is_hashmap'_def
  apply (sep_auto intro: hm_it_adjust_rule)
  subgoal
    using le_imp_less_Suc by fastforce
  subgoal premises prems for l xs i xs'
  proof -
    from prems have "l ! i \<noteq> []"
      by (auto simp: concat_take_Suc_empty)
    with prems(1-6) show ?thesis
      apply (cases xs')
       apply sep_auto
      apply sep_auto
      subgoal for a b list aa ba
        apply (rule weak_map_of_SomeI[of _ b])
        apply auto
        apply (rule bexI[of _ "l ! i"])
        subgoal
          by (metis list.set_intros(1))
        subgoal
          by (cases "length l"; fastforce simp: take_Suc_conv_app_nth)
        done
      done
  qed
  done

lemma
  "<P * R> c <\<lambda> r. Q r * R>" if "<P> c <\<lambda> r. Q r>"
  using that
  by (simp add: frame_rule)


definition
  "next_key m = do {
    ASSERT (m \<noteq> Map.empty);
    k \<leftarrow> SPEC (\<lambda> k. k \<in> dom m);
    RETURN k
  }
  "

lemma hm_it_next_key_next_key_aux:
  fixes K :: "_ :: {hashable, heap} \<Rightarrow> _"
  assumes "CONSTRAINT is_pure K" "nofail (next_key m)"
  shows
    "<hm.assn K V m mi>
      hm_it_next_key mi
    <\<lambda>r. \<exists>\<^sub>Axa. hm.assn K V m mi * K xa r * true * \<up> (RETURN xa \<le> next_key m)>"
  using \<open>nofail _\<close> unfolding next_key_def
  apply (simp add: pw_bind_nofail pw_ASSERT(1))
  unfolding hm.assn_def hr_comp_def
  apply sep_auto
  subgoal for m'
    apply (rule cons_post_rule)
     apply (rule hm_it_next_key_rule)
     defer
     apply (sep_auto eintros del: exI)
    subgoal premises prems for x v'
    proof -
      from prems obtain k v where "m k = Some v" "(x, k) \<in> the_pure K" "(v', v) \<in> the_pure V"
        apply atomize_elim
        by (meson map_rel_obtain2)
      with prems \<open>CONSTRAINT is_pure K\<close> show ?thesis
        apply -
        apply (rule exI[where x = k], rule exI[where x = m'])
        apply sep_auto
        apply (rule entailsI)
        apply sep_auto
        by (metis mod_pure_star_dist mod_star_trueI pure_def pure_the_pure)
    qed
    by force
  done

lemma hm_it_next_key_next_key:
  fixes K :: "_ :: {hashable, heap} \<Rightarrow> _"
  assumes "CONSTRAINT is_pure K"
  shows
    "(hm_it_next_key, next_key) \<in> (hm.assn K V)\<^sup>k \<rightarrow>\<^sub>a K"
  using assms by sepref_to_hoare (sep_auto intro!: hm_it_next_key_next_key_aux)

lemma hm_it_next_key_next_key':
  shows
    "(hm_it_next_key, next_key) \<in> (hm.hms_assn V)\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding hm.hms_assn_def
  apply sepref_to_hoare
  apply sep_auto
  unfolding next_key_def
  apply (simp add: refine_pw_simps)
  subgoal for m m' mi
    apply (rule cons_rule[where
          P' = "is_hashmap mi m' * map_assn V m mi * \<up>(mi \<noteq> Map.empty)"
          and Q = "\<lambda> x. is_hashmap mi m' * \<up> (x \<in> dom mi) * map_assn V m mi"]
        )
      apply (sep_auto; unfold map_assn_def; auto; fail)+
    apply (rule norm_pre_pure_rule1)
    apply (rule frame_rule[OF hm_it_next_key_rule[of mi m']])
    by (sep_auto; unfold map_assn_def; auto)+
  done

subsection \<open>Computing the range of a map\<close>

definition ran_of_map where
  "ran_of_map m \<equiv> do
      {
        (xs, m) \<leftarrow> WHILEIT
          (\<lambda> (xs, m'). finite (dom m') \<and> ran m = ran m' \<union> set xs) (\<lambda> (_, m). Map.empty \<noteq> m)
            (\<lambda> (xs, m). do
              {
                k \<leftarrow> next_key m;
                let (x, m) = op_map_extract k m;
                ASSERT (x \<noteq> None);
                RETURN (the x # xs, m)
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

lemma ran_of_map_correct[refine]:
  "ran_of_map m \<le> SPEC (\<lambda> r. set r = ran m)" if "finite (dom m)"
  using that unfolding ran_of_map_def next_key_def
  apply (refine_vcg wf_ran_of_map_var)
         apply (simp; fail)
        apply (simp; fail)
       apply (simp; fail)
      apply (clarsimp; fail)
     apply (clarsimp; fail)
  subgoal
    unfolding dom_def by (clarsimp, auto dest: insert_restrict_ran)
  subgoal
    unfolding ran_of_map_var_def op_map_extract_def by (fastforce intro: card_Diff1_less)
  by auto

end -- \<open>End of private context for auxiliary facts and definitions\<close>

sepref_register next_key :: "(('b, 'a) i_map \<Rightarrow> 'b nres)"

definition (in imp_map_is_empty) [code_unfold]: "hms_is_empty \<equiv> is_empty"

lemma (in imp_map_is_empty) hms_empty_rule [sep_heap_rules]:
  "<hms_assn A m mi> hms_is_empty mi <\<lambda>r. hms_assn A m mi * \<up>(r \<longleftrightarrow> m=Map.empty)>\<^sub>t"
  unfolding hms_is_empty_def hms_assn_def map_assn_def by sep_auto

context imp_map_is_empty
begin

lemma hms_is_empty_hnr[sepref_fr_rules]:
  "(hms_is_empty, RETURN o op_map_is_empty) \<in> (hms_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by sepref_to_hoare sep_auto

sepref_decl_impl is_empty: hms_is_empty_hnr uses op_map_is_empty.fref[where V = Id] .
print_theorems

end

lemma (in imp_map) hms_assn'_id_hms_assn:
  "hms_assn' id_assn A = hms_assn A"
  by (subst hms_assn'_def) simp

(* This is to make the pre-processing phase pick the right type for the input *)
lemma [intf_of_assn]:
  "intf_of_assn (hm.hms_assn' a b) TYPE(('aa, 'bb) i_map)"
  by simp

context
  notes [sepref_fr_rules] = hm_it_next_key_next_key'[folded hm.hms_assn'_id_hms_assn]
begin

sepref_definition ran_of_map_impl is
  "ran_of_map" :: "(hm.hms_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn A"
  unfolding ran_of_map_def hm.hms_assn'_id_hms_assn[symmetric]
  unfolding op_map_is_empty_def[symmetric]
  unfolding hm.hms_fold_custom_empty HOL_list.fold_custom_empty
  by sepref

end (* End of anonymous context for setup *)

end (* Theory *)