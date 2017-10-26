theory Heap_Hash_Map
  imports
    Separation_Logic_Imperative_HOL.Sep_Main Separation_Logic_Imperative_HOL.Sep_Examples
    Refine_Imperative_HOL.IICF
begin

(* TODO: Move to Separation_Logic_Imperative_HOL *)
definition big_star :: "assn multiset \<Rightarrow> assn" ("\<And>* _" [60] 90) where
  "big_star S \<equiv> fold_mset (op *) emp S"

interpretation comp_fun_commute_mult:
  comp_fun_commute "(op * :: ('a :: ab_semigroup_mult \<Rightarrow> _ \<Rightarrow> _))"
  by standard (auto simp: ab_semigroup_mult_class.mult.left_commute)

lemma sep_big_star_insert [simp]: "\<And>* (add_mset x S) = (x * \<And>* S)"
  by (auto simp: big_star_def)

lemma sep_big_star_union [simp]: "\<And>* (S + T) = (\<And>* S * \<And>* T)"
  by (auto simp: big_star_def comp_fun_commute_mult.fold_mset_fun_left_comm)

lemma sep_big_star_empty [simp]: "\<And>* {#} = emp"
  by (simp add: big_star_def)

(* TODO: Move to Sepref-IICF *)
definition "map_assn V m mi \<equiv>
  \<up> (dom mi = dom m \<and> finite (dom m)) *
  (\<And>* {# V (the (m k)) (the (mi k)) . k \<in># mset_set (dom m)#})
"

lemma map_assn_empty_map[simp]:
  "map_assn A Map.empty Map.empty = emp"
  unfolding map_assn_def by auto

lemma in_mset_union_split:
  "mset_set S = mset_set (S - {k}) + {#k#}" if "k \<in> S" "finite S"
  using that by (auto simp: mset_set.remove)

lemma in_mset_dom_union_split:
  "mset_set (dom m) = mset_set (dom m - {k}) + {#k#}" if "m k = Some v" "finite (dom m)"
  apply (rule in_mset_union_split)
  using that by (auto)

lemma dom_remove_not_in_dom_simp[simp]:
  "dom m - {k} = dom m" if "m k = None"
  using that unfolding dom_def by auto

lemma map_assn_delete:
  "map_assn A m mh \<Longrightarrow>\<^sub>A
   map_assn A (m(k := None)) (mh(k := None)) * option_assn A (m k) (mh k)"
  unfolding map_assn_def
  apply sep_auto
  apply (sep_auto cong: multiset.map_cong_simp)
   apply (cases "m k"; cases "mh k"; simp)
     apply (auto; fail)+
   by (subst in_mset_dom_union_split, assumption+, sep_auto)

lemma [simp]:
  "z \<in># mset_set S \<longleftrightarrow> z \<in> S" if "finite S"
  using that by auto

lemma ent_refl':
  "a = b \<Longrightarrow> a \<Longrightarrow>\<^sub>A b"
  by auto

lemma map_assn_update_aux:
  "map_assn A m mh * A v vi \<Longrightarrow>\<^sub>A map_assn A (m(k \<mapsto> v)) (mh(k \<mapsto> vi))"
  if "k \<notin> dom m"
  unfolding map_assn_def
  apply (sep_auto simp: that cong: multiset.map_cong_simp)
  apply (subst mult.commute)
  apply (rule ent_star_mono)
   apply simp
  apply (rule ent_refl')
  apply (rule arg_cong[where f = "big_star"])
  apply (rule image_mset_cong)
  using that by auto

lemma map_assn_update:
  "map_assn A m mh * A v vi \<Longrightarrow>\<^sub>A
   map_assn A (m(k \<mapsto> v)) (mh(k \<mapsto> vi)) * true"
  apply (rule ent_frame_fwd[OF map_assn_delete[where k = k]], frame_inference)
  apply (rule ent_frame_fwd[OF map_assn_update_aux[where k = k and A = A], rotated], frame_inference)
  by (sep_auto simp del: map_upd_eq_restrict)+



(* TODO: Move to IICF, this is a generic pattern to enhance a map-implementation to
  heap-based values, a la Chargueraud *)

definition (in imp_map) "hms_assn A m mi \<equiv> \<exists>\<^sub>Amh. is_map mh mi * map_assn A m mh"

definition (in imp_map) "hms_assn' K A = hr_comp (hms_assn A) (\<langle>the_pure K, Id\<rangle>map_rel)"
declare (in imp_map) hms_assn'_def[symmetric, fcomp_norm_unfold]

definition (in imp_map_empty) [code_unfold]: "hms_empty \<equiv> empty"

lemma (in imp_map_empty) hms_empty_rule [sep_heap_rules]:
  "<emp> hms_empty <hms_assn A Map.empty>\<^sub>t"
  unfolding hms_empty_def hms_assn_def
  by (sep_auto eintros: exI[where x = Map.empty])

definition (in imp_map_update) [code_unfold]: "hms_update = update"

lemma (in imp_map_update) hms_update_rule [sep_heap_rules]:
  "<hms_assn A m mi * A v vi> hms_update k vi mi <hms_assn A (m(k \<mapsto> v))>\<^sub>t"
  unfolding hms_update_def hms_assn_def
  apply (sep_auto eintros del: exI)
  subgoal for mh mi
    apply (rule exI[where x = "mh(k \<mapsto> vi)"])
    apply (rule ent_frame_fwd[OF map_assn_update[where A = A]], frame_inference)
    by sep_auto
  done

lemma restrict_not_in_dom_simp[simp]:
  "m |` (- {k}) = m" if "m k = None"
  using that by (auto simp: restrict_map_def)

definition [code]:
  "hms_extract lookup delete k m =
    do {
      vo \<leftarrow> lookup k m;
      case vo of
        None \<Rightarrow> return (None, m) |
        Some v \<Rightarrow> do {
          m \<leftarrow> delete k m;
          return (Some v, m)
        }
    }
  "

locale imp_map_extract_derived = imp_map_delete + imp_map_lookup
begin

lemma [simp]:
  assumes "vassn_tag (map_assn A m mh)"
  shows "mh k = None \<longleftrightarrow> m k = None" "dom mh = dom m" "finite (dom m)"
  using assms unfolding map_assn_def vassn_tag_def by auto

lemma hms_extract_rule [sep_heap_rules]:
  "<hms_assn A m mi>
    hms_extract lookup delete k mi
  <\<lambda> (vi, mi'). option_assn A (m k) vi * hms_assn A (m(k := None)) mi'>\<^sub>t"
  unfolding hms_extract_def hms_assn_def
  apply (sep_auto eintros del: exI)
  subgoal
    unfolding map_assn_def by auto
  subgoal for mh
    apply (rule exI[where x = "mh(k := None)"])
    apply (rule fr_refl)
    apply (rule ent_star_mono, simp add: fun_upd_idem)
    apply (rule entails_preI, simp add: fun_upd_idem)
    done
  apply (sep_auto eintros del: exI)
  subgoal for mh
    apply (rule exI[where x = "mh(k := None)"])
    apply (rule ent_frame_fwd[OF map_assn_delete[where A = A]], frame_inference)
    by (sep_auto simp add: map_upd_eq_restrict)+
  done

end

context imp_map_update
begin

lemma hms_update_hnr:
  "(uncurry2 hms_update, uncurry2 (RETURN ooo op_map_update)) \<in>
  id_assn\<^sup>k *\<^sub>a A\<^sup>d *\<^sub>a (hms_assn A)\<^sup>d \<rightarrow>\<^sub>a hms_assn A"
  by sepref_to_hoare sep_auto

sepref_decl_impl update: hms_update_hnr uses op_map_update.fref[where V = Id] .

end

context imp_map_empty
begin

lemma hms_empty_hnr:
  "(uncurry0 hms_empty, uncurry0 (RETURN op_map_empty)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a hms_assn A"
  by sepref_to_hoare sep_auto

sepref_decl_impl (no_register) empty: hms_empty_hnr uses op_map_empty.fref[where V = Id] .
print_theorems
  thm empty_hnr
definition "op_hms_empty \<equiv> IICF_Map.op_map_empty"

  sublocale hms: map_custom_empty op_hms_empty
    by unfold_locales (simp add: op_hms_empty_def)
  (* lemmas [sepref_fr_rules] = hms_empty_hnr[folded op_hms_empty_def] *)

  lemmas [sepref_fr_rules] = empty_hnr[folded op_hms_empty_def]

  lemmas hms_fold_custom_empty = hms.fold_custom_empty

end

sepref_decl_op map_extract: "\<lambda>k m. (m k, m(k := None))" :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>V\<rangle>option_rel \<times>\<^sub>r \<langle>K,V\<rangle>map_rel"
  where "single_valued K" "single_valued (K\<inverse>)"
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
   apply (elim IntE)
   apply parametricity
  apply (elim IntE; rule IntI)
   apply parametricity
   apply (simp add: pres_eq_iff_svb; fail)
  by auto

context imp_map_extract_derived
begin

lemma hms_extract_hnr:
  "(uncurry (hms_extract lookup delete), uncurry (RETURN oo op_map_extract)) \<in>
  id_assn\<^sup>k *\<^sub>a (hms_assn A)\<^sup>d \<rightarrow>\<^sub>a prod_assn (option_assn A) (hms_assn A)"
  by sepref_to_hoare sep_auto

sepref_decl_impl "extract": hms_extract_hnr uses op_map_extract.fref[where V = Id] .

end

interpretation hms_hm: imp_map_extract_derived is_hashmap hm_delete hm_lookup by standard

end