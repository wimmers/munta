theory Liveness_Subsumption_Impl
  imports Liveness_Subsumption_Map Heap_Hash_Map
begin

locale Liveness_Search_Space_Key_Impl_Defs =
  Liveness_Search_Space_Key_Defs _ _ _ _ _ _ key for key :: "'a \<Rightarrow> 'ki :: {hashable, heap}" +
  fixes A :: "'a \<Rightarrow> ('ai :: heap) \<Rightarrow> assn"
  fixes succsi :: "'ai \<Rightarrow> 'ai list Heap"
  fixes a\<^sub>0i :: "'ai Heap"
  fixes Lei :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"
  fixes keyi :: "'ai \<Rightarrow> 'ki Heap"
  fixes copyi :: "'ai \<Rightarrow> 'ai Heap"

locale Liveness_Search_Space_Key_Impl =
  Liveness_Search_Space_Key_Impl_Defs +
  Liveness_Search_Space_Key +
  assumes refinements[sepref_fr_rules]:
    "(uncurry0 a\<^sub>0i, uncurry0 (RETURN (PR_CONST a\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"
    "(uncurry Lei,uncurry (RETURN oo PR_CONST op \<unlhd>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    "(succsi,RETURN o PR_CONST succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A"
    "(keyi,RETURN o PR_CONST key) \<in> A\<^sup>k \<rightarrow>\<^sub>a id_assn"
    "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"

context Liveness_Search_Space_Key_Defs
begin

(* XXX The lemma has this form to avoid unwanted eta-expansions.
  The eta-expansions arise from the type of 'insert_map_set v S' *)
lemma insert_map_set_alt_def: "(None, insert_map_set v S) = (
  let
    k = key v; (S', S) = op_map_extract k S
  in
    case S' of
      Some S1 \<Rightarrow> (None, S(k \<mapsto> (insert v S1)))
    | None \<Rightarrow> (None, S(k \<mapsto> {v}))
)
"
  unfolding insert_map_set_def op_map_extract_def by (auto simp: Let_def split: option.split)

lemma check_subsumption_map_set_alt_def: "check_subsumption_map_set v S = (
  let
    k = key v; (S', S) = op_map_extract k S;
    S1' = (case S' of Some S1 \<Rightarrow> S1 | None \<Rightarrow> {})
  in (\<exists> x \<in> S1'. v \<unlhd> x)
)
"
  unfolding check_subsumption_map_set_def op_map_extract_def by (auto simp: Let_def)

lemma check_subsumption_map_set_extract: "(S, check_subsumption_map_set v S) = (
  let
    k = key v; (S', S) = op_map_extract k S
  in (
    case S' of
      Some S1 \<Rightarrow> (let r = (\<exists> x \<in> S1. v \<unlhd> x) in (op_map_update k S1 S, r))
    | None \<Rightarrow> (S, False)
  )
)
"
  unfolding check_subsumption_map_set_def op_map_extract_def op_map_update_def op_map_delete_def
  by (auto simp: Let_def split: option.split)

lemma check_subsumption_map_list_extract: "(S, check_subsumption_map_list v S) = (
  let
    k = key v; (S', S) = op_map_extract k S
  in (
    case S' of
      Some S1 \<Rightarrow> (let r = (\<exists> x \<in> set S1. x \<unlhd> v) in (op_map_update k S1 S, r))
    | None \<Rightarrow> (S, False)
  )
)
"
  unfolding check_subsumption_map_list_def op_map_extract_def op_map_update_def op_map_delete_def
  by (auto simp: Let_def split: option.split)

lemma push_map_list_alt_def: "(None, push_map_list v S) = (
  let
    k = key v; (S', S) = op_map_extract k S
  in
    case S' of
      Some S1 \<Rightarrow> (None, S(k \<mapsto> v # S1))
    | None \<Rightarrow> (None, S(k \<mapsto> [v]))
)
"
  unfolding push_map_list_def op_map_extract_def by (auto simp: Let_def split: option.split)

(* XXX The check for emptiness is superfluous if we thread through the pre-condition *)
lemma pop_map_list_alt_def: "(None, pop_map_list v S) = (
  let
    k = key v; (S', S) = op_map_extract k S
  in
    case S' of
      Some S1 \<Rightarrow> (None, S(k \<mapsto> if op_list_is_empty S1 then [] else tl S1))
    | None \<Rightarrow> (None, S(k \<mapsto> []))
)
"
  unfolding pop_map_list_def op_map_extract_def by (auto simp: Let_def split: option.split)

lemmas alt_defs =
  insert_map_set_alt_def check_subsumption_map_set_extract
  check_subsumption_map_list_extract pop_map_list_alt_def push_map_list_alt_def

lemma dfs_map_alt_def:
  "dfs_map = (\<lambda> P. do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      let (ST, b) = (ST, check_subsumption_map_list v ST) in
      if b then RETURN (P, ST, True)
      else do {
        let (P, b1) = (P, check_subsumption_map_set v P) in
        if b1 then
          RETURN (P, ST, False)
        else do {
            let (_, ST1) = (None, push_map_list (COPY v) ST);
            (P1, ST2, r) \<leftarrow>
              nfoldli (succs v) (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST1,False);
            let (_, ST') = (None, pop_map_list (COPY v) ST2);
            let (_, P') = (None, insert_map_set (COPY v) P1);
            RETURN (P', ST', r)
          }
      }
    ) (P,Map.empty,a\<^sub>0);
    RETURN (r, P)
  })"
  unfolding dfs_map_def
  unfolding Let_def
  unfolding COPY_def
  by auto

definition dfs_map' where
  "dfs_map' a P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      let (ST, b) = (ST, check_subsumption_map_list v ST) in
      if b then RETURN (P, ST, True)
      else do {
        let (P, b1) = (P, check_subsumption_map_set v P) in
        if b1 then
          RETURN (P, ST, False)
        else do {
            let (_, ST1) = (None :: 'v option, push_map_list (COPY v) ST);
            (P1, ST2, r) \<leftarrow>
              nfoldli (succs v) (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST1,False);
            let (_, ST') = (None :: 'v option, pop_map_list (COPY v) ST2);
            let (_, P') = (None :: 'v option, insert_map_set (COPY v) P1);
            RETURN (P', ST', r)
          }
      }
    ) (P,Map.empty,a);
    RETURN (r, P)
  }"

lemma dfs_map'_id:
  "dfs_map' a\<^sub>0 = dfs_map"
  apply (subst dfs_map_alt_def)
  unfolding dfs_map'_def ..

end (* Search Space Nodes Empty Key Impl Defs 1 *)

definition (in imp_map_delete) [code_unfold]: "hms_delete = delete"

lemma (in imp_map_delete) hms_delete_rule [sep_heap_rules]:
  "<hms_assn A m mi> hms_delete k mi <hms_assn A (m(k := None))>\<^sub>t"
  unfolding hms_delete_def hms_assn_def
  apply (sep_auto eintros del: exI)
  subgoal for mh
    apply (rule exI[where x = "mh(k := None)"])
    apply (rule ent_frame_fwd[OF map_assn_delete[where A = A]], frame_inference)
    by sep_auto
  done

context imp_map_delete
begin

lemma hms_delete_hnr:
  "(uncurry hms_delete, uncurry (RETURN oo op_map_delete)) \<in>
  id_assn\<^sup>k *\<^sub>a (hms_assn A)\<^sup>d \<rightarrow>\<^sub>a hms_assn A"
  by sepref_to_hoare sep_auto

sepref_decl_impl delete: hms_delete_hnr uses op_map_delete.fref[where V = Id] .

end

lemma fold_insert_set:
  "fold insert xs S = set xs \<union> S"
  by (induction xs arbitrary: S) auto

lemma set_alt_def:
  "set xs = fold insert xs {}"
  by (simp add: fold_insert_set)

(* XXX Duplication *)
lemma list_ex_foldli:
  "list_ex P xs = foldli xs Not (\<lambda> x y. P x \<or> y) False"
 apply (induction xs)
 apply (simp; fail)
 subgoal for x xs
  apply simp
  apply (induction xs)
 by auto
 done

context Liveness_Search_Space_Key_Impl
begin

sepref_register
  "PR_CONST a\<^sub>0" "PR_CONST op \<unlhd>" "PR_CONST succs" "PR_CONST key"

lemma [def_pat_rules]:
  "a\<^sub>0 \<equiv> UNPROTECT a\<^sub>0" "op \<unlhd> \<equiv> UNPROTECT op \<unlhd>" "succs \<equiv> UNPROTECT succs" "key \<equiv> UNPROTECT key"
  by simp_all

abbreviation "passed_assn \<equiv> hm.hms_assn' id_assn (lso_assn A)"

(* This is to make the pre-processing phase pick the right type for the input *)
lemma [intf_of_assn]:
  "intf_of_assn (hm.hms_assn' a b) TYPE(('aa, 'bb) i_map)"
  by simp

sepref_definition dfs_map_impl is
  "PR_CONST dfs_map" :: "passed_assn\<^sup>d \<rightarrow>\<^sub>a prod_assn bool_assn passed_assn"
  unfolding PR_CONST_def
  apply (subst dfs_map_alt_def)
  unfolding alt_defs
  unfolding Bex_set list_ex_foldli
  unfolding fold_lso_bex
  unfolding lso_fold_custom_empty hm.hms_fold_custom_empty HOL_list.fold_custom_empty
  by sepref

sepref_register dfs_map

lemmas [sepref_fr_rules] = dfs_map_impl.refine_raw

lemma passed_empty_refine[sepref_fr_rules]:
  "(uncurry0 hm.hms_empty, uncurry0 (RETURN (PR_CONST hm.op_hms_empty))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a passed_assn"
  by (rule hfrefI, auto simp: pure_unit_rel_eq_empty intro!: sepref_fr_rules(13)[simplified])

sepref_register hm.op_hms_empty

sepref_thm dfs_map_impl' is
  "uncurry0 (do {(r, p) \<leftarrow> dfs_map Map.empty; RETURN r})" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding hm.hms_fold_custom_empty by sepref

sepref_definition dfs_map'_impl is
  "uncurry dfs_map'"
  :: "A\<^sup>d *\<^sub>a (hm.hms_assn' id_assn (lso_assn A))\<^sup>d \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a hm.hms_assn' id_assn (lso_assn A)"
  unfolding dfs_map'_def
  unfolding PR_CONST_def
  unfolding alt_defs
  unfolding Bex_set list_ex_foldli
  unfolding fold_lso_bex
  unfolding lso_fold_custom_empty hm.hms_fold_custom_empty HOL_list.fold_custom_empty
  by sepref

concrete_definition (in -) dfs_map_impl'
  uses Liveness_Search_Space_Key_Impl.dfs_map_impl'.refine_raw is "(uncurry0 ?f,_)\<in>_"

lemma (in Liveness_Search_Space_Key) dfs_map_empty:
  "dfs_map Map.empty \<le> \<Down> (bool_rel \<times>\<^sub>r map_set_rel) dfs_spec" if "V a\<^sub>0"
proof -
  (* XXX Make lemma *)
  have "liveness_compatible {}"
    unfolding liveness_compatible_def by auto
  have "(Map.empty, {}) \<in> map_set_rel"
    unfolding map_set_rel_def by auto
  note dfs_map_dfs_refine[OF this \<open>V a\<^sub>0\<close>]
  also note dfs_correct[OF \<open>V a\<^sub>0\<close> \<open>liveness_compatible {}\<close>]
  finally show ?thesis
    by auto
qed

lemma (in Liveness_Search_Space_Key) dfs_map_empty_correct:
  "do {(r, p) \<leftarrow> dfs_map Map.empty; RETURN r} \<le> SPEC (\<lambda> r. r \<longleftrightarrow> (\<exists> x. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x))"
  if "V a\<^sub>0"
  supply dfs_map_empty[OF \<open>V a\<^sub>0\<close>, THEN order.trans, refine_vcg]
  apply refine_vcg
  unfolding dfs_spec_def pw_le_iff by (auto simp: refine_pw_simps)

lemma dfs_map_impl'_hnr:
  "(uncurry0 (dfs_map_impl' TYPE('f) TYPE('g) TYPE('h) succsi a\<^sub>0i Lei keyi copyi),
    uncurry0 (SPEC (\<lambda>r. r = (\<exists>x. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x)))
   ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn" if "V a\<^sub>0"
  using
    dfs_map_impl'.refine[
      OF Liveness_Search_Space_Key_Impl_axioms,
      FCOMP dfs_map_empty_correct[THEN Id_SPEC_refine, THEN nres_relI],
      OF \<open>V a\<^sub>0\<close>
      ] .

lemma dfs_map_impl'_hoare_triple:
  "<\<up>(V a\<^sub>0)> 
    dfs_map_impl' TYPE('f) TYPE('g) TYPE('h) succsi a\<^sub>0i Lei keyi copyi 
  <\<lambda>r. \<up>(r \<longleftrightarrow> (\<exists> x. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x))>\<^sub>t"
  using dfs_map_impl'_hnr[to_hnr]
  unfolding hn_refine_def
  apply clarsimp
  apply (erule cons_post_rule)
  by (sep_auto simp: pure_def)
      
end (* Liveness Search Space Key Impl *)




end (* Theory *)