theory Unreachability_TA_Misc
  imports
    TA_Impl.Normalized_Zone_Semantics_Impl_Semantic_Refinement
    Collections.Refine_Dflt_ICF
    Unreachability_Misc
begin

paragraph \<open>Misc TA\<close>

context TA_Start
begin

(* XXX This is in Normalized_Zone_Semantics_Impl but in the wrong context *)
lemma V_I:
  assumes "\<forall> i \<in> {1..<Suc n}. M 0 i \<le> 0"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> V"
  unfolding V_def DBM_zone_repr_def
proof (safe, goal_cases)
  case prems: (1 u i)
  then have "v i = i"
    using X_alt_def X_def triv_numbering by blast
  with prems have "v i > 0" "v i \<le> n" by auto
  with prems have "dbm_entry_val u None (Some i) (M 0 (v i))"
    unfolding DBM_val_bounded_def by auto
  moreover from assms \<open>v i > 0\<close> \<open>v i \<le> n\<close> have "M 0 (v i) \<le> 0" by auto
  ultimately
  show ?case
    apply (cases "M 0 (v i)")
    unfolding neutral less_eq dbm_le_def
    by (auto elim!: dbm_lt.cases simp: \<open>v i = i\<close>)
qed

end

paragraph \<open>Persisting imperative data structures\<close>

lemmas amtx_copy_hnr = amtx_copy_hnr[unfolded op_mtx_copy_def, folded COPY_def[abs_def]]

lemma lso_op_set_is_empty_hnr[sepref_fr_rules]:
  "(return o (\<lambda>xs. xs = []), RETURN o op_set_is_empty) \<in> (lso_assn AA)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding lso_assn_def hr_comp_def br_def by sepref_to_hoare sep_auto

context
  fixes n :: nat
begin

qualified definition
  "dbm_tab M \<equiv> \<lambda> (i, j). if i \<le> n \<and> j \<le> n then M ! ((n + 1) * i + j) else 0"

private lemma
  shows mtx_nonzero_dbm_tab_1: "(a, b) \<in> mtx_nonzero (dbm_tab M) \<Longrightarrow> a < Suc n"
    and mtx_nonzero_dbm_tab_2: "(a, b) \<in> mtx_nonzero (dbm_tab M) \<Longrightarrow> b < Suc n"
  unfolding mtx_nonzero_def dbm_tab_def by (auto split: if_split_asm)

definition
  "list_to_dbm M = op_amtx_new (Suc n) (Suc n) (dbm_tab M)"

lemma [sepref_fr_rules]:
  "(return o dbm_tab, RETURN o PR_CONST dbm_tab) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
  by sepref_to_hoare sep_auto

lemmas [sepref_opt_simps] = dbm_tab_def

sepref_register dbm_tab

sepref_definition list_to_dbm_impl
  is "RETURN o PR_CONST list_to_dbm" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
  supply mtx_nonzero_dbm_tab_1[simp] mtx_nonzero_dbm_tab_2[simp]
  unfolding PR_CONST_def list_to_dbm_def by sepref

lemma the_pure_Id:
  "the_pure (\<lambda>a c. \<up> (c = a)) = Id"
  by (subst is_pure_the_pure_id_eq) (auto simp: pure_def intro: is_pureI)

lemma of_list_list_to_dbm:
  "(Array.of_list, (RETURN \<circ>\<circ> PR_CONST) list_to_dbm)
  \<in> [\<lambda>a. length a = Suc n * Suc n]\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn n"
  apply sepref_to_hoare
  apply sep_auto
  unfolding amtx_assn_def hr_comp_def IICF_Array_Matrix.is_amtx_def
  apply (sep_auto eintros del: exI)
  subgoal for xs p
    apply (rule exI[where x = "list_to_dbm xs"])
    apply (rule exI[where x = xs])
    apply (sep_auto simp: list_to_dbm_def dbm_tab_def the_pure_Id)
     apply (simp add: algebra_simps; fail)
    apply sep_auto
    done
  done

end

definition
  "array_freeze a = do {xs \<leftarrow> Array.freeze a; Heap_Monad.return (IArray xs)}"

definition
  "array_unfreeze a = Array.of_list (IArray.list_of a)"

definition
  "iarray_mtx_rel n m c a \<equiv>
    IArray.length a = n * m
  \<and> (\<forall>i<n.\<forall>j<m. c (i, j) = IArray.sub a (i * m + j))
  \<and> (\<forall>i j. i \<ge> n \<or> j \<ge> m \<longrightarrow> c (i, j) = 0)"

lemma iarray_mtx_rel_is_amtx:
  "x \<mapsto>\<^sub>a IArray.list_of a \<Longrightarrow>\<^sub>A IICF_Array_Matrix.is_amtx n m c x" if "iarray_mtx_rel n m c a"
  using that unfolding is_amtx_def iarray_mtx_rel_def by simp solve_entails

lemma array_unfreeze_ht:
  "<emp> array_unfreeze a <amtx_assn n m id_assn c>" if "iarray_mtx_rel n m c a"
  using that unfolding array_unfreeze_def amtx_assn_def by (sep_auto intro: iarray_mtx_rel_is_amtx)

lemma array_freeze_ht:
  "<amtx_assn n m id_assn c a> array_freeze a <\<lambda>a. \<up>(iarray_mtx_rel n m c a)>\<^sub>t"
  unfolding array_freeze_def amtx_assn_def iarray_mtx_rel_def is_amtx_def
  by (sep_auto intro: iarray_mtx_rel_is_amtx)


datatype ('a, 'b) frozen_hm =
  Frozen_Hash_Map (array_of_hm: "('a, 'b) list_map iarray") (size_of_hm: nat)

definition diff_array_freeze :: "'a array \<Rightarrow> 'a iarray" where
  "diff_array_freeze a = IArray (list_of_array a)"

definition hm_freeze where
  "hm_freeze \<equiv> \<lambda>hm. case hm of Impl_Array_Hash_Map.HashMap a _
    \<Rightarrow> Frozen_Hash_Map (diff_array_freeze a) (array_length a)"

definition frozen_hm_lookup where
  "frozen_hm_lookup \<equiv> \<lambda>key hm.
    case hm of Frozen_Hash_Map a n \<Rightarrow>
      let
        code = bounded_hashcode_nat n key;
        bucket = IArray.sub a code
      in
        list_map_lookup (=) key bucket
  "

lemma list_of_array_nth:
  "list_of_array a ! n = array_get a n"
  by (cases a) simp

lemma frozen_hm_lookup_hm_freeze:
  "frozen_hm_lookup k (hm_freeze m) = Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k m"
proof -
  obtain a n where "m = Impl_Array_Hash_Map.HashMap a n"
    by (cases m) auto
  have "IArray.sub (diff_array_freeze a) i = array_get a i" for i
    unfolding diff_array_freeze_def by (simp add: list_of_array_nth)
  then show ?thesis
    unfolding frozen_hm_lookup_def \<open>m = _\<close> hm_freeze_def by simp
qed

context
  fixes M :: "('a :: hashable * 'b) list"
begin

definition "map_of_list = fold (\<lambda>(k, v) a. a(k \<mapsto> v)) M Map.empty"

lemma [autoref_rules]:
  "(M, M) \<in> \<langle>Id \<times>\<^sub>r Id\<rangle>list_rel"
  by simp

schematic_goal M_impl:
  "(?M::?'c, map_of_list:::\<^sub>r\<langle>Id,Id\<rangle>dflt_ahm_rel) \<in> ?R"
  unfolding map_of_list_def
  apply (autoref (trace))
  done

concrete_definition hashmap_of_list uses M_impl

definition
  "frozen_hm_of_list \<equiv> hm_freeze hashmap_of_list"

theorem hashmap_of_list_lookup:
  "(\<lambda>k. Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k hashmap_of_list, map_of_list)
  \<in> Id \<rightarrow> \<langle>Id\<rangle>option_rel" (is "(\<lambda>k. ?f k hashmap_of_list, _) \<in> ?R")
proof -
  have *: "(?f, Intf_Map.op_map_lookup) \<in> Id \<rightarrow> ahm_map_rel' bounded_hashcode_nat \<rightarrow> Id"
    using Impl_Array_Hash_Map.ahm_lookup_impl[OF hashable_bhc_is_bhc] by simp
  { fix k :: 'a
    have "abstract_bounded_hashcode Id bounded_hashcode_nat = bounded_hashcode_nat"
      unfolding abstract_bounded_hashcode_def by (intro ext) auto
    from hashmap_of_list.refine obtain hm where
      "(hashmap_of_list, hm) \<in> \<langle>Id, Id\<rangle>ahm_map_rel"
      "(hm, map_of_list) \<in> ahm_map_rel' bounded_hashcode_nat"
      unfolding ahm_rel_def by (clarsimp simp: \<open>_ = bounded_hashcode_nat\<close>)
    with * have "?f k hm = Intf_Map.op_map_lookup k map_of_list"
      by (auto dest!: fun_relD)
    with \<open>(hashmap_of_list, hm) \<in> _\<close> have "?f k hashmap_of_list = map_of_list k"
      unfolding ahm_map_rel_def array_rel_def by clarsimp
  }
  then show ?thesis
    by simp
qed

theorem frozen_hm_of_list_lookup:
  "(\<lambda>k. frozen_hm_lookup k frozen_hm_of_list, map_of_list) \<in> Id \<rightarrow> \<langle>Id\<rangle>option_rel"
  using hashmap_of_list_lookup unfolding frozen_hm_of_list_def
  by (simp add: frozen_hm_lookup_hm_freeze)

end

definition
  "array_all2 n P as bs \<equiv> \<forall>i < n. P (IArray.sub as i) (IArray.sub bs i)"

lemma iarray_mtx_relD:
  assumes "iarray_mtx_rel n m M a" "i < n" "j < m"
  shows "M (i, j) = IArray.sub a (i * m + j)"
  using assms unfolding iarray_mtx_rel_def by auto

lemma array_all2_iff_pointwise_cmp:
  assumes "iarray_mtx_rel (Suc n) (Suc n) M a" "iarray_mtx_rel (Suc n) (Suc n) M' b"
  shows "array_all2 (Suc n * Suc n) P a b \<longleftrightarrow> pointwise_cmp P n (curry M) (curry M')"
proof -
  have *: \<open>i + i * n + j < Suc (n + (n + n * n))\<close> if \<open>i \<le> n\<close> and \<open>j \<le> n\<close> for i j :: \<open>nat\<close>
    using that by (simp add: algebra_simps) (intro le_imp_less_Suc add_mono; simp)
  have **: "\<exists>i \<le> n. \<exists>j \<le> n. k = i + i * n + j" if "k < Suc n * Suc n" for k
    apply (inst_existentials "k div Suc n" "k mod Suc n")
    subgoal
      by (meson less_Suc_eq_le less_mult_imp_div_less that)
    subgoal
      by simp
    subgoal
      by (metis div_mod_decomp mult_Suc_right)
    done
  from assms show ?thesis
    unfolding pointwise_cmp_def array_all2_def
    by (auto dest: *[simplified] **[simplified] simp: iarray_mtx_relD)
qed

paragraph \<open>Unsorted\<close>

lemma fold_generalize_start:
  assumes "\<And>a. P a \<Longrightarrow> Q (fold g xs a)" "P a"
  shows "Q (fold g xs a)"
  using assms by auto

end