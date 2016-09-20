theory FW_Code
  imports "../IRF/Refine_Imperative_HOL/IICF/IICF"
          "../IRF/Refine_Imperative_HOL/IICF/Impl/IICF_Array_Sqmatrix"
          Floyd_Warshall
          Refine_More
begin

definition fw_upd' :: "('a::linordered_ab_monoid_add) mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mtx nres" where
  "fw_upd' m k i j =
  RETURN (op_mtx_set m (i, j) (min (op_mtx_get m (i, j)) (op_mtx_get m (i, k) + op_mtx_get m (k, j))))"

definition fw' ::  "('a::linordered_ab_monoid_add) mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mtx nres" where
  "fw' m n k i j = RECT (\<lambda> fw (m, k, i, j).
      case (k, i, j) of
        (0, 0, 0) \<Rightarrow> fw_upd' m 0 0 0 |
        (Suc k, 0, 0) \<Rightarrow> do {m' \<leftarrow> fw (m, k, n, n); fw_upd' m' (Suc k) 0 0} |
        (k, Suc i, 0) \<Rightarrow> do {m' \<leftarrow> fw (m, k, i, n); fw_upd' m' k (Suc i) 0} |
        (k, i, Suc j) \<Rightarrow> do {m' \<leftarrow> fw (m, k, i, j); fw_upd' m' k i (Suc j)}
    ) (m, k, i, j)"

lemma fw'_simps:
  "fw' m n 0       0       0        = fw_upd' m 0 0 0"
  "fw' m n (Suc k) 0       0        = do {m' \<leftarrow> fw' m n k n n; fw_upd' m' (Suc k) 0 0}"
  "fw' m n k       (Suc i) 0        = do {m' \<leftarrow> fw' m n k i n; fw_upd' m' k (Suc i) 0}"
  "fw' m n k       i       (Suc j)  = do {m' \<leftarrow> fw' m n k i j; fw_upd' m' k i (Suc j)}"
unfolding fw'_def by (subst RECT_unfold, (refine_mono; fail), (auto split: nat.split; fail))+

lemma
  "fw' m n k i j \<le> SPEC (\<lambda> r. r = uncurry (fw (curry m) n k i j))"
by (induction "curry m" n k i j arbitrary: m rule: fw.induct)
   (fastforce simp add: fw_upd'_def fw_upd_def upd_def fw'_simps pw_le_iff refine_pw_simps)+

lemma fw_upd'_spec:
  "fw_upd' M k i j \<le> SPEC (\<lambda> M'. M' = uncurry (fw_upd (curry M) k i j))"
by (auto simp: fw_upd'_def fw_upd_def upd_def pw_le_iff refine_pw_simps)

lemma for_rec3_fw:
  "for_rec3 fw_upd' M n i j k \<le> SPEC (\<lambda> M'. M' = uncurry (fw (curry M) n i j k))"
using fw_upd'_spec
by (induction "fw_upd' :: (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> _" M n i j k rule: for_rec3.induct)
   (fastforce simp: pw_le_iff refine_pw_simps)+


context
  fixes n :: nat
  fixes dummy :: "'a::{linordered_ab_monoid_add,zero,heap}"
begin

lemma [sepref_import_param]: "(op+,op+::'a\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp
lemma [sepref_import_param]: "(min,min::'a\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

abbreviation "node_assn \<equiv> nat_assn"
abbreviation "mtx_assn \<equiv> asmtx_assn (Suc n) id_assn::('a mtx \<Rightarrow>_)"

sepref_definition fw_upd_impl is
  "uncurry2 (uncurry fw_upd')" ::
  "[\<lambda> (((_,k),i),j). k \<le> n \<and> i \<le> n \<and> j \<le> n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a node_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding fw_upd'_def[abs_def] by sepref_keep

declare fw_upd_impl.refine[sepref_fr_rules]

sepref_register fw_upd' :: "'a i_mtx \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a i_mtx nres"

definition
  "fw_impl' (M :: 'a mtx) = for_rec3 fw_upd' M n n n n"

lemma [sepref_fr_rules]:
  "(uncurry0 (return n), uncurry0 (RETURN n)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a node_assn"
by (sep_auto intro!: hfrefI hn_refineI simp: pure_def)

sepref_register n

declare imp_nfoldli_def[sepref_opt_simps del]
sepref_definition fw_impl is
  "fw_impl'" :: "mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
unfolding fw_impl'_def[abs_def] for_rec3_eq
 apply (subst (1) nfoldli_assert'[symmetric])
 apply (subst (1) nfoldli_assert'[symmetric])
 apply (subst (1) nfoldli_assert'[symmetric])
 apply sepref_keep
done

thm sepref_opt_simps TrueI sepref_opt_simps2

print_theorems

end

export_code fw_impl in SML_imp
thm fw_impl.refine

definition fw_spec where
  "fw_spec n M \<equiv> SPEC (\<lambda> M'. 
    if (\<exists> i \<le> n. M' i i < \<one>)
    then \<not> cycle_free M n
    else \<forall>i \<le> n. \<forall>j \<le> n. M' i j = D M i j n \<and> cycle_free M n)"

lemma D_diag_nonnegI:
  assumes "cycle_free M n" "i \<le> n"
  shows "D M i i n \<ge> \<one>"
using assms D_dest''[OF refl, of M i i n] unfolding cycle_free_def by auto

lemma fw_fw_spec:
  "RETURN (fw M n n n n) \<le> fw_spec n M"
unfolding fw_spec_def
proof (simp, safe, goal_cases)
  case prems: (1 i)
  with fw_shortest_path[OF prems(3)] D_diag_nonnegI show ?case by fastforce
next
  case 2 then show ?case using FW_neg_cycle_detect by (force intro: fw_shortest_path[symmetric])
next
  case 3 then show ?case using FW_neg_cycle_detect by blast
qed

definition
  "mat_curry_rel = {(Mu, Mc). curry Mu = Mc}"

definition
  "mtx_curry_assn n = hr_comp (mtx_assn n) (br curry (\<lambda>_. True))"

declare mtx_curry_assn_def[symmetric, fcomp_norm_unfold]

lemma fw_impl'_correct:
  "(fw_impl', fw_spec) \<in> Id \<rightarrow> br curry (\<lambda> _. True) \<rightarrow> \<langle>br curry (\<lambda> _. True)\<rangle> nres_rel"
unfolding fw_impl'_def[abs_def] using for_rec3_fw fw_fw_spec
by (fastforce simp: in_br_conv pw_le_iff refine_pw_simps intro!: nres_relI)

theorem fw_impl_correct:
  "(fw_impl n, fw_spec n) \<in> (mtx_curry_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_curry_assn n"
using fw_impl.refine[FCOMP fw_impl'_correct[THEN fun_relD, OF IdI]] .

corollary
  "<mtx_curry_assn n M Mi> fw_impl n Mi <\<lambda> Mi'. \<exists>\<^sub>A M'. mtx_curry_assn n M' Mi' * \<up>
    (if (\<exists> i \<le> n. M' i i < \<one>)
    then \<not> cycle_free M n
    else \<forall>i \<le> n. \<forall>j \<le> n. M' i j = D M i j n \<and> cycle_free M n)>\<^sub>t"
by (rule cons_rule[OF _ _ fw_impl_correct[THEN hfrefD, THEN hn_refineD]]) (sep_auto simp: fw_spec_def)+

thm fw_impl'_def

abbreviation "FW m n \<equiv> fw m n n n n"

definition "FW' = uncurry oo FW o curry"

definition "FW'' n M = FW' M n"

term swap

lemma fw_impl'_refine_FW'':
  "(fw_impl' n, RETURN o PR_CONST (FW'' n)) \<in> Id \<rightarrow> \<langle>Id\<rangle> nres_rel"
unfolding fw_impl'_def[abs_def] FW''_def[abs_def] FW'_def using for_rec3_fw
by (force simp: pw_le_iff pw_nres_rel_iff refine_pw_simps)

end