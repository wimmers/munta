theory DBM_Operations_Impl_Refine
  imports
    DBM_Operations_Impl
    "~~/src/HOL/Library/IArray"
begin

section \<open>Refinement\<close>

instantiation DBMEntry :: (linordered_cancel_ab_monoid_add) zero
begin
  definition "0 = Le 0"
  instance ..
end

instance DBMEntry :: ("{countable}") countable
apply (rule countable_classI[of "(\<lambda>Le (a::'a) \<Rightarrow> to_nat (0::nat,a) | DBM.Lt a \<Rightarrow> to_nat (1::nat,a) | DBM.INF \<Rightarrow> to_nat (2::nat,undefined::'a) )"])
apply (simp split: DBMEntry.splits)
done

instance DBMEntry :: ("{heap}") heap ..

instance int :: linordered_cancel_ab_monoid_add by (standard; simp)

(* XXX Move *)
lemma [code]:
  "dbm_lt (Lt a) \<infinity> = True"
  "dbm_lt (Le a) \<infinity> = True"
  "dbm_lt (Le a) (Le b) = (a < b)"
  "dbm_lt (Le a) (Lt b) = (a < b)"
  "dbm_lt (Lt a) (Le b) = (a \<le> b)"
  "dbm_lt (Lt a) (Lt b) = (a < b)"
  "dbm_lt \<infinity> x = False"
by auto

definition dbm_subset' :: "nat \<Rightarrow> ('t :: {linorder, zero}) DBM' \<Rightarrow> 't DBM' \<Rightarrow> bool" where
  "dbm_subset' n M M' \<equiv> pointwise_cmp (op \<le>) n (curry M) (curry M')"

lemma dbm_subset'_alt_def:
  "dbm_subset' n M M' \<equiv>
    list_all (\<lambda> i. list_all (\<lambda> j. (op_mtx_get M (i, j) \<le> op_mtx_get M' (i, j))) [0..<Suc n]) [0..<Suc n]"
by (simp add: dbm_subset'_def pointwise_cmp_alt_def neutral)

lemma dbm_subset_alt_def'[code]:
  "dbm_subset n M M' =
    (list_ex (\<lambda> i. op_mtx_get M (i, i) < \<one>) [0..<Suc n] \<or>
    list_all (\<lambda> i. list_all (\<lambda> j. (op_mtx_get M (i, j) \<le> op_mtx_get M' (i, j))) [0..<Suc n]) [0..<Suc n])"
by (simp add: dbm_subset_def check_diag_alt_def pointwise_cmp_alt_def neutral)

context
  fixes n :: nat
begin

abbreviation "mtx_assn \<equiv> asmtx_assn (Suc n) id_assn"

(* declare param_upt[sepref_import_param] *)

lemma [sepref_import_param]: "(Le,Le) \<in> Id\<rightarrow>Id" by simp
lemmas Relation.IdI[where a = \<infinity>, sepref_import_param]
lemma [sepref_import_param]: "(op+,op+) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(uminus,uminus) \<in> (Id::(_*_)set)\<rightarrow>Id" by simp

term reset_canonical_upd

term "reset_canonical_upd :: int DBM' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int DBM'"

term "(uncurry2 (uncurry (\<lambda>x. RETURN ooo (reset_canonical_upd :: int DBM' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int DBM')x)))"

term "SYNTH (uncurry2 (uncurry (\<lambda>x. RETURN ooo (reset_canonical_upd :: int DBM' \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int DBM')x))) ([\<lambda>(((_,i),j),_). i\<le>n \<and> j\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn)"

term "[\<lambda>(((_,i),j),_). i\<le>n \<and> j\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn"

sepref_definition reset_canonical_upd_impl' is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo reset_canonical_upd x))" ::
  "[\<lambda>(((_,i),j),_). i\<le>n \<and> j\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding reset_canonical_upd_alt_def[abs_def] op_mtx_set_def[symmetric] by sepref

sepref_definition reset_canonical_upd_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo reset_canonical_upd x))" ::
  "[\<lambda>(((_,i),j),_). i\<le>n \<and> j\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding reset_canonical_upd_alt_def[abs_def] op_mtx_set_def[symmetric] by sepref

sepref_definition up_canonical_upd_impl is
  "uncurry (RETURN oo up_canonical_upd)" :: "[\<lambda>(_,i). i\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding up_canonical_upd_def[abs_def] op_mtx_set_def[symmetric] by sepref

(* XXX Which version is better for this constant? *)
(* lemmas [sepref_import_param] = Relation.IdI[of \<one>] *)
lemma [sepref_import_param]:
  "(Le 0, \<one>) \<in> Id"
unfolding neutral by simp

sepref_definition check_diag_impl' is
  "uncurry (RETURN oo check_diag)" ::
  "[\<lambda>(i, _). i\<le>n]\<^sub>a nat_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow> bool_assn"
unfolding check_diag_alt_def[abs_def] list_ex_foldli neutral[symmetric] by sepref

lemma [sepref_opt_simps]:
  "(x = True) = x"
by simp

sepref_definition dbm_subset'_impl is
  "uncurry2 (RETURN ooo dbm_subset')" ::
  "[\<lambda>((i, _), _). i\<le>n]\<^sub>a nat_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow> bool_assn"
unfolding dbm_subset'_alt_def[abs_def] list_all_foldli by sepref

sepref_register check_diag ::
  "nat \<Rightarrow> _ :: {linordered_cancel_ab_monoid_add,heap} DBMEntry i_mtx \<Rightarrow> bool"

sepref_register dbm_subset' ::
  "nat \<Rightarrow> 'a :: {linordered_cancel_ab_monoid_add,heap} DBMEntry i_mtx \<Rightarrow> 'a DBMEntry i_mtx \<Rightarrow> bool"

lemmas [sepref_fr_rules] = dbm_subset'_impl.refine check_diag_impl'.refine

sepref_definition dbm_subset_impl' is
  "uncurry2 (RETURN ooo dbm_subset)" ::
  "[\<lambda>((i, _), _). i\<le>n]\<^sub>a nat_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow> bool_assn"
unfolding dbm_subset_def[abs_def] dbm_subset'_def[symmetric] short_circuit_conv by sepref

context
  notes [id_rules] = itypeI[of n "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

sepref_definition dbm_subset_impl is
  "uncurry (RETURN oo dbm_subset n)" :: "mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
unfolding dbm_subset_def[abs_def] dbm_subset'_def[symmetric] short_circuit_conv by sepref

sepref_definition check_diag_impl is
  "RETURN o check_diag n" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
unfolding check_diag_alt_def[abs_def] list_ex_foldli neutral[symmetric] by sepref

end

abbreviation "clock_assn \<equiv> pure (nbn_rel (Suc n))"

definition zero_clock :: nat where
  "zero_clock = 0"

sepref_register zero_clock

lemma [sepref_import_param]:
  "(zero_clock, zero_clock) \<in> nbn_rel (Suc n)"
unfolding zero_clock_def by auto

lemma [sepref_import_param]: "(Lt,Lt) \<in> Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(Le,Le) \<in> Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(\<infinity>,\<infinity>) \<in> Id" by simp
lemma [sepref_import_param]: "(Le,Le) \<in> Id\<rightarrow>Id" by simp

lemma [sepref_import_param]: "(min :: _ DBMEntry \<Rightarrow> _, min) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

lemmas [sepref_opt_simps] = zero_clock_def


sepref_definition abstra_upd_impl is
  "uncurry (RETURN oo abstra_upd)" ::
  "(acconstraint_assn clock_assn id_assn)\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
  unfolding abstra_upd_alt_def[abs_def] zero_clock_def[symmetric]
using [[goals_limit = 1]] by sepref

sepref_register abstra_upd ::
  "(nat, ('a :: {linordered_cancel_ab_monoid_add,uminus,heap})) acconstraint \<Rightarrow> 'a DBMEntry i_mtx \<Rightarrow> 'a DBMEntry i_mtx"

lemmas [sepref_fr_rules] = abstra_upd_impl.refine

sepref_definition abstr_upd_impl is
  "uncurry (RETURN oo abstr_upd)" :: "(list_assn (acconstraint_assn clock_assn id_assn))\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
  unfolding abstr_upd_alt_def by sepref

lemma [sepref_import_param]: "(norm_lower, norm_lower) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(norm_upper, norm_upper) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp

definition zero_clock2 :: "_ :: linordered_cancel_ab_monoid_add" where
  "zero_clock2 = 0"

sepref_register zero_clock2

lemma [sepref_import_param]: "(zero_clock2, zero_clock2) \<in> Id" by simp
lemma [sepref_import_param]: "(Suc, Suc) \<in> Id \<rightarrow> Id" by simp

abbreviation
  "iarray_assn x y \<equiv> pure (br IArray (\<lambda>_. True)) y x"

lemma [sepref_fr_rules]:
  "(uncurry (return oo IArray.sub), uncurry (RETURN oo op_list_get))
  \<in> iarray_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
unfolding br_def by sepref_to_hoare sep_auto

lemmas [sepref_opt_simps] = zero_clock2_def

sepref_definition norm_upd_impl is
  "uncurry2 (RETURN ooo norm_upd)" ::
   "[\<lambda>((_, xs), i). length xs > n \<and> i\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a iarray_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding norm_upd_def[abs_def] norm_upd_line_def zero_clock2_def[symmetric]
by sepref

sepref_definition norm_upd_impl' is
  "uncurry2 (RETURN ooo norm_upd)" ::
   "[\<lambda>((_, xs), i). length xs > n \<and> i\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a (list_assn id_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding norm_upd_def[abs_def] norm_upd_line_def zero_clock2_def[symmetric] by sepref

export_code abstr_upd_impl in SML_imp

export_code abstra_upd_impl in SML_imp

export_code dbm_subset_impl in SML_imp

(* XXX This fails. Why? *)
(* export_code norm_upd_impl in SML *)

end

export_code reset_canonical_upd_impl checking SML

export_code up_canonical_upd_impl checking SML

export_code dbm_subset_impl checking SML

code_thms dbm_subset

(*
code_pred dbm_lt .
code_thms dbm_lt
*)

(* lemmas dbm_lt.simps[code] *)

lemma [code]:
  "dbm_le a b = (a = b \<or> (a \<prec> b))"
unfolding dbm_le_def by auto

export_code dbm_subset checking SML

export_code dbm_subset in SML

end