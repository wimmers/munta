theory DBM_Operations_Impl_Refine
  imports
    DBM_Operations_Impl
    Sepref_Acconstraint
    "HOL-Library.IArray"
    TA_Library.Imperative_Loops
begin

lemma the_pure_id_assn_eq[simp]:
  "the_pure (\<lambda>a c. \<up> (c = a)) = Id"
proof -
  have *: "(\<lambda>a c. \<up> (c = a)) = pure Id"
    unfolding pure_def by simp
  show ?thesis
    by (subst *) simp
qed

lemma pointwise_cmp_iff:
  "pointwise_cmp P n M M' \<longleftrightarrow> list_all2 P (take ((n + 1) * (n + 1)) xs) (take ((n + 1) * (n + 1)) ys)"
  if "\<forall>i\<le>n. \<forall>j\<le>n. xs ! (i + i * n + j) = M i j"
    "\<forall>i\<le>n. \<forall>j\<le>n. ys ! (i + i * n + j) = M' i j"
    "(n + 1) * (n + 1) \<le> length xs" "(n + 1) * (n + 1) \<le> length ys"
  using that unfolding pointwise_cmp_def
  unfolding list_all2_conv_all_nth
  apply clarsimp
  apply safe
  subgoal premises prems for x
  proof -
    let ?i = "x div (n + 1)" let ?j = "x mod (n + 1)"
    from \<open>x < _\<close> have "?i < Suc n" "?j \<le>n"
      by (simp add: less_mult_imp_div_less)+
    with prems have
      "xs ! (?i + ?i * n + ?j) = M ?i ?j" "ys ! (?i + ?i * n + ?j) = M' ?i ?j"
      "P (M ?i ?j) (M' ?i ?j)"
      by auto
    moreover have "?i + ?i * n + ?j = x"
      by (metis ab_semigroup_add_class.add.commute mod_div_mult_eq mult_Suc_right plus_1_eq_Suc)
    ultimately show \<open>P (xs ! x) (ys ! x)\<close>
      by auto
  qed
  subgoal for i j
    apply (erule allE[of _ i], erule impE, simp)
    apply (erule allE[of _ i], erule impE, simp)
    apply (erule allE[of _ "i + i * n + j"], erule impE)
    subgoal
      by (rule le_imp_less_Suc) (auto intro!: add_mono simp: algebra_simps)
    apply (erule allE[of _ j], erule impE, simp)
    apply (erule allE[of _ j], erule impE, simp)
    apply simp
    done
  done


fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse sep (x # y # xs) = x # sep # intersperse sep (y # xs)" |
  "intersperse _ xs = xs"

no_notation infinity ("\<infinity>")

section \<open>Refinement\<close>

instance DBMEntry :: ("{countable}") countable
  apply (rule
    countable_classI[of
      "(\<lambda>Le (a::'a) \<Rightarrow> to_nat (0::nat,a) |
           DBM.Lt a \<Rightarrow> to_nat (1::nat,a) |
            DBM.INF \<Rightarrow> to_nat (2::nat,undefined::'a) )"])
apply (simp split: DBMEntry.splits)
done

instance DBMEntry :: ("{heap}") heap ..

definition dbm_subset' :: "nat \<Rightarrow> ('t :: {linorder, zero}) DBM' \<Rightarrow> 't DBM' \<Rightarrow> bool" where
  "dbm_subset' n M M' \<equiv> pointwise_cmp (\<le>) n (curry M) (curry M')"

lemma dbm_subset'_alt_def:
  "dbm_subset' n M M' \<equiv>
    list_all (\<lambda> i. list_all (\<lambda> j. (op_mtx_get M (i, j) \<le> op_mtx_get M' (i, j))) [0..<Suc n]) [0..<Suc n]"
by (simp add: dbm_subset'_def pointwise_cmp_alt_def neutral)

lemma dbm_subset_alt_def'[code]:
  "dbm_subset n M M' =
    (list_ex (\<lambda> i. op_mtx_get M (i, i) < 0) [0..<Suc n] \<or>
    list_all (\<lambda> i. list_all (\<lambda> j. (op_mtx_get M (i, j) \<le> op_mtx_get M' (i, j))) [0..<Suc n]) [0..<Suc n])"
by (simp add: dbm_subset_def check_diag_alt_def pointwise_cmp_alt_def neutral)

context
  fixes n :: nat
begin

abbreviation
  mtx_assn :: "(nat \<times> nat \<Rightarrow> ('a :: {linordered_ab_monoid_add, heap})) \<Rightarrow> 'a array \<Rightarrow> assn"
where
  "mtx_assn \<equiv> asmtx_assn (Suc n) id_assn"

(* declare param_upt[sepref_import_param] *)

lemma [sepref_import_param]: "(Le,Le) \<in> Id\<rightarrow>Id" by simp
lemmas Relation.IdI[where a = \<infinity>, sepref_import_param]
lemma [sepref_import_param]: "((+),(+)) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(uminus,uminus) \<in> (Id::(_*_)set)\<rightarrow>Id" by simp

sepref_definition reset_canonical_upd_impl' is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo reset_canonical_upd x))" ::
  "[\<lambda>(((_,i),j),_). i\<le>n \<and> j\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding reset_canonical_upd_alt_def op_mtx_set_def[symmetric] by sepref

sepref_definition reset_canonical_upd_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo reset_canonical_upd x))" ::
  "[\<lambda>(((_,i),j),_). i\<le>n \<and> j\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k  *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding reset_canonical_upd_alt_def op_mtx_set_def[symmetric] by sepref

sepref_definition up_canonical_upd_impl is
  "uncurry (RETURN oo up_canonical_upd)" :: "[\<lambda>(_,i). i\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding up_canonical_upd_def op_mtx_set_def[symmetric] by sepref

lemma [sepref_import_param]:
  "(Le 0, 0) \<in> Id"
  unfolding neutral by simp

(* XXX Not sure if this is dangerous *)
sepref_register 0

sepref_definition check_diag_impl' is
  "uncurry (RETURN oo check_diag)" ::
  "[\<lambda>(i, _). i\<le>n]\<^sub>a nat_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow> bool_assn"
  unfolding check_diag_alt_def list_ex_foldli neutral[symmetric] by sepref

lemma [sepref_opt_simps]:
  "(x = True) = x"
by simp

sepref_definition dbm_subset'_impl2 is
  "uncurry2 (RETURN ooo dbm_subset')" ::
  "[\<lambda>((i, _), _). i\<le>n]\<^sub>a nat_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow> bool_assn"
unfolding dbm_subset'_alt_def list_all_foldli by sepref

definition
  "dbm_subset'_impl' \<equiv> \<lambda>m a b.
    do {
    imp_for 0 ((m + 1) * (m + 1)) Heap_Monad.return
      (\<lambda>i _. do {
        x \<leftarrow> Array.nth a i; y \<leftarrow> Array.nth b i; Heap_Monad.return (x \<le> y)
      })
      True
    }"

lemma imp_for_list_all2_spec:
  "
  <a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys>
  imp_for 0 n' Heap_Monad.return
    (\<lambda>i _. do {
      x \<leftarrow> Array.nth a i; y \<leftarrow> Array.nth b i; Heap_Monad.return (P x y)
    })
    True
  <\<lambda>r. \<up>(r \<longleftrightarrow> list_all2 P (take n' xs) (take n' ys)) * a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys>\<^sub>t"
  if "n' \<le> length xs" "n' \<le> length ys"
  apply (rule cons_rule[rotated 2])
    apply (rule imp_for_list_all2'[where xs = xs and ys = ys and R = id_assn and S = id_assn])
        apply (use that in simp; fail)+
    apply (sep_auto simp: pure_def array_assn_def is_array_def)+
  done

lemma dbm_subset'_impl'_refine:
  "(uncurry2 dbm_subset'_impl', uncurry2 (RETURN \<circ>\<circ>\<circ> dbm_subset'))
\<in> [\<lambda>((i, _), _). i = n]\<^sub>a nat_assn\<^sup>k *\<^sub>a local.mtx_assn\<^sup>k *\<^sub>a local.mtx_assn\<^sup>k \<rightarrow> bool_assn"
  apply sepref_to_hoare
  unfolding dbm_subset'_impl'_def
  unfolding amtx_assn_def hr_comp_def is_amtx_def
(* XXX The simp rules for imp_for need a name *)
  apply (sep_auto heap: imp_for_list_all2_spec simp only:)
    apply (simp; intro add_mono mult_mono; simp; fail)+
  apply sep_auto

  subgoal for b bi ba bia l la a bb
    unfolding dbm_subset'_def by (simp add: pointwise_cmp_iff[where xs = l and ys = la])

  subgoal for b bi ba bia l la a bb
    unfolding dbm_subset'_def by (simp add: pointwise_cmp_iff[where xs = l and ys = la])
  done

sepref_register check_diag ::
  "nat \<Rightarrow> _ :: {linordered_cancel_ab_monoid_add,heap} DBMEntry i_mtx \<Rightarrow> bool"

sepref_register dbm_subset' ::
  "nat \<Rightarrow> 'a :: {linordered_cancel_ab_monoid_add,heap} DBMEntry i_mtx \<Rightarrow> 'a DBMEntry i_mtx \<Rightarrow> bool"

lemmas [sepref_fr_rules] = dbm_subset'_impl'_refine check_diag_impl'.refine

sepref_definition dbm_subset_impl' is
  "uncurry2 (RETURN ooo dbm_subset)" ::
  "[\<lambda>((i, _), _). i=n]\<^sub>a nat_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow> bool_assn"
unfolding dbm_subset_def dbm_subset'_def[symmetric] short_circuit_conv by sepref

context
  notes [id_rules] = itypeI[of n "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

sepref_definition dbm_subset_impl is
  "uncurry (RETURN oo PR_CONST (dbm_subset n))" :: "mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset_def dbm_subset'_def[symmetric] short_circuit_conv PR_CONST_def
  by sepref

sepref_definition check_diag_impl is
  "RETURN o PR_CONST (check_diag n)" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding check_diag_alt_def list_ex_foldli neutral[symmetric] PR_CONST_def
  by sepref

sepref_definition dbm_subset'_impl is
  "uncurry (RETURN oo PR_CONST (dbm_subset' n))" :: "mtx_assn\<^sup>k *\<^sub>a mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset'_alt_def list_all_foldli PR_CONST_def
  by sepref

end

abbreviation "clock_assn \<equiv> nbn_assn (Suc n)"

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
unfolding abstra_upd_alt_def zero_clock_def[symmetric] by sepref

sepref_register abstra_upd ::
  "(nat, ('a :: {linordered_cancel_ab_monoid_add,uminus,heap})) acconstraint
  \<Rightarrow> 'a DBMEntry i_mtx \<Rightarrow> 'a DBMEntry i_mtx"

lemmas [sepref_fr_rules] = abstra_upd_impl.refine

sepref_definition abstr_upd_impl is
  "uncurry (RETURN oo abstr_upd)"
  :: "(list_assn (acconstraint_assn clock_assn id_assn))\<^sup>k *\<^sub>a mtx_assn\<^sup>d \<rightarrow>\<^sub>a mtx_assn"
unfolding abstr_upd_alt_def by sepref

lemma [sepref_import_param]: "(norm_lower, norm_lower) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(norm_upper, norm_upper) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp
lemma [sepref_import_param]: "(norm_diag,  norm_diag) \<in> Id\<rightarrow>Id" by simp

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
  unfolding norm_upd_def norm_upd_line_def zero_clock2_def[symmetric] by sepref

sepref_definition norm_upd_impl' is
  "uncurry2 (RETURN ooo norm_upd)" ::
   "[\<lambda>((_, xs), i). length xs > n \<and> i\<le>n]\<^sub>a mtx_assn\<^sup>d *\<^sub>a (list_assn id_assn)\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn"
unfolding norm_upd_def norm_upd_line_def zero_clock2_def[symmetric] by sepref

export_code abstr_upd_impl in SML_imp

export_code abstra_upd_impl in SML_imp

export_code dbm_subset_impl in SML_imp

text \<open>DBM to List\<close>
definition dbm_to_list :: "(nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> 'a list" where
  "dbm_to_list M \<equiv>
  rev $ fold (\<lambda>i xs. fold (\<lambda>j xs. M (i, j) # xs) [0..<Suc n] xs) [0..<Suc n] []
"

context
  notes [id_rules] = itypeI[of n "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

sepref_definition dbm_to_list_impl is
  "RETURN o PR_CONST dbm_to_list" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"
  unfolding dbm_to_list_def HOL_list.fold_custom_empty PR_CONST_def by sepref

text \<open>DBM to String\<close>

context
  fixes show_clock :: "nat \<Rightarrow> string"
    and show_num :: "'a :: {linordered_ab_group_add,heap} \<Rightarrow> string"
begin

definition
  "make_string e i j \<equiv>
    if i = j then if e < 0 then Some (''EMPTY'') else None
    else
    if i = 0 then
    case e of
      DBMEntry.Le a \<Rightarrow> if a = 0 then None else Some (show_clock j @ '' >= '' @ show_num (- a))
    | DBMEntry.Lt a \<Rightarrow> Some (show_clock j @ '' > ''  @ show_num (- a))
    | _ \<Rightarrow> None
    else if j = 0 then
    case e of
      DBMEntry.Le a \<Rightarrow> Some (show_clock i @ '' <= '' @ show_num a)
    | DBMEntry.Lt a \<Rightarrow> Some (show_clock i @ '' < ''  @ show_num a)
    | _ \<Rightarrow> None
    else
    case e of
      DBMEntry.Le a \<Rightarrow> Some (show_clock i @ '' - '' @ show_clock j @ '' <= '' @ show_num a)
    | DBMEntry.Lt a \<Rightarrow> Some (show_clock i @ '' - '' @ show_clock j @ '' < '' @ show_num a)
    | _ \<Rightarrow> None
"

definition
  "dbm_list_to_string xs \<equiv>
  (concat o intersperse '', '' o rev o snd o snd) $ fold (\<lambda>e (i, j, acc).
    let
      v = make_string e i j;
      j = (j + 1) mod (n + 1);
      i = (if j = 0 then i + 1 else i)
    in
    case v of
      None \<Rightarrow> (i, j, acc)
    | Some s \<Rightarrow> (i, j, s # acc)
  ) xs (0, 0, [])
"

lemma [sepref_import_param]:
  "(dbm_list_to_string, PR_CONST dbm_list_to_string) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>Id\<rangle>list_rel"
  by simp

definition show_dbm where
  "show_dbm M \<equiv> PR_CONST dbm_list_to_string (dbm_to_list M)"

sepref_register "PR_CONST local.dbm_list_to_string"
sepref_register dbm_to_list :: "'b i_mtx \<Rightarrow> 'b list"

lemmas [sepref_fr_rules] = dbm_to_list_impl.refine

sepref_definition show_dbm_impl is
  "RETURN o show_dbm" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"
  unfolding show_dbm_def by sepref

end (* Context for show functions *)

end (* Context for importing n *)

end (* Context for n *)

export_code norm_upd_impl checking SML

export_code reset_canonical_upd_impl checking SML

export_code reset_canonical_upd_impl checking SML

export_code up_canonical_upd_impl checking SML

export_code dbm_subset_impl checking SML

code_thms dbm_subset

lemma [code]:
  "dbm_le a b = (a = b \<or> (a \<prec> b))"
unfolding dbm_le_def by auto

export_code dbm_subset checking SML

export_code dbm_subset in SML

end
