theory Deadlock_Impl
  imports Deadlock "library/Abstract_Term"
begin

paragraph \<open>Misc\<close>

lemma constraint_clk_conv_ac:
  "constraint_clk (conv_ac ac) = constraint_clk ac"
  by (cases ac; auto)

lemma constraint_clk_conv_cc:
  "collect_clks (conv_cc cc) = collect_clks cc"
  by (auto simp: collect_clks_def constraint_clk_conv_ac image_def)

lemma atLeastLessThan_alt_def:
  "{a..<b} = {k. a \<le> k \<and> k < b}"
  by auto

lemma atLeastLessThan_Suc_alt_def:
  "{a..<Suc b} = {k. a \<le> k \<and> k \<le> b}"
  by auto

lemma (in Graph_Defs) deadlock_if_deadlocked:
  "deadlock y" if "deadlocked y"
  using that unfolding deadlock_def by (inst_existentials y) auto



subsection \<open>Functional Refinement\<close>

paragraph \<open>Elementary list operations\<close>

lemma map_conv_rev_fold:
  "map f xs = rev (fold (\<lambda> a xs. f a # xs) xs [])"
proof -
  have "fold (\<lambda> a xs. f a # xs) xs ys = rev (map f xs) @ ys" for ys
    by (induction xs arbitrary: ys) auto
  then show ?thesis
    by simp
qed

lemma rev_map_conv_fold:
  "rev (map f xs) = fold (\<lambda> a xs. f a # xs) xs []"
  using map_conv_rev_fold[of f xs] by simp

lemma concat_map_conv_rev_fold:
  "concat (map f xs) = rev (fold (\<lambda> xs ys. rev (f xs) @ ys) xs [])"
proof -
  have "rev (fold (\<lambda> xs ys. rev (f xs) @ ys) xs ys) = rev ys @ List.maps f xs" for ys
    by (induction xs arbitrary: ys) (auto simp: maps_simps)
  then show ?thesis
    by (simp add: concat_map_maps)
qed

lemma concat_conv_fold_rev:
  "concat xss = fold (@) (rev xss) []"
  using fold_append_concat_rev[of "rev xss"] by simp

lemma filter_conv_rev_fold:
  "filter P xs = rev (fold (\<lambda>x xs. if P x then x # xs else xs) xs [])"
proof -
  have "rev ys @ filter P xs = rev (fold (\<lambda>x xs. if P x then x # xs else xs) xs ys)" for ys
    by (induction xs arbitrary: ys) (auto, metis revg.simps(2) revg_fun)
  from this[symmetric] show ?thesis
    by simp
qed

paragraph \<open>DBM operations\<close>

definition
  "free_upd1 n M c =
  (let
    M1 = fold (\<lambda>i M. if i \<noteq> c then (M((i, c) := op_mtx_get M (i, 0))) else M) [0..<Suc n] M;
    M2 = fold (\<lambda>i M. if i \<noteq> c then M((c,i) := \<infinity>)         else M) [0..<Suc n] M1
  in
    M2
  )
  "

definition
  "pre_reset_upd1 n M x \<equiv> free_upd1 n (restrict_zero_upd n M x) x"

definition
  "pre_reset_list_upd1 n M r \<equiv> fold (\<lambda> x M. pre_reset_upd1 n M x) r M"

definition
  "upd_pairs xs = fold (\<lambda>(p,q) f. f(p:=q)) xs"

lemma upd_pairs_Nil:
  "upd_pairs [] f = f"
  unfolding upd_pairs_def by simp

lemma upd_pairs_Cons:
  "upd_pairs ((p, q) # xs) f = upd_pairs xs (f(p:=q))"
  unfolding upd_pairs_def by simp

lemma upd_pairs_no_upd:
  assumes "p \<notin> fst ` set xs"
  shows "upd_pairs xs f p = f p"
  using assms by (induction xs arbitrary: f) (auto simp: upd_pairs_Nil upd_pairs_Cons)

lemma upd_pairs_upd:
  assumes "(p, y) \<in> set xs" "distinct (map fst xs)"
  shows "upd_pairs xs f p = y"
  using assms proof (induction xs arbitrary: f)
  case Nil
  then show ?case
    by (simp add: upd_pairs_Nil)
next
  case (Cons x xs)
  then show ?case
    by (cases x) (auto simp add: upd_pairs_Cons upd_pairs_no_upd)
qed

lemma upd_pairs_append:
  "upd_pairs (xs @ ys) = upd_pairs ys o upd_pairs xs"
  unfolding upd_pairs_def fold_append ..

lemma upd_pairs_commute_single:
  "upd_pairs xs (f(a := b)) = (upd_pairs xs f)(a := b)" if "a \<notin> fst ` set xs"
  using that by (induction xs arbitrary: f) (auto simp: upd_pairs_Nil upd_pairs_Cons fun_upd_twist)

lemma upd_pairs_append':
  "upd_pairs (xs @ ys) = upd_pairs xs o upd_pairs ys" if "fst ` set xs \<inter> fst ` set ys = {}"
  using that
proof (induction xs)
  case Nil
  then show ?case
    by (simp add: upd_pairs_Nil)
next
  case (Cons a xs)
  then show ?case
    by (cases a) (auto simp add: upd_pairs_Nil upd_pairs_Cons upd_pairs_commute_single)
qed

definition
  "upd_pairs' xs = fold (\<lambda>(p,q) f. f(p:=f q)) xs"

lemma upd_pairs'_Nil:
  "upd_pairs' [] f = f"
  unfolding upd_pairs'_def by simp

lemma upd_pairs'_Cons:
  "upd_pairs' ((p, q) # xs) f = upd_pairs' xs (f(p:=f q))"
  unfolding upd_pairs'_def by simp

lemma upd_pairs'_upd_pairs:
  assumes "fst ` set xs \<inter> snd ` set xs = {}"
  shows   "upd_pairs' xs f = upd_pairs (map (\<lambda>(p, q). (p, f q)) xs) f"
  using assms
proof (induction xs arbitrary: f)
  case Nil
  then show ?case
    by (simp add: upd_pairs_Nil upd_pairs'_Nil)
next
  case (Cons x xs)
  obtain a b where [simp]: "x = (a, b)"
    by (cases x)
  from Cons.prems have *:
    "map (\<lambda>(p, q). (p, if q = a then f b else f q)) xs = map (\<lambda>(p, q). (p, f q)) xs"
    by auto
  from Cons show ?case
    by (auto simp add: upd_pairs_Cons upd_pairs'_Cons *)
qed

lemma upd_pairs_map:
  "upd_pairs (map f xs) = fold (\<lambda>pq g. let (p,q) = f pq in g(p:=q)) xs"
  unfolding upd_pairs_def fold_map
  by (intro arg_cong2[where f = fold] ext) (auto simp: comp_def split: prod.split)

lemma down_upd_alt_def:
  "down_upd n M =
  upd_pairs ([((0, j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)). j \<leftarrow> [1..<Suc n]]) M"
proof -
  define xs where
    "xs = [((0::nat, j), Min ({Le 0} \<union> {M (k, j) | k. 1 \<le> k \<and> k \<le> n})). j \<leftarrow> [1..<Suc n]]"
  have "distinct (map fst xs)"
    unfolding xs_def by (auto simp add: map_concat comp_def distinct_map)
  have *: "fold min [M (k, j). k\<leftarrow>[1..<Suc n]] (Le 0) = Min ({Le 0} \<union> {M (k, j) |k. 1 \<le> k \<and> k \<le> n})"
    for j
    by (subst Min.set_eq_fold[symmetric])
       (auto simp: atLeastLessThan_Suc_alt_def simp del: upt_Suc intro: arg_cong[where f = Min])
  show ?thesis
    unfolding * xs_def[symmetric]
  by (intro ext, auto simp add: down_upd_def)
     (subst upd_pairs_upd[OF _ \<open>distinct _\<close>] upd_pairs_no_upd, auto simp: image_def xs_def; fail)+
qed

lemma down_upd_alt_def1:
  "down_upd n M =
  fold (\<lambda>j M. let (p,q) = ((0, j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)) in M(p:=q))
  [1..<Suc n] M"
proof -
  have *: "
    fold (\<lambda>j M.  let (p,q) = ((0,j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)) in M(p:=q))  xs M
  = fold (\<lambda>j M'. let (p,q) = ((0,j), fold min [M (k, j). k \<leftarrow> [1..<Suc n]] (Le 0)) in M'(p:=q)) xs M
  " for xs
  proof (induction xs arbitrary: M)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x xs)
    then show ?case
      by (auto 4 7 intro: arg_cong2[where f = min] fold_cong)
  qed
  then show ?thesis
    unfolding down_upd_alt_def upd_pairs_map ..
qed

lemma
  "free_upd n M c =
  upd_pairs ([((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c] @ [((i,c), M(i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]) M"
  if "c \<le> n"
proof -
  let ?xs1 = "\<lambda>n. [((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  let ?xs2 = "\<lambda>n. [((i,c), M(i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  define xs where "xs = ?xs1 n @ ?xs2 n"
  have "distinct (map fst xs)"
    unfolding xs_def
    apply (auto simp del: upt_Suc simp add: map_concat comp_def if_distrib split: if_split)
     apply (auto split: if_split_asm simp: distinct_map inj_on_def intro!: distinct_concat)
    done
  from \<open>c \<le> n\<close> show ?thesis
    unfolding xs_def[symmetric]
  by (intro ext, auto simp: free_upd_def)
     (subst upd_pairs_upd[OF _ \<open>distinct (map fst xs)\<close>] upd_pairs_no_upd, auto simp: xs_def; fail)+
qed

lemma free_upd_alt_def1:
  "free_upd n M c = (let
    M1 = upd_pairs' ([((i,c), (i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]) M;
    M2 = upd_pairs ([((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c]) M1
  in
    M2
  )" (is "_ = ?r")
  if "0 < c" "c \<le> n"
proof -
  let ?xs1 = "\<lambda>n. [((c,i), \<infinity>). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  let ?xs2 = "\<lambda>n. [((i,c), M(i,0)). i \<leftarrow> [0..<Suc n], i \<noteq> c]"
  define xs where "xs = ?xs1 n @ ?xs2 n"
  let ?t = "upd_pairs xs M"
  have "distinct (map fst xs)"
    unfolding xs_def
    apply (auto simp del: upt_Suc simp add: map_concat comp_def if_distrib split: if_split)
     apply (auto split: if_split_asm simp: distinct_map inj_on_def intro!: distinct_concat)
    done
  from \<open>c \<le> n\<close> have "free_upd n M c = ?t"
    by (intro ext, auto simp: free_upd_def)
      (subst upd_pairs_upd[OF _ \<open>distinct _\<close>] upd_pairs_no_upd, auto simp: xs_def; fail)+
  also have "\<dots> = ?r"
    unfolding xs_def
    apply (subst upd_pairs_append')
    subgoal
      by auto
    apply (subst upd_pairs'_upd_pairs)
    subgoal
      using \<open>c > 0\<close> by auto
    apply (simp del: upt_Suc add: map_concat)
    apply (intro arg_cong2[where f = upd_pairs] arg_cong[where f = concat])
    by (simp del: upt_Suc)+
  finally show ?thesis .
qed

lemma free_upd_free_upd1:
  "free_upd n M c = free_upd1 n M c" if "c > 0" "c \<le> n"
proof -
  let ?x1 = "\<lambda>xs. upd_pairs' ([((i,c), (i,0)). i \<leftarrow> xs, i \<noteq> c]) M"
  let ?x2 = "\<lambda>xs. fold (\<lambda>i M. if i \<noteq> c then (M((i, c) := M(i, 0))) else M) xs M"
  have *: "?x1 xs = ?x2 xs" for xs
    by (induction xs arbitrary: M) (auto simp: upd_pairs'_Nil upd_pairs'_Cons)
  let ?y1 = "\<lambda>xs. upd_pairs ([((c,i), \<infinity>). i \<leftarrow> xs, i \<noteq> c])"
  let ?y2 = "fold (\<lambda>i M. if i \<noteq> c then M((c,i) := \<infinity>) else M)"
  have **: "?y1 xs M = ?y2 xs M" for xs M
    by (induction xs arbitrary: M) (auto simp: upd_pairs_Nil upd_pairs_Cons)
  show ?thesis
    unfolding free_upd_alt_def1[OF that] free_upd1_def op_mtx_get_def * ** ..
qed

lemma free_upd_alt_def:
  "free_upd n M c =
    fold (\<lambda>i M. if i \<noteq> c then (M((c,i) := \<infinity>, (i, c) := M(i, 0))) else M) [0..<Suc n] M"
  if "c \<le> n"
  oops

lemma pre_reset_upd_pre_reset_upd1:
  "pre_reset_upd n M c = pre_reset_upd1 n M c" if "c > 0" "c \<le> n"
  unfolding pre_reset_upd_def pre_reset_upd1_def free_upd_free_upd1[OF that] ..

lemma pre_reset_list_upd_pre_reset_list_upd1:
  "pre_reset_list_upd n M cs = pre_reset_list_upd1 n M cs" if "\<forall>c \<in> set cs. 0 < c \<and> c \<le> n"
  unfolding pre_reset_list_upd_def pre_reset_list_upd1_def
  using that by (intro fold_cong; simp add: pre_reset_upd_pre_reset_upd1)

lemma pre_reset_list_transfer'[transfer_rule]:
  includes lifting_syntax shows
  "(eq_onp (\<lambda>x. x = n) ===> RI2 n ===> list_all2 (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ===> RI2 n)
    pre_reset_list pre_reset_list_upd1"
  unfolding rel_fun_def
  apply safe
  apply (subst pre_reset_list_upd_pre_reset_list_upd1[symmetric])
  subgoal
    unfolding list.rel_eq_onp by (auto simp: eq_onp_def list_all_iff)
  by (rule pre_reset_list_transfer[unfolded rel_fun_def, rule_format])
     (auto simp: eq_onp_def list_all2_iff)



subsection \<open>Imperative Refinement\<close>

context
  fixes n :: nat
  notes [id_rules] = itypeI[of n "TYPE (nat)"]
    and [sepref_import_param] = IdI[of n]
begin

sepref_definition down_impl is
  "RETURN o PR_CONST (down_upd n)" ::
  "(mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
  unfolding down_upd_alt_def1 upd_pairs_map PR_CONST_def
  unfolding Let_def prod.case
  unfolding fold_map comp_def
  unfolding neutral[symmetric]
  by sepref

context
  notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
begin

sepref_register
  abstr_upd "FW'' n" "Normalized_Zone_Semantics_Impl_Semantic_Refinement.repair_pair n"
  and_entry_upd "free_upd1 n" "restrict_zero_upd n" "pre_reset_upd1 n"

end

lemmas [sepref_fr_rules] = abstr_upd_impl.refine fw_impl_refine_FW''

sepref_definition abstr_FW_impl is
  "uncurry (RETURN oo PR_CONST (abstr_FW_upd n))" ::
  "(list_assn (acconstraint_assn (clock_assn n) id_assn))\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a mtx_assn n"
  unfolding abstr_FW_upd_def FW''_def[symmetric] PR_CONST_def by sepref

sepref_definition free_impl is
  "uncurry (RETURN oo PR_CONST (free_upd1 n))" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn n"
  unfolding free_upd1_def op_mtx_set_def[symmetric] PR_CONST_def by sepref

sepref_definition and_entry_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo and_entry_upd x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow> mtx_assn n"
  unfolding and_entry_upd_def by sepref

lemmas [sepref_fr_rules] = and_entry_impl.refine

sepref_definition restrict_zero_impl is
  "uncurry (RETURN oo PR_CONST (restrict_zero_upd n))" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow> mtx_assn n"
  unfolding restrict_zero_upd_def PR_CONST_def by sepref

lemmas [sepref_fr_rules] = free_impl.refine restrict_zero_impl.refine

sepref_definition pre_reset_impl is
  "uncurry (RETURN oo PR_CONST (pre_reset_upd1 n))" ::
  "[\<lambda>(_, i). i\<le>n]\<^sub>a (mtx_assn n)\<^sup>d *\<^sub>a (clock_assn n)\<^sup>k \<rightarrow> mtx_assn n"
  unfolding pre_reset_upd1_def PR_CONST_def by sepref

lemmas [sepref_fr_rules] = pre_reset_impl.refine

sepref_definition pre_reset_list_impl is
  "uncurry (RETURN oo PR_CONST (pre_reset_list_upd1 n))" ::
  "(mtx_assn n)\<^sup>d *\<^sub>a (list_assn (clock_assn n))\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
  unfolding pre_reset_list_upd1_def PR_CONST_def by sepref

sepref_definition and_entry_repair_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo PR_CONST (and_entry_repair_upd n) x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow> mtx_assn n"
  unfolding and_entry_repair_upd_def PR_CONST_def by sepref

private definition
  "V_dbm'' = V_dbm' n"

text \<open>We use @{term V_dbm''} because we cannot register @{term V_dbm'} twice with the refinement
  framework: we view it as a function first, and as a DBM later.\<close>

lemma V_dbm'_alt_def:
  "V_dbm' n = op_amtx_new (Suc n) (Suc n) (V_dbm'')"
  unfolding V_dbm''_def by simp

notation fun_rel_syn (infixr "\<rightarrow>" 60)

text \<open>We need the custom rule here because @{term V_dbm'} is a higher-order constant\<close>
lemma [sepref_fr_rules]:
  "(uncurry0 (return V_dbm''), uncurry0 (RETURN (PR_CONST (V_dbm''))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
  by sepref_to_hoare sep_auto

sepref_register "V_dbm'' :: nat \<times> nat \<Rightarrow> _ DBMEntry"

text \<open>Necessary to solve side conditions of @{term op_amtx_new}\<close>
lemma V_dbm''_bounded:
  "mtx_nonzero V_dbm'' \<subseteq> {0..<Suc n} \<times> {0..<Suc n}"
  unfolding mtx_nonzero_def V_dbm''_def V_dbm'_def neutral by auto

text \<open>We need to pre-process the lemmas due to a failure of \<open>TRADE\<close>\<close>
lemma V_dbm''_bounded_1:
  "(a, b) \<in> mtx_nonzero V_dbm'' \<Longrightarrow> a < Suc n"
  using V_dbm''_bounded by auto

lemma V_dbm''_bounded_2:
  "(a, b) \<in> mtx_nonzero V_dbm'' \<Longrightarrow> b < Suc n"
  using V_dbm''_bounded by auto

lemmas [sepref_opt_simps] = V_dbm''_def

sepref_definition V_dbm_impl is
  "uncurry0 (RETURN (PR_CONST (V_dbm' n)))" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
  supply V_dbm''_bounded_1[simp] V_dbm''_bounded_2[simp]
  using V_dbm''_bounded
  apply (subst V_dbm'_alt_def)
  unfolding PR_CONST_def by sepref

text \<open>This form of 'type casting' is used to assert a bound on the natural number.\<close>
private definition make_clock :: "nat \<Rightarrow> nat" where [sepref_opt_simps]:
  "make_clock x = x"

lemma make_clock[sepref_import_param]:
  "(make_clock, make_clock) \<in> [\<lambda>i. i \<le> n]\<^sub>f nat_rel \<rightarrow> nbn_rel (Suc n)"
  unfolding make_clock_def by (rule frefI) simp

private definition "get_entries m =
  [(make_clock i, make_clock j).
    i\<leftarrow>[0..<Suc n], j\<leftarrow>[0..<Suc n], (i > 0 \<or> j > 0) \<and> i \<le> n \<and> j \<le> n \<and> m (i, j) \<noteq> \<infinity>]"

private definition
  "upd_entry i j M m = and_entry_repair_upd n j i (neg_dbm_entry (m (i, j))) (op_mtx_copy M)"

private definition
  "upd_entries i j m = map (\<lambda> M. upd_entry i j M m)"

context
  notes [map_type_eqs] = map_type_eqI[of "TYPE(nat * nat \<Rightarrow> 'e)" "TYPE('e i_mtx)"]
begin

sepref_register
  "dbm_minus_canonical_check_upd n"
  "dbm_subset_fed_upd n" "abstr_FW_upd n" "pre_reset_list_upd1 n" "V_dbm' n" "down_upd n"
  upd_entry upd_entries get_entries "and_entry_repair_upd n"

end

lemma [sepref_import_param]: "(neg_dbm_entry,neg_dbm_entry) \<in> Id\<rightarrow>Id" by simp

lemmas [sepref_fr_rules] = and_entry_repair_impl.refine

sepref_definition upd_entry_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo PR_CONST upd_entry x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow> mtx_assn n"
  unfolding upd_entry_def PR_CONST_def by sepref

text \<open>This is to ensure that the refinement initially infers the right 'type' for list arguments.\<close>
lemma [intf_of_assn]:
  "intf_of_assn AA TYPE('aa) \<Longrightarrow> intf_of_assn (list_assn(AA)) TYPE('aa list)"
  by (rule intf_of_assnI)

lemmas [sepref_fr_rules] = upd_entry_impl.refine

sepref_definition upd_entries_impl is
  "uncurry2 (uncurry (\<lambda>x. RETURN ooo PR_CONST upd_entries x))" ::
  "[\<lambda>(((i, j),_),_). i\<le>n \<and> j \<le> n]\<^sub>a
    nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k *\<^sub>a (list_assn (mtx_assn n))\<^sup>k \<rightarrow> list_assn (mtx_assn n)"
  unfolding upd_entries_def PR_CONST_def
  unfolding map_conv_rev_fold rev_conv_fold
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

lemma [sepref_import_param]: "((=), (=)) \<in> Id\<rightarrow>Id\<rightarrow>Id" by simp

sepref_definition get_entries_impl is
  "RETURN o PR_CONST get_entries" ::
  "(mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a list_assn ((clock_assn n) \<times>\<^sub>a (clock_assn n))"
  unfolding get_entries_def PR_CONST_def
  unfolding map_conv_rev_fold
  unfolding concat_conv_fold_rev
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

lemmas [sepref_fr_rules] = upd_entries_impl.refine get_entries_impl.refine

private lemma dbm_minus_canonical_upd_alt_def:
  "dbm_minus_canonical_upd n xs m =
  concat (map (\<lambda>ij. map (\<lambda> M.
      and_entry_repair_upd n (snd ij) (fst ij) (neg_dbm_entry (m (fst ij, snd ij))) (op_mtx_copy M))
    xs) (get_entries m))"
  unfolding dbm_minus_canonical_upd_def op_mtx_copy_def get_entries_def split_beta make_clock_def
  by simp

sepref_definition dbm_minus_canonical_impl is
  "uncurry (RETURN oo PR_CONST (dbm_minus_canonical_check_upd n))" ::
  "(list_assn (mtx_assn n))\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a list_assn (mtx_assn n)"
  unfolding dbm_minus_canonical_check_upd_def dbm_minus_canonical_upd_alt_def PR_CONST_def
  unfolding upd_entry_def[symmetric] upd_entries_def[symmetric]
  unfolding filter_conv_rev_fold concat_map_conv_rev_fold rev_conv_fold
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

lemmas [sepref_fr_rules] = dbm_minus_canonical_impl.refine

sepref_definition dbm_subset_fed_impl is
  "uncurry (RETURN oo PR_CONST (dbm_subset_fed_upd n))" ::
  "(mtx_assn n)\<^sup>d *\<^sub>a (list_assn (mtx_assn n))\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  unfolding dbm_subset_fed_upd_alt_def PR_CONST_def
  unfolding list_ex_foldli filter_conv_rev_fold
  unfolding short_circuit_conv
  supply [sepref_fr_rules] = HOL_list_empty_hnr_aux
  by sepref

end (* Fixed n *)


subsection \<open>Implementation for a Concrete Automaton\<close>

context Reachability_Problem_Impl
begin

definition
  "check_deadlock_dbm l M = dbm_subset_fed_upd n M (
   [down_upd n (abstr_FW_upd n (inv_of_A l) (abstr_FW_upd n g
      (pre_reset_list_upd1 n (abstr_FW_upd n (inv_of_A l') (V_dbm' n)) r)
    )). (g, a, r, l') \<leftarrow> trans_fun l
   ]
  )"

abbreviation zone_of ("\<lbrakk>_\<rbrakk>") where "zone_of M \<equiv> [curry (conv_M M)]\<^bsub>v,n\<^esub>"

theorem check_deadlock_dbm_correct:
  "TA.check_deadlock l \<lbrakk>M\<rbrakk> = check_deadlock_dbm l M" if
  "\<lbrakk>M\<rbrakk> \<subseteq> V" "l \<in> states" "Deadlock.canonical' n (curry (conv_M M))"
proof -
  text \<open>0. Setup \<open>&\<close> auxiliary facts\<close>
  include lifting_syntax
  note [simp del] = And.simps abstr.simps (* TODO: make definitions *)
  have inv_of_simp: "inv_of (conv_A A) l = conv_cc (inv_of A l)" if \<open>l \<in> states\<close> for l
    using inv_fun \<open>l \<in> states\<close> unfolding inv_rel_def b_rel_def fun_rel_def
    by (force split: prod.split simp: inv_of_def)

  have trans_funD: "l' \<in> states"
    "collect_clks (inv_of A l) \<subseteq> clk_set A" "collect_clks (inv_of A l') \<subseteq> clk_set A"
    "collect_clks g \<subseteq> clk_set A" "set r \<subseteq> clk_set A"
    if "(g, a, r, l') \<in> set(trans_fun l)" for g a r l'
    subgoal
      using \<open>l \<in> states\<close> that trans_impl_states by auto
    subgoal
      by (metis collect_clks_inv_clk_set)
    subgoal
      by (metis collect_clks_inv_clk_set)
    subgoal
      using that \<open>l \<in> _\<close> by (intro collect_clocks_clk_set trans_impl_trans_of)
    subgoal
      using that \<open>l \<in> _\<close> by (intro reset_clk_set trans_impl_trans_of)
    done

  text \<open>1. Transfer to most abstract DBM operations\<close>
  have [transfer_rule]:
    "(eq_onp (\<lambda> (g, a, r, l'). (g, a, r, l') \<in> set (trans_fun l)) ===> RI2 n)
      (\<lambda>(g, a, r, l'). down n
          (abstr_FW n (conv_cc (inv_of A l))
            (abstr_FW n (conv_cc g)
              (pre_reset_list n (abstr_FW n (conv_cc (inv_of A l')) V_dbm v) r) v) v))
      (\<lambda>(g, a, r, l'). down_upd n
          (abstr_FW_upd n (inv_of A l)
            (abstr_FW_upd n g (pre_reset_list_upd1 n (abstr_FW_upd n (inv_of A l') (V_dbm' n)) r))
          ))
    " (is "(_ ===> RI2 n) (\<lambda> (g, a, r, l'). ?f g a r l') (\<lambda> (g, a, r, l'). ?g g a r l')")
  proof (intro rel_funI, clarsimp simp: eq_onp_def)
    fix g a r l' assume "(g, a, r, l') \<in> set (trans_fun l)"
    have *: "rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri (conv_ac ac) ac"
      if "constraint_clk ac > 0" "constraint_clk ac \<le> n" for ac
      using that by (cases ac) (auto simp: eq_onp_def ri_def)
    have *: "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri) (conv_cc g) g"
      if "collect_clks g \<subseteq> clk_set A" for g
      unfolding list_all2_map1 using that clock_range
      by (auto simp: collect_clks_def intro!: * list.rel_refl_strong)
    have [transfer_rule]:
      "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri) (conv_cc g) g"
      "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri)
        (conv_cc (inv_of A l)) (inv_of A l)"
      "list_all2 (rel_acconstraint (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) ri)
        (conv_cc (inv_of A l')) (inv_of A l')"
      by (intro * trans_funD[OF \<open>(g, a, r, l') \<in> set (trans_fun l)\<close>])+
    have [transfer_rule]:
      "list_all2 (eq_onp (\<lambda>x. 0 < x \<and> x < Suc n)) r r"
      using trans_funD(5)[OF \<open>(g, a, r, l') \<in> set (trans_fun l)\<close>] clock_range
      by (auto 4 3 dest: bspec subsetD simp: eq_onp_def list_all2_same)
    show "RI2 n (?f g a r l') (?g g a r l')"
      by transfer_prover
  qed
  have [transfer_rule]:
    "(eq_onp (\<lambda>l'. l' = l) ===> list_all2 (eq_onp (\<lambda>(g,a,r,l'). (g,a,r,l') \<in> set (trans_fun l))))
      trans_fun trans_fun
    "
    unfolding rel_fun_def eq_onp_def by (auto intro: list.rel_refl_strong)
  note [transfer_rule] = dbm_subset_fed_transfer
  have [transfer_rule]: "eq_onp (\<lambda>l'. l' = l) l l" "(eq_onp (\<lambda>x. x < Suc n)) n n"
    by (auto simp: eq_onp_def)
  have *: "
    (dbm_subset_fed_check n (curry (conv_M M))
         (map (\<lambda>(g, a, r, l').
                  down n
          (abstr_FW n (conv_cc (inv_of A l))
            (abstr_FW n (conv_cc g)
              (pre_reset_list n (abstr_FW n (conv_cc (inv_of A l')) V_dbm v) r) v) v))
           (trans_fun l))) =
    (dbm_subset_fed_upd n M
         (map (\<lambda>(g, a, r, l').
                  down_upd n
          (abstr_FW_upd n (inv_of A l)
            (abstr_FW_upd n g (pre_reset_list_upd1 n (abstr_FW_upd n (inv_of A l') (V_dbm' n)) r))
          ))
         (trans_fun l)))
    "
    by transfer_prover

  text \<open>2. Semantic argument establishing equivalences between zones and DBMs\<close>
  have **:
    "[down n (abstr_FW n (conv_cc (inv_of A l)) (abstr_FW n (conv_cc g)
          (pre_reset_list n (abstr_FW n (conv_cc (inv_of A l')) V_dbm v) r) v) v)]\<^bsub>v,n\<^esub>
  = (zone_set_pre ({u. u \<turnstile> inv_of (conv_A A) l'} \<inter> V) r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}
       \<inter> {u. u \<turnstile> conv_cc g} \<inter> {u. u \<turnstile> inv_of (conv_A A) l})\<^sup>\<down> \<inter> V"
    if "(g, a, r, l') \<in> set(trans_fun l)" for g a r l'
  proof -
    from trans_funD[OF \<open>(g, a, r, l') \<in> set (trans_fun l)\<close>] have clock_conditions:
      "\<forall>c\<in>collect_clks (conv_cc (inv_of A l)). 0 < c \<and> c \<le> n"
      "\<forall>c\<in>collect_clks (conv_cc (inv_of A l')). 0 < c \<and> c \<le> n"
      "\<forall>c\<in>collect_clks (conv_cc g). 0 < c \<and> c \<le> n"
      "\<forall>c\<in>set r. 0 < c \<and> c \<le> n"
      using \<open>l \<in> states\<close> clock_range by (auto simp: constraint_clk_conv_cc)
    have structural_conditions:
      "abstr_FW n (conv_cc (inv_of A l')) V_dbm v 0 0 \<le> 0"
      "\<forall>x\<in>set r. abstr_FW n (map conv_ac (inv_of A l')) V_dbm v 0 x \<le> 0"
      subgoal
        using abstr_FW_diag_preservation[of n V_dbm "conv_cc (inv_of A l')" v]
        by (simp add: V_dbm_def)
      subgoal
        using \<open>\<forall>c\<in>set r. 0 < c \<and> c \<le> n\<close>
        by (auto 4 3 simp: V_dbm_def intro: abstr_FW_mono order.trans)
      done
    note side_conditions = clock_conditions structural_conditions
      abstr_FW_canonical[unfolded canonical'_def] abstr_FW_canonical
    show ?thesis
      apply (subst dbm.down_correct, rule side_conditions)
      apply (subst dbm.abstr_FW_correct, rule side_conditions)
      apply (subst dbm.abstr_FW_correct, rule side_conditions)
      apply (subst dbm.pre_reset_list_correct, (rule side_conditions)+)
      apply (subst dbm.abstr_FW_correct, (rule side_conditions)+)
      by (simp add: inv_of_simp[OF \<open>l \<in> states\<close>] inv_of_simp[OF \<open>l' \<in> states\<close>] dbm.V_dbm_correct
          atLeastLessThanSuc_atLeastAtMost Int_commute)
  qed
  have **:
    "(\<Union>x\<in>set (trans_fun l).
              dbm.zone_of
               (case x of (g, a, r, l') \<Rightarrow>
                  down n
        (abstr_FW n (conv_cc (inv_of A l))
          (abstr_FW n (conv_cc g)
            (pre_reset_list n (abstr_FW n (conv_cc (inv_of A l')) V_dbm v) r) v) v)))
    = (\<Union>(g,a,r,l')\<in>set (trans_fun l).
    ((zone_set_pre ({u. u \<turnstile> inv_of (conv_A A) l'} \<inter> V) r \<inter> {u. \<forall> x \<in> set r. u x \<ge> 0}
           \<inter> {u. u \<turnstile> conv_cc g} \<inter> {u. u \<turnstile> inv_of (conv_A A) l})\<^sup>\<down> \<inter> V)
    )
    "
    by (auto simp: **)

  text \<open>3. Putting it all together\<close>
  have transD: "\<exists> g'. (g', a, r, l') \<in> set (trans_fun l) \<and> g = conv_cc g'"
    if "conv_A A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" for g a r l'
    using trans_of_trans_impl[OF _ \<open>l \<in> states\<close>] that
    unfolding trans_of_def by (auto 5 0 split: prod.split_asm)
  have transD2:
    "conv_A A \<turnstile> l \<longrightarrow>\<^bsup>conv_cc g,a,r\<^esup> l'" if "(g, a, r, l') \<in> set (trans_fun l)" for g a r l'
    using trans_impl_trans_of[OF that \<open>l \<in> states\<close>]
    unfolding trans_of_def by (auto 4 3 split: prod.split)
  show ?thesis
    unfolding TA.check_deadlock_alt_def[OF \<open>_ \<subseteq> V\<close>] check_deadlock_dbm_def inv_of_A_def *[symmetric]
    apply (subst dbm.dbm_subset_fed_check_correct[symmetric, OF that(3)])
    apply (simp add: **)
    apply safe
    subgoal for x
      by (auto 4 5 elim!: transD[elim_format] dest: subsetD)
    subgoal for x
      apply (drule subsetD, assumption)
      apply clarsimp
      subgoal for g a r l'
        apply (inst_existentials "
          (zone_set_pre ({u. u \<turnstile> inv_of (conv_A A) l'} \<inter> V) r \<inter> {u. \<forall>x\<in>set r. 0 \<le> u x}
           \<inter> {u. u \<turnstile> conv_cc g} \<inter> {u. u \<turnstile> inv_of (conv_A A) l})\<^sup>\<down> \<inter> V" "conv_cc g" a r l')
        apply (auto dest: transD2)
        done
      done
    done
qed

lemmas [sepref_fr_rules] =
  V_dbm_impl.refine abstr_FW_impl.refine pre_reset_list_impl.refine
  down_impl.refine dbm_subset_fed_impl.refine

sepref_definition check_deadlock_impl is
  "uncurry (RETURN oo PR_CONST check_deadlock_dbm)" ::
  "location_assn\<^sup>k *\<^sub>a (mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  unfolding check_deadlock_dbm_def PR_CONST_def
  unfolding case_prod_beta
  unfolding map_conv_rev_fold
  apply (rewrite "HOL_list.fold_custom_empty")
  by sepref

end (* Reachability Problem Impl *)


subsection \<open>Checking a Property on the Reachable Set\<close>

locale Worklist_Map2_Impl_check =
  Worklist_Map2_Impl_finite +
  fixes Q :: "'a \<Rightarrow> bool"
  fixes Qi
  assumes Q_refine: "(Qi,RETURN o PR_CONST Q) \<in> A\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  and F_False: "F = (\<lambda> _. False)"
  and Q_mono: "\<And> a b. a \<preceq> b \<Longrightarrow> \<not> empty a \<Longrightarrow> reachable a \<Longrightarrow> reachable b \<Longrightarrow> Q a \<Longrightarrow> Q b"
begin

definition check_passed :: "bool nres" where
  "check_passed = do {
    (r, passed) \<leftarrow> pw_algo_map2;
    ASSERT (finite (dom passed));
    passed \<leftarrow> ran_of_map passed;
    r \<leftarrow> nfoldli passed (\<lambda>b. \<not>b)
      (\<lambda> passed' _.
        do {
          passed' \<leftarrow> SPEC (\<lambda>l. set l = passed');
          nfoldli passed' (\<lambda>b. \<not>b)
            (\<lambda>v' _.
              if Q v' then RETURN True else RETURN False
            )
            False
        }
      )
      False;
    RETURN r
  }"

lemma check_passed_correct:
  "check_passed \<le> SPEC (\<lambda> r. (r \<longleftrightarrow> (\<exists> a. reachable a \<and> \<not> empty a \<and> Q a)))"
proof -
  have [simp]: "F_reachable = False"
    unfolding F_reachable_def F_False Search_Space_Defs.F_reachable_def by simp
  define outer_inv where "outer_inv passed done todo r \<equiv>
    set done \<union> set todo = ran passed \<and>
    (\<not> r \<longrightarrow> (\<forall> S \<in> set done. \<forall> x \<in> S. \<not> Q x)) \<and>
    (r \<longrightarrow> (\<exists> a. reachable a \<and> \<not> empty a \<and> Q a))
  " for passed :: "'c \<Rightarrow> 'a set option" and "done" todo and r :: bool
  define inner_inv where "inner_inv passed done todo r \<equiv>
    set done \<union> set todo = passed \<and>
    (\<not> r \<longrightarrow> (\<forall> x \<in> set done. \<not> Q x)) \<and>
    (r \<longrightarrow> (\<exists> a. reachable a \<and> \<not> empty a \<and> Q a))
  " for passed :: "'a set" and "done" todo and r :: bool
  show ?thesis
    supply [refine_vcg] = pw_algo_map2_correct
    unfolding check_passed_def
    apply (refine_rcg refine_vcg)
    subgoal
      by auto
    subgoal for _ brk_false passed range_list
      apply (rule nfoldli_rule[where I = "outer_inv passed"])

(* Init: I [] range_list False *)
      subgoal
        unfolding outer_inv_def
        by auto

(* Inner loop *)
        apply (refine_rcg refine_vcg)
      subgoal for current "done" todo r xs
        apply clarsimp
        apply (rule nfoldli_rule[where I = "inner_inv current"])

        subgoal (* Init: I [] xs False *)
          unfolding inner_inv_def
          by auto

(* inner inv *)
        subgoal for p x l1 l2 r'
          apply (auto simp: inner_inv_def)
          apply (auto simp: outer_inv_def)
          unfolding map_set_rel_def
          apply auto
            (* by (metis Sup_insert Un_insert_left insert_iff subset_Collect_conv) *)
        proof -
          assume a1: "insert (insert x (set l1 \<union> set l2)) (set done \<union> set todo) = ran passed"
          assume a2: "\<Union>ran passed \<subseteq> {a. reachable a \<and> \<not> empty a}"
          assume "\<forall>x\<in>set l1. \<not> Q x"
          assume a3: "Q x"
          have "reachable x \<and> \<not> empty x"
            using a2 a1 by blast
          then show "\<exists>a. reachable a \<and> \<not> empty a \<and> Q a"
            using a3 by blast
        qed

(* break inner \<longrightarrow> break outer *)
        subgoal for p l1 l2 r'
          unfolding inner_inv_def outer_inv_def
          by (metis append.assoc append_Cons append_Nil set_append)

(* finished inner \<longrightarrow> outer inv *)
        subgoal for p r'
          unfolding inner_inv_def outer_inv_def
          by clarsimp
        done

(* break outer *)
      subgoal for l1 l2 r
        unfolding outer_inv_def
        by auto

(* outer finished *)
      subgoal for r
        unfolding outer_inv_def
        apply auto
        apply (elim allE impE)
        apply (intro conjI; assumption)
        apply safe
        apply (drule Q_mono, assumption+)
        unfolding map_set_rel_def
        by auto
      done
    done
qed

thm pw_algo_map2_impl.refine_raw

schematic_goal pw_algo_map2_refine:
  "(?x, uncurry0 (PR_CONST pw_algo_map2)) \<in>
  unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a hm.hms_assn' K (lso_assn A)"
  unfolding PR_CONST_def hm.hms_assn'_id_hms_assn[symmetric] by (rule pw_algo_map2_impl.refine_raw)

sepref_register pw_algo_map2

sepref_register "PR_CONST Q"

sepref_thm check_passed_impl is
  "uncurry0 check_passed" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  supply [sepref_fr_rules] = pw_algo_map2_refine ran_of_map_impl.refine lso_id_hnr Q_refine
  using pure_K left_unique_K right_unique_K
  unfolding check_passed_def
  apply (rewrite in Q PR_CONST_def[symmetric])
  unfolding hm.hms_fold_custom_empty
  unfolding list_of_set_def[symmetric]
  by sepref

thm check_passed_impl.refine_raw

concrete_definition (in -) check_passed_impl
  uses Worklist_Map2_Impl_check.check_passed_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"

thm check_passed_impl.refine

lemma check_passed_impl_hnr:
    "(uncurry0 (check_passed_impl succsi a\<^sub>0i Fi Lei emptyi keyi copyi tracei Qi),
      uncurry0 (RETURN (\<exists>a. reachable a \<and> \<not> empty a \<and> Q a)))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    using
      check_passed_impl.refine[
        OF Worklist_Map2_Impl_check_axioms,
        FCOMP check_passed_correct[THEN Id_SPEC_refine, THEN nres_relI]
        ]
    by (simp add: RETURN_def)

end


subsection \<open>Complete Deadlock Checker\<close>

paragraph \<open>Miscellaneous Properties\<close>

context E_From_Op_Bisim
begin

text \<open>More general variant of @{thm E_from_op_reachability_check} *)\<close>
theorem E_from_op_reachability_check:
  assumes "\<And>a b. P a \<Longrightarrow> a \<sim> b \<Longrightarrow> wf_state a \<Longrightarrow> wf_state b \<Longrightarrow> P b"
  shows
  "(\<exists>l' D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> P (l', D')) \<longleftrightarrow> (\<exists>l' D'. E_from_op\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> P (l', D'))"
  by (rule E_E\<^sub>1_steps_equiv[OF E_E_from_op_step E_from_op_E_step E_from_op_wf_state];
     (assumption | rule assms))

end

context Regions_TA
begin

lemma check_deadlock_anti_mono:
  "check_deadlock l Z" if "check_deadlock l Z'" "Z \<subseteq> Z'"
  using that unfolding check_deadlock_def by auto

lemma global_clock_numbering:
  "global_clock_numbering A v n"
  using valid_abstraction clock_numbering_le clock_numbering by blast

text \<open>Variant of @{thm bisim} without emptiness.\<close>
lemma bisim:
  "Bisimulation_Invariant
  (\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle>)
  (\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle>)
  (\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>)
  (\<lambda> _. True) (\<lambda> (l, D). valid_dbm D)"
proof (standard, goal_cases)
  \<comment> \<open>\<open>\<beta> \<Rightarrow> \<N>\<close>\<close>
  case (1 a b a')
  then show ?case
    by (blast elim: norm_beta_complete1[OF global_clock_numbering valid_abstraction])
next
  \<comment> \<open>\<open>\<N> \<Rightarrow> \<beta>\<close>\<close>
  case (2 a a' b')
  then show ?case
    by (blast intro: norm_beta_sound''[OF global_clock_numbering valid_abstraction])
next
  \<comment> \<open>\<open>\<beta>\<close> invariant\<close>
  case (3 a b)
  then show ?case
    by simp
next
  \<comment> \<open>\<open>\<N>\<close> invariant\<close>
  case (4 a b)
  then show ?case
    by (auto intro: valid_dbm_step_z_norm''[OF global_clock_numbering valid_abstraction])
qed

lemma steps_z_beta_reaches:
  "reaches (l, Z) (l', Z')" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>" "Z' \<noteq> {}"
  using that
proof (induction "(l', Z')" arbitrary: l' Z' rule: rtranclp_induct)
  case base
  then show ?case
    by blast
next
  case (step y l'' Z'')
  obtain l' Z' where [simp]: "y = (l', Z')"
    by force
  from step.prems step.hyps(2) have "Z' \<noteq> {}"
    by (clarsimp simp: step_z_beta'_empty)
  from step.prems step.hyps(3)[OF \<open>y = _\<close> this] step.hyps(2) show ?case
    including graph_automation_aggressive by auto
qed

lemma reaches_steps_z_beta_iff:
  "reaches (l, Z) (l', Z') \<longleftrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}" if "Z \<noteq> {}"
  apply safe
  subgoal
    including graph_automation_aggressive by (induction rule: rtranclp_induct) auto
  using that by (auto dest: steps_z_beta_reaches elim: rtranclp.cases)

end

lemma dbm_int_init_dbm:
  "dbm_int (curry init_dbm) n"
  unfolding init_dbm_def by auto

context Reachability_Problem
begin

lemma wf_dbm_canonical'D:
  "Deadlock.canonical' n (curry (conv_M D))" if "wf_dbm D"
  using that unfolding wf_dbm_def Deadlock.canonical'_def check_diag_conv_M_iff by simp

lemma subsumes_dbm_subsetD:
  "dbm_subset n M M'" if "subsumes n (l, M) (l', M')" "\<not> check_diag n M"
  using that by (cases "l = l'") (auto simp: subsumes_simp_1 subsumes_simp_2)

lemma subsumes_loc_eqD:
  "l = l'" if "subsumes n (l, M) (l', M')" "\<not> check_diag n M"
  using that by (cases "l = l'") (auto simp: subsumes_simp_1 subsumes_simp_2)

lemma init_dbm_zone:
  "[curry (init_dbm :: real DBM')]\<^bsub>v,n\<^esub> = {u. \<forall>c\<in>{1..n}. u c = 0}"
  using init_dbm_semantics by blast

lemma not_check_deadlock_mono:
  "case a of (l, M) \<Rightarrow> \<not> TA.check_deadlock l (dbm.zone_of (curry (conv_M M))) \<Longrightarrow>
   a \<sim> b \<Longrightarrow> wf_state a \<Longrightarrow> wf_state b \<Longrightarrow>
  case b of (l, M) \<Rightarrow> \<not> TA.check_deadlock l (dbm.zone_of (curry (conv_M M)))"
  unfolding TA.check_deadlock_def state_equiv_def dbm_equiv_def by auto

lemma not_check_deadlock_non_empty:
  "Z \<noteq> {}" if "\<not> TA.check_deadlock l Z"
  using that unfolding TA.check_deadlock_def by auto

end (* Reachability Problem *)

context Reachability_Problem_Impl
begin

lemma op_E_from_op_iff:
  "op.E_from_op = E_op''.E_from_op"
  unfolding PR_CONST_def ..

lemma reachable_states:
  "l \<in> states" if "E_op''.reachable (l, M)"
  using that unfolding E_op''.reachable_def
  by (induction "(l, M)" arbitrary: l M; force simp: a\<^sub>0_def state_set_def E_op''.E_from_op_def)

lemma E_op''_states:
  "l' \<in> states" if "E_op''.E_from_op (l, M) (l', M')" "l \<in> states"
  using that by (force simp: a\<^sub>0_def state_set_def E_op''.E_from_op_def)

subsubsection \<open>Instantiating the Checker Algorithm\<close>

corollary check_deadlock_dbm_correct':
  assumes "l \<in> states" "wf_state (l, M)"
  shows "TA.check_deadlock l (dbm.zone_of (curry (conv_M M))) = check_deadlock_dbm l M"
  apply (rule check_deadlock_dbm_correct)
  using assms
  unfolding wf_state_def Deadlock.canonical'_def prod.case
    apply (blast dest: wf_dbm_altD)
   apply (rule assms)
  using assms
  unfolding wf_state_def Deadlock.canonical'_def prod.case
  apply -
  apply (drule wf_dbm_altD(1))
  unfolding canonical'_conv_M_iff check_diag_conv_M_iff by simp

corollary check_deadlock_dbm_correct'':
  assumes "E_op''.reachable (l, M)"
  shows "TA.check_deadlock l (dbm.zone_of (curry (conv_M M))) = check_deadlock_dbm l M"
  using assms
  apply -
  apply (rule check_deadlock_dbm_correct')
   apply (erule reachable_states)
  unfolding E_op''.reachable_def wf_state_def prod.case apply (erule E_op''.reachable_wf_dbm)
  done

lemma not_check_deadlock_non_empty:
  "Z \<noteq> {}" if "\<not> TA.check_deadlock l Z"
  using that unfolding TA.check_deadlock_def by auto

sepref_register check_deadlock_dbm :: "'s \<Rightarrow> int DBMEntry i_mtx \<Rightarrow> bool"

sepref_definition check_deadlock_neg_impl is
  "RETURN o (\<lambda>(l, M). \<not> check_deadlock_dbm l M)" ::
  "(location_assn \<times>\<^sub>a mtx_assn n)\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  supply [sepref_fr_rules] = check_deadlock_impl.refine
  by sepref

lemma not_check_deadlock_mono:
  "case a of (l, M) \<Rightarrow> \<not> TA.check_deadlock l (dbm.zone_of (curry (conv_M M))) \<Longrightarrow>
   a \<sim> b \<Longrightarrow> wf_state a \<Longrightarrow> wf_state b \<Longrightarrow>
  case b of (l, M) \<Rightarrow> \<not> TA.check_deadlock l (dbm.zone_of (curry (conv_M M)))"
  unfolding TA.check_deadlock_def state_equiv_def dbm_equiv_def by auto

lemma not_check_deadlock_compatible:
  assumes
    "(case a of (l, Z) \<Rightarrow> \<lambda>(l', D'). l' = l \<and> dbm.zone_of (curry (conv_M D')) = Z) b"
   "case b of (l, M) \<Rightarrow> l \<in> states \<and> wf_state (l, M)"
 shows
   "(case a of (l, Z) \<Rightarrow> \<not> TA.check_deadlock l Z) = (case b of (l, M) \<Rightarrow> \<not> check_deadlock_dbm l M)"
  using assms by (auto simp: check_deadlock_dbm_correct'[symmetric])

lemma deadlock_check_diag:
  "\<not> check_diag n M" if "\<not> check_deadlock_dbm l M" "op.reaches a\<^sub>0 (l, M)"
  using that(1)
  apply (subst (asm) check_deadlock_dbm_correct'[symmetric])
  subgoal
    using E_op''.reachable_def reachable_states that(2) by auto
  subgoal
    unfolding wf_state_def using op.reachable_wf_dbm[OF that(2)] by simp
  using canonical_check_diag_empty_iff by (blast dest: not_check_deadlock_non_empty)

(* XXX Duplication *)
lemma norm_final_bisim:
  "Bisimulation_Invariant
     (\<lambda>(l, D) (l', D'). \<exists>a. step_z_norm'' (conv_A A) l D a l' D')
     E_op''.E_from_op
     (\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y) wf_state"
  by (rule
    Bisimulation_Invariant_sim_replace[OF
      Bisimulation_Invariant_composition[OF
        step_z_norm''_step_impl'_equiv[unfolded step_impl'_E] E_op''.E_from_op_bisim
      ]
    ])
    (auto simp add: state_equiv_def dbm_equiv_def)

interpretation bisim:
  Bisimulation_Invariant
  "\<lambda>(l, Z) (l', Z'). step_z_beta' (conv_A A) l Z l' Z'"
  "\<lambda>a b. op.E_from_op a b"
  "\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z"
  "\<lambda>_. True" "\<lambda>(l, M). l \<in> states \<and> wf_state (l, M)"
  unfolding op_E_from_op_iff
  thm TA.bisim Bisimulation_Invariant_strengthen_post'
Bisimulation_Invariant_composition[OF TA.bisim norm_final_bisim]
norm_final_bisim
  by (rule Bisimulation_Invariant_strengthen_post',
      (rule Bisimulation_Invariant_composition[OF TA.bisim norm_final_bisim]
        Bisimulation_Invariant_sim_replace
        )+) (auto 4 3 dest: E_op''_states wf_dbm_D(3) simp: wf_state_def)

context
  assumes l\<^sub>0_in_A: "l\<^sub>0 \<in> Simulation_Graphs_TA.state_set A"
begin

interpretation TA:
  Regions_TA_Start_State v n "Suc n" "{1..<Suc n}" k "conv_A A" l\<^sub>0 "{u. \<forall>c\<in>{1..n}. u c = 0}"
  apply standard
  subgoal
    by (intro l\<^sub>0_state_set l\<^sub>0_in_A)
  subgoal
    unfolding V'_def
    apply safe
    subgoal for x
      unfolding V_def by auto
    apply (inst_existentials "curry init_dbm :: real DBM")
     apply (simp add: init_dbm_zone)
    by (rule dbm_int_init_dbm)
  subgoal
    by auto
  done

lemmas beta_final_bisim = bisim.Bisimulation_Invariant_axioms

lemma check_deadlock:
  "(\<exists>a. op.reachable a \<and>
    \<not> (case a of (l, M) \<Rightarrow> check_diag n M) \<and> (case a of (l, M) \<Rightarrow> \<not> check_deadlock_dbm l M))
  \<longleftrightarrow> (\<exists>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<and> deadlock (l\<^sub>0, u\<^sub>0))" (is "?l \<longleftrightarrow> ?r")
proof -
  text \<open>@{term TA.reaches} corresponds to (non-empty) steps of @{term step_z_beta'}\<close>
  text \<open>@{term Standard_Search_Space.reaches} corresponds to steps of @{term E}\<close>
  text \<open>@{term op.reaches} corresponds to steps of @{term op.E_from_op} (@{term E_op''})\<close>
  have "?r \<longleftrightarrow> (\<exists>l Z. TA.reaches (l\<^sub>0, {u. \<forall>c\<in>{1..n}. u c = 0}) (l, Z) \<and> \<not>TA.check_deadlock l Z)"
    using TA.deadlock_check unfolding TA.a\<^sub>0_def from_R_def by simp
  also have
    "\<dots> \<longleftrightarrow> (\<exists>l Z. bisim.A.reaches (l\<^sub>0, {u. \<forall>c\<in>{1..n}. u c = 0}) (l, Z) \<and> \<not>TA.check_deadlock l Z)"
    apply safe
    subgoal for l Z
      by (subst (asm) TA.reaches_steps_z_beta_iff) auto
    subgoal for l Z
      by (subst TA.reaches_steps_z_beta_iff) (auto dest: not_check_deadlock_non_empty)
    done
  also have "\<dots> \<longleftrightarrow> (\<exists>l M. op.reaches a\<^sub>0 (l, M) \<and> \<not> check_deadlock_dbm l M)"
    using bisim.reaches_ex_iff[where
        \<phi> = "\<lambda> (l, Z). \<not>TA.check_deadlock l Z" and \<psi> = "\<lambda>(l, M). \<not> check_deadlock_dbm l M",
        OF not_check_deadlock_compatible
        ]
    using wf_state_init init_dbm_zone unfolding a\<^sub>0_def by clarsimp
  also have "\<dots> \<longleftrightarrow> ?l"
    unfolding op.reachable_def by (auto 4 4 dest: deadlock_check_diag)
  finally show ?thesis ..
qed

lemma check_deadlock':
  "(\<nexists>a. op.reachable a \<and>
    \<not> (case a of (l, M) \<Rightarrow> check_diag n M) \<and> (case a of (l, M) \<Rightarrow> \<not> check_deadlock_dbm l M))
  \<longleftrightarrow> (\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0))" (is "?l \<longleftrightarrow> ?r")
  using check_deadlock by auto

context
  assumes "F = (\<lambda> _. False)"
begin

print_locale Worklist_Map2_Impl_check
term K

interpretation Worklist_Map2_Impl_check
  op.E_from_op a\<^sub>0 F_rel "subsumes n" succs "\<lambda> (l, M). check_diag n M" subsumes'
  "\<lambda> (l, M). F l" state_assn'
  succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl fst "return o fst" state_copy_impl
  tracei location_assn "\<lambda>(l, M). \<not> check_deadlock_dbm l M" check_deadlock_neg_impl
  apply standard
  subgoal
    using check_deadlock_neg_impl.refine unfolding PR_CONST_def .
  subgoal
    unfolding F_rel_def unfolding \<open>F = _\<close> by auto
  subgoal for a b
    apply clarsimp
    apply (subst (asm) check_deadlock_dbm_correct''[symmetric], assumption)
    apply (subst (asm) check_deadlock_dbm_correct''[symmetric], assumption)
    apply (frule subsumes_loc_eqD, assumption)
    apply (drule subsumes_dbm_subsetD, assumption)
    apply (drule dbm_subset_conv)
    apply (subst (asm) dbm_subset_correct''[symmetric])
    by (auto dest: TA.check_deadlock_anti_mono E_op''.reachable_wf_dbm simp: E_op''.reachable_def)
  done

lemmas check_passed_impl_hnr = check_passed_impl_hnr[unfolded check_deadlock]

end (* F is always false *)

end (* l\<^sub>0 belongs to A *)

definition
  "is_start_in_states = (trans_fun l\<^sub>0 \<noteq> [])"

lemma is_start_in_states:
  "l\<^sub>0 \<in> Simulation_Graphs_TA.state_set A" if "is_start_in_states"
proof -
  from that obtain g a r l' where "(g, a, r, l') \<in> set (trans_fun l\<^sub>0)"
    by (cases "hd (trans_fun l\<^sub>0)" rule: prod_cases4)
       (auto dest: hd_in_set simp: is_start_in_states_def)
  from trans_impl_trans_of[OF this] have "A \<turnstile> l\<^sub>0 \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    by simp
  then show ?thesis
    unfolding Simulation_Graphs_TA.state_set_def trans_of_def by auto
qed

lemma deadlocked_if_not_is_start_in_states:
  "deadlocked (l\<^sub>0, Z\<^sub>0)" if "\<not> is_start_in_states"
proof -
  have *: False if "A \<turnstile> l\<^sub>0 \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" for g a r l'
    using trans_of_trans_impl[OF that] \<open>\<not> _\<close> unfolding is_start_in_states_def by auto
  { fix l g2 a2 r2 l' assume A: "conv_A A \<turnstile> l \<longrightarrow>\<^bsup>g2,a2,r2\<^esup> l'"
    obtain g1 a1 r1 where **: "A \<turnstile> l \<longrightarrow>\<^bsup>g1,a1,r1\<^esup> l'"
      using A unfolding trans_of_def by (cases A) force
    then have "\<exists> g1 a1 r1. A \<turnstile> l \<longrightarrow>\<^bsup>g1,a1,r1\<^esup> l'"
      by auto
  } note ** = this (* XXX Better proof *)
  show ?thesis
    unfolding deadlocked_def
    apply (rule ccontr)
    apply clarsimp
    apply (cases rule: step'.cases, assumption)
    apply (cases rule: step_a.cases, assumption)
    apply (auto 4 3 elim: * dest: ** step_delay_loc)
    done
qed

lemma deadlock_if_not_is_start_in_states:
  "deadlock (l\<^sub>0, Z\<^sub>0)" if "\<not> is_start_in_states"
  unfolding deadlock_def using deadlocked_if_not_is_start_in_states[OF that] by blast

sepref_definition is_start_in_states_impl is
  "uncurry0 (RETURN is_start_in_states)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding is_start_in_states_def by sepref

(* lemmas [sepref_fr_rules] = check_passed_impl_hnr *)

thm check_passed_impl_hnr

thm is_start_in_states_impl.refine[to_hnr, unfolded hn_refine_def, simplified]

lemma is_start_in_states_impl_hoare:
  "<emp> is_start_in_states_impl
   <\<lambda>r. \<up> ((r \<longrightarrow> l\<^sub>0 \<in> Simulation_Graphs_TA.state_set A)
         \<and> (\<not>r \<longrightarrow> deadlocked (l\<^sub>0, \<lambda>_ . 0))
   )>\<^sub>t"
  by (sep_auto
      intro: deadlocked_if_not_is_start_in_states
      simp: mod_star_conv is_start_in_states[simplified]
      heap: is_start_in_states_impl.refine[to_hnr, unfolded hn_refine_def, simplified]
      )

(* XXX Move *)
lemma deadlock_if_deadlocked:
  "deadlock y" if "deadlocked y"
  using that unfolding deadlock_def by (inst_existentials y) auto

lemma is_start_in_states_impl_hoare':
  "<emp> is_start_in_states_impl
   <\<lambda>r. \<up> ((r \<longrightarrow> l\<^sub>0 \<in> Simulation_Graphs_TA.state_set A)
         \<and> (\<not>r \<longrightarrow> (\<exists>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<and> deadlock (l\<^sub>0, u\<^sub>0)))
   )>\<^sub>t"
  by (rule cons_post_rule[OF is_start_in_states_impl_hoare]) (auto intro: deadlock_if_deadlocked)

definition
  "check_passed_impl_start \<equiv> do {
    r1 \<leftarrow> is_start_in_states_impl;
    if r1 then do {
      r2 \<leftarrow> check_passed_impl succs_impl a\<^sub>0_impl F_impl subsumes_impl emptiness_check_impl
            (return \<circ> fst) state_copy_impl tracei check_deadlock_neg_impl;
             return r2
    }
    else return True
  }"

lemma check_passed_impl_start_hnr:
  "(uncurry0 check_passed_impl_start,
    uncurry0 (RETURN (\<exists>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<and> deadlock (l\<^sub>0, u\<^sub>0)))
  ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn" if "F = (\<lambda>_. False)"
proof -
  define has_deadlock where "has_deadlock \<equiv> \<exists>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<and> deadlock (l\<^sub>0, u\<^sub>0)"
  note [sep_heap_rules] =
    check_passed_impl_hnr[OF _ that, to_hnr, unfolded hn_refine_def, folded has_deadlock_def, simplified]
    is_start_in_states_impl_hoare'[folded has_deadlock_def, simplified]
  show ?thesis
    unfolding has_deadlock_def[symmetric] check_passed_impl_start_def
    by sepref_to_hoare (sep_auto simp: mod_star_conv)
qed

end (* Reachability Problem Impl *)


context Reachability_Problem_precompiled
begin

lemma F_is_False_iff:
  "PR_CONST F = (\<lambda>_. False) \<longleftrightarrow> final = []"
  unfolding F_def by (cases final; simp; metis)

lemma F_impl_False: "F_impl = (\<lambda>_. return False)" if "final = []"
  using that unfolding F_impl_def unfolding final_fun_def List.member_def by auto

definition deadlock_checker where
  "deadlock_checker \<equiv>
    let
      key = return \<circ> fst;
      sub = subsumes_impl;
      copy = state_copy_impl;
      start = a\<^sub>0_impl;
      final = (\<lambda>_. return False);
      succs = succs_impl;
      empty = emptiness_check_impl;
      P = check_deadlock_neg_impl;
      trace = tracei
    in do {
      r1 \<leftarrow> is_start_in_states_impl;
      if r1 then do {
        r2 \<leftarrow> check_passed_impl succs start final sub empty key copy trace P;
        return r2
      }
      else return True
    }"

theorem deadlock_checker_hnr:
  assumes "final = []"
  shows
    "(uncurry0 deadlock_checker, uncurry0 (RETURN (\<exists>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<and> deadlock (0, u\<^sub>0))))
     \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding deadlock_checker_def Let_def
  using check_passed_impl_start_hnr[
      unfolded F_is_False_iff F_impl_False[OF assms] check_passed_impl_start_def,
      OF assms] .

ML \<open>
    fun pull_let ctxt u t =
      let
        val t1 = abstract_over (u, t);
        val r1 = Const (@{const_name "HOL.Let"}, dummyT) $ u $ Abs ("I", dummyT, t1);
        val ct1 = Syntax.check_term ctxt r1;
        val g1 =
          Goal.prove ctxt [] [] (Logic.mk_equals (t, ct1))
          (fn {context, ...} => EqSubst.eqsubst_tac context [0] [@{thm Let_def}] 1
          THEN resolve_tac context [@{thm Pure.reflexive}] 1)
      in g1 end;

    fun get_rhs thm =
      let
        val Const ("Pure.eq", _) $ _ $ r = Thm.full_prop_of thm
      in r end;

    fun get_lhs thm =
      let
        val Const ("Pure.imp", _) $ (Const ("Pure.eq", _) $ l $ _) $ _ = Thm.full_prop_of thm
      in l end;

    fun pull_tac' u ctxt thm =
      let
        val l = get_lhs thm;
        val rewr = pull_let ctxt u l;
      in Local_Defs.unfold_tac ctxt [rewr] thm end;

    fun pull_tac u ctxt = SELECT_GOAL (pull_tac' u ctxt) 1;
  \<close>

schematic_goal deadlock_checker_alt_def:
  "deadlock_checker \<equiv> ?impl"
  unfolding deadlock_checker_def
  unfolding succs_impl_def
  unfolding E_op''_impl_def abstr_repair_impl_def abstra_repair_impl_def
  unfolding
    start_inv_check_impl_def unbounded_dbm_impl_def unbounded_dbm'_def
    unbounded_dbm_def
  unfolding check_deadlock_neg_impl_def check_deadlock_impl_def
  unfolding is_start_in_states_impl_def
   apply (abstract_let "IArray.sub (IArray (map (IArray o map int) k))" k)
   apply (abstract_let "inv_fun" inv_fun)
   apply (abstract_let "trans_impl" trans)
   unfolding inv_fun_def[abs_def] trans_impl_def[abs_def]
   apply (abstract_let "IArray inv" inv_ia)
   apply (abstract_let "IArray trans_map" trans_map)
   unfolding trans_map_def label_def
   unfolding init_dbm_impl_def a\<^sub>0_impl_def
   unfolding subsumes_impl_def
   unfolding emptiness_check_impl_def
   unfolding state_copy_impl_def
  by (rule Pure.reflexive)

end (* Reachability Problem Precompiled *)

concrete_definition deadlock_checker_impl
  uses Reachability_Problem_precompiled.deadlock_checker_alt_def

export_code deadlock_checker_impl in SML_imp module_name TA

definition [code]:
  "check_deadlock n m k I T \<equiv>
    if Reachability_Problem_precompiled n m k I T
    then deadlock_checker_impl m k I T \<bind> (\<lambda>x. return (Some x))
    else return None"

theorem deadlock_check:
  "(uncurry0 (check_deadlock n m k I T),
    uncurry0 (
       RETURN (
        if (Reachability_Problem_precompiled n m k I T)
        then Some (
            if
              \<exists> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<and>
              Graph_Defs.deadlock
                (\<lambda>(l, u) (l', u').
                    (conv_A (Reachability_Problem_precompiled_defs.A n I T)) \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
                (0, u\<^sub>0)
            then True
            else False
          )
        else None
       )
    )
   ) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
proof -
  define reach_check where
    "reach_check =
    (\<exists> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<and>
              Graph_Defs.deadlock
            (\<lambda>(l, u) (l', u').
                (conv_A (Reachability_Problem_precompiled_defs.A n I T)) \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
            (0, u\<^sub>0))"
  note [sep_heap_rules] = Reachability_Problem_precompiled.deadlock_checker_hnr[OF _ HOL.refl,
      to_hnr, unfolded hn_refine_def, rule_format,
      of n m k I T,
      unfolded reach_check_def[symmetric]
      ]
  show ?thesis
    unfolding reach_check_def[symmetric]
    by sepref_to_hoare
       (sep_auto simp: deadlock_checker_impl.refine[symmetric] mod_star_conv check_deadlock_def)
qed


paragraph \<open>Standard Deadlock Checker Implementation\<close>
context Reachability_Problem_Impl
begin

definition deadlock_checker where
  "deadlock_checker \<equiv>
    let
      key = return \<circ> fst;
      sub = subsumes_impl;
      copy = state_copy_impl;
      start = a\<^sub>0_impl;
      final = (\<lambda>_. return False);
      succs = succs_impl;
      empty = emptiness_check_impl;
      P = check_deadlock_neg_impl;
      trace = tracei
    in do {
      r1 \<leftarrow> is_start_in_states_impl;
      if r1 then do {
        r2 \<leftarrow> check_passed_impl succs start final sub empty key copy trace P;
        return r2
      }
      else return True
    }
    "

interpretation ta_bisim: Bisimulation_Invariant
  "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(l, u) (l', u'). l' = l \<and> (\<forall> c. c \<in> clk_set (conv_A A) \<longrightarrow> u c = u' c))"
  "(\<lambda>_. True)" "(\<lambda>_. True)"
  by (rule ta_bisimulation[of "conv_A A"])

lemma deadlock_zero_clock_val_iff:
  "(\<exists>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<and> deadlock (l\<^sub>0, u\<^sub>0)) \<longleftrightarrow> deadlock (l\<^sub>0, \<lambda>_. 0)"
  apply safe
  subgoal for u
    using clocks_I[of "\<lambda>_. 0" u] by (subst ta_bisim.deadlock_iff; simp)
  by auto

context
  assumes F_fun_False: "\<And>x. F_fun x = False" and F_False: "F = (\<lambda>_. False)"
begin
lemma F_impl_is_False:
  "F_impl = (\<lambda>_. return False)"
  unfolding F_impl_def F_fun_False by simp

lemma deadlock_checker_correct:
  "(uncurry0 deadlock_checker, uncurry0 (Refine_Basic.RETURN (deadlock (l\<^sub>0, \<lambda>_. 0))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding
    deadlock_checker_def Let_def F_impl_is_False[symmetric]
    check_passed_impl_start_def[symmetric] deadlock_zero_clock_val_iff[symmetric]
    check_passed_impl_start_def[symmetric] deadlock_zero_clock_val_iff[symmetric]
  using check_passed_impl_start_hnr[OF F_False] .

lemmas deadlock_checker_hoare = deadlock_checker_correct[to_hnr, unfolded hn_refine_def, simplified]

end

end

end (* Theory *)