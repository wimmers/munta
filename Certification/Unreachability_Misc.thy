theory Unreachability_Misc
  imports
    Simulation_Graphs_Certification
    Worklist_Algorithms.Leadsto_Impl
    TA_Library.Printing
    TA_Library.Imperative_Loops
    TA_Library.Trace_Timing
begin

paragraph \<open>Misc\<close>

theorem (in -) arg_max_nat_lemma2:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "P k"
    and "finite (Collect P)"
  shows "P (arg_max f P) \<and> (\<forall>y. P y \<longrightarrow> f y \<le> f (arg_max f P))"
proof -
  let ?b = "Max (f ` Collect P) + 1"
  from assms(2) have "\<forall>y. P y \<longrightarrow> f y < ?b"
    by (auto intro: Max_ge le_imp_less_Suc)
  with assms(1) show ?thesis
    by (rule arg_max_nat_lemma)
qed

paragraph \<open>Misc \<open>heap\<close>\<close>

lemma hoare_triple_success:
  assumes "<P> c <Q>" and "(h, as) \<Turnstile> P"
  shows "success c h"
  using assms unfolding hoare_triple_def Let_def success_def
  by (cases "execute c h") (force simp: run.simps)+

lemma run_return: "run (return x) (Some h) (Some h) x" for h
  by (auto simp: execute_simps intro: run.regular)

lemma return_htD:
  assumes "<Q x> return x <PP>"
  shows "Q x \<Longrightarrow>\<^sub>A PP x"
  using assms unfolding hoare_triple_def Let_def by (force intro: run_return entailsI)

definition run_heap :: "'a Heap \<Rightarrow> 'a" where
  "run_heap h = fst (the (execute h Heap.empty))"

code_printing constant run_heap \<rightharpoonup> (SML) "(fn f => f ()) _"
code_printing constant run_heap \<rightharpoonup> (OCaml) "(fun f -> f ()) _"

definition run_map_heap :: "('a \<Rightarrow> 'b Heap) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "run_map_heap f xs = map (run_heap o f) xs"

lemma hoare_triple_executeD:
  assumes "<emp> c <\<lambda>r. \<up>(P r)>\<^sub>t"
  shows "P (fst (the (execute c h)))"
proof -
  have "(h, {}) \<Turnstile> emp"
    by simp
  with assms(1) have "success c h"
    by (rule hoare_triple_success)
  then obtain r h' where "execute c h = Some (r, h')"
    unfolding success_def by auto
  then have "run c (Some h) (Some h') r"
    by (intro regular) auto
  with \<open>execute c h = _\<close> show ?thesis
    using assms unfolding hoare_triple_def by (force intro: mod_emp_simp)
qed

lemma hoare_triple_run_heapD:
  assumes "<emp> c <\<lambda>r. \<up>(P r)>\<^sub>t"
    shows "P (run_heap c)"
  using hoare_triple_executeD[OF assms] unfolding run_heap_def .

lemma list_all2_conjI:
  assumes "list_all2 P as bs" "list_all2 Q as bs"
    shows "list_all2 (\<lambda>a b. P a b \<and> Q a b) as bs"
  using assms unfolding list_all2_conv_all_nth by auto

lemma hoare_triple_run_map_heapD:
  assumes "list_all (\<lambda>x. <emp> c x <\<lambda>r. \<up>(P x r)>\<^sub>t) xs"
    shows "list_all2 P xs (run_map_heap c xs)"
  using assms unfolding run_map_heap_def list_all2_map2 list.pred_rel
  by (elim list_all2_mono) (auto simp: eq_onp_def intro: hoare_triple_run_heapD)

lemma hoare_triple_run_map_heapD':
  assumes "list_all2 (\<lambda>x xi. <emp> c xi <\<lambda>r. \<up>(P x r)>\<^sub>t) xs xsi"
    shows "list_all2 P xs (run_map_heap c xsi)"
  using assms unfolding run_map_heap_def list_all2_map2 list.pred_rel
  by (elim list_all2_mono) (auto simp: eq_onp_def intro: hoare_triple_run_heapD)

definition
  "parallel_fold_map = Heap_Monad.fold_map"


(* definition
  "ht_refine \<Gamma> c \<Gamma>' R m \<equiv> nofail m \<and> (\<forall>h. success  \<longrightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up> (RETURN x \<le> m))>\<^sub>t" *)



paragraph \<open>Misc \<open>nres\<close>\<close>

lemma no_fail_RES_bindI:
  assumes "\<And>x. x \<in> S \<Longrightarrow> nofail (f x)"
  shows "nofail (RES S \<bind> f)"
  using assms pw_RES_bind_choose(1) by blast

lemma nfoldli_ub_RES_rule:
  assumes "\<And>x s. x \<in> set xs \<Longrightarrow> s \<in> S \<Longrightarrow> f x s \<le> RES S" "s \<in> S"
  shows "nfoldli xs c f s \<le> RES S"
  using assms
  by (induction xs arbitrary: s; simp; metis (no_types) inres_simps(2) pw_bind_le_iff pw_le_iff)

lemma nfoldli_ub_rule:
  assumes "\<And>x s. x \<in> set xs \<Longrightarrow> inres ub s \<Longrightarrow> f x s \<le> ub" "inres ub s"
  shows "nfoldli xs c f s \<le> ub"
  using nfoldli_ub_RES_rule assms by (metis inres_def nofail_RES_conv nres_order_simps(21) pw_leI')

lemma nfoldli_nofail_rule:
  assumes "\<And>x s. x \<in> set xs \<Longrightarrow> inres ub s \<Longrightarrow> f x s \<le> ub" "inres ub s" "nofail ub"
  shows "nofail (nfoldli xs c f s)"
  using assms by - (erule pwD1[rotated], rule nfoldli_ub_rule)

lemma SUCCEED_lt_RES_iff[simp]:
  "SUCCEED < RES S \<longleftrightarrow> S \<noteq> {}"
  unfolding bot_nres_def by (subst less_nres.simps) auto

lemma SUCCEED_lt_RETURN[intro, simp]:
  "SUCCEED < RETURN x"
  unfolding RETURN_def by simp

lemma SUCCEED_lt_FAIL[intro, simp]:
  "SUCCEED < FAIL"
  unfolding bot_nres_def top_nres_def by (subst less_nres.simps) auto

lemma bind_RES_gt_SUCCEED_I:
  assumes "\<And>s. f s > SUCCEED" "S \<noteq> {}"
  shows "do {x \<leftarrow> RES S; f x} > SUCCEED"
  by (metis RES_bind_choose assms(1) assms(2) le_less preorder_class.less_le_not_le set_notEmptyE)


paragraph \<open>Monadic \<open>list_all\<close> and \<open>list_ex\<close>\<close>

definition
  "monadic_list_all P xs \<equiv> nfoldli xs id (\<lambda>x _. P x) True"

text \<open>Debug version\<close>
definition
  "monadic_list_all_fail P xs \<equiv>
      nfoldli xs (\<lambda>x. x = None) (\<lambda>x _. do {b \<leftarrow> P x; RETURN (if b then None else Some x)}) None"

lemma monadic_list_all_fail_alt_def:
  "monadic_list_all_fail P xs =
      nfoldli xs (\<lambda>x. x = None) (\<lambda>x _. do {
        b \<leftarrow> P (COPY x); if b then RETURN None else RETURN (Some x)}) None"
  unfolding monadic_list_all_fail_def
  apply (intro arg_cong2[where f = "nfoldli xs (\<lambda>x. x = None)"] ext)
apply simp
  apply (rule bind_cong)
    apply auto
  done

definition
  "monadic_list_all_fail' P xs \<equiv>
    nfoldli xs (\<lambda>x. x = None) (\<lambda>x _. do {
      r \<leftarrow> P x; RETURN (case r of None \<Rightarrow> None | Some r \<Rightarrow> Some r)})
    None"

lemma monadic_list_all_fail'_alt_def:
  "monadic_list_all_fail' P xs =
    nfoldli xs (\<lambda>x. x = None) (\<lambda>x _. do {
      r \<leftarrow> P x; case r of None \<Rightarrow> RETURN None | Some r \<Rightarrow> RETURN (Some r)})
    None"
  unfolding monadic_list_all_fail'_def
  apply (intro arg_cong2[where f = "nfoldli xs (\<lambda>x. x = None)"] ext)
   apply simp
   apply (rule bind_cong)
    apply (auto split: option.splits)
  done

lemma monadic_list_all_fail_monadic_list_all_fail':
  "monadic_list_all_fail P xs =
   monadic_list_all_fail' (\<lambda>x. do {b \<leftarrow> P x; RETURN (if b then None else Some x)}) xs"
  unfolding monadic_list_all_fail_def monadic_list_all_fail'_def
  apply (intro arg_cong2[where f = "nfoldli xs (\<lambda>x. x = None)"] ext)
   apply simp
  apply (rule bind_cong)
    apply auto
  done

lemma monadic_list_all_rule:
  assumes "\<And>x. Pi x \<le> SPEC (\<lambda>r. r = P x)"
  shows "monadic_list_all Pi xs \<le> SPEC (\<lambda>r. r \<longleftrightarrow> list_all P xs)"
  using assms unfolding monadic_list_all_def
  by (intro nfoldli_rule[where I = "\<lambda>as bs b. b = list_all P as \<and> set (as @ bs) = set xs"]) auto

definition
  "monadic_list_ex P xs \<equiv> nfoldli xs Not (\<lambda>x _. P x) False"

lemma monadic_list_ex_rule:
  assumes "\<And>x. Pi x \<le> SPEC (\<lambda>r. r = P x)"
  shows "monadic_list_ex Pi xs \<le> SPEC (\<lambda>r. r \<longleftrightarrow> list_ex P xs)"
  using assms unfolding monadic_list_ex_def
  by (intro nfoldli_rule[where I = "\<lambda>as bs b. b = list_ex P as \<and> set (as @ bs) = set xs"]) auto

lemma monadic_list_ex_empty[simp]:
  "monadic_list_ex P [] = RETURN False"
  unfolding monadic_list_ex_def by simp

lemma monadic_list_all_empty[simp]:
  "monadic_list_all P [] = RETURN True"
  unfolding monadic_list_all_def by simp

lemma monadic_list_all_False: "monadic_list_all (\<lambda>x. RETURN False) xs = RETURN (xs = [])"
  by (cases xs) (auto simp: monadic_list_all_def)

lemma monadic_list_all_RETURN:
  "monadic_list_all (\<lambda>x. RETURN (P x)) xs = RETURN (list_all P xs)"
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  then show ?case
    by (cases "P x") (auto simp: monadic_list_all_def)
qed

lemma monadic_list_ex_RETURN:
  "monadic_list_ex (\<lambda>x. RETURN (P x)) xs = RETURN (list_ex P xs)"
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  then show ?case
    by (cases "P x") (auto simp: monadic_list_ex_def)
qed

lemma monadic_list_ex_RETURN_mono:
  assumes "set xs = set ys"
  shows "monadic_list_ex (\<lambda>s. RETURN (P s)) xs \<le> monadic_list_ex (\<lambda>s. RETURN (P s)) ys"
  using assms by (simp add: monadic_list_ex_RETURN list_ex_iff)

lemma monadic_list_ex_nofailI:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> nofail (f x)"
  shows "nofail (monadic_list_ex f xs)"
  using assms unfolding monadic_list_ex_def
  by - (rule nfoldli_nofail_rule[where ub = "RES UNIV"]; simp add: pw_le_iff)

lemma monadic_list_all_nofailI:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> nofail (f x)"
  shows "nofail (monadic_list_all f xs)"
  using assms unfolding monadic_list_all_def
  by - (rule nfoldli_nofail_rule[where ub = "RES UNIV"]; simp add: pw_le_iff)

context
  fixes xs and g :: "_ \<Rightarrow> bool nres"
  assumes g_gt_SUCCEED: "\<And>x. x \<in> set xs \<Longrightarrow> g x > SUCCEED"
begin

private lemma nfoldli_gt_SUCCEED: "nfoldli xs c (\<lambda>x _. g x) a > SUCCEED" for a c
  using g_gt_SUCCEED
proof (induction xs arbitrary: a)
  case (Cons x xs)
  then show ?case
    by (cases "g x"; force intro: bind_RES_gt_SUCCEED_I simp: monadic_list_all_def)
qed simp

lemma monadic_list_all_gt_SUCCEED:
  "monadic_list_all g xs > SUCCEED"
  using nfoldli_gt_SUCCEED unfolding monadic_list_all_def .

lemma monadic_list_ex_gt_SUCCEED:
  "monadic_list_ex g xs > SUCCEED"
  using nfoldli_gt_SUCCEED unfolding monadic_list_ex_def .

end (* Anonymous context *)

lemma monadic_list_ex_is_RETURN:
  "\<exists> r. monadic_list_ex (\<lambda>x. RETURN (P x)) xs = RETURN r"
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  then show ?case
    by (cases "P x") (auto simp: monadic_list_ex_def)
qed

lemma monadic_list_all_list_ex_is_RETURN:
  "\<exists>r. monadic_list_all (\<lambda>x. monadic_list_ex (\<lambda>y. RETURN (P x y)) ys) xs = RETURN r"
proof -
  let ?f = "\<lambda>x. SOME r. monadic_list_ex (\<lambda>y. RETURN (P x y)) ys = RETURN r"
  have "monadic_list_all (\<lambda>x. monadic_list_ex (\<lambda>y. RETURN (P x y)) ys) xs
      = monadic_list_all (\<lambda>x. RETURN (?f x)) xs"
    by (fo_rule arg_cong2; intro HOL.refl monadic_list_ex_is_RETURN ext someI_ex)
  then show ?thesis
    by (simp add: monadic_list_all_RETURN)
qed

lemma monadic_list_all_mono[refine_mono]:
  "monadic_list_all P xs \<le> monadic_list_all Q xs" if "\<forall> x \<in> set xs. P x \<le> Q x"
proof -
  have "nfoldli xs id (\<lambda>x _. P x) a \<le> nfoldli xs id (\<lambda>x _. Q x) a" for a
    using that by (induction xs arbitrary: a; clarsimp; refine_mono)
  then show ?thesis
    unfolding monadic_list_all_def .
qed

lemma monadic_list_ex_mono[refine_mono]:
  "monadic_list_ex P xs \<le> monadic_list_ex Q xs" if "\<forall> x \<in> set xs. P x \<le> Q x"
proof -
  have "nfoldli xs Not (\<lambda>x _. P x) a \<le> nfoldli xs Not (\<lambda>x _. Q x) a" for a
    using that by (induction xs arbitrary: a; clarsimp; refine_mono)
  then show ?thesis
    unfolding monadic_list_ex_def .
qed


paragraph \<open>Abstract \<open>nres\<close> algorithm\<close>

context Reachability_Invariant_paired_defs
begin

context
  fixes P :: "('l \<times> 's) \<Rightarrow> bool"
begin

definition "check_prop \<equiv>
do {
  xs \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l. do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST M l);
    monadic_list_all (\<lambda>s. RETURN (PR_CONST P (l, s))) xs
  }
  ) xs
}"

lemma check_prop_correct:
  "check_prop \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<forall>l \<in> L. \<forall>s \<in> M l. P (l, s)))"
  unfolding check_prop_def
  by (refine_vcg monadic_list_all_rule monadic_list_ex_rule) (auto simp: list_all_iff)

end

end


locale Reachability_Impl_base =
  Unreachability_Invariant_paired_pre_defs where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes succs :: "'l \<Rightarrow> 's set \<Rightarrow> ('l \<times> 's set) list"
  assumes succs_correct:
    "\<And>l. \<forall>s \<in> xs. P (l, s)
  \<Longrightarrow> {(l', s')| l' ys s'. (l', ys) \<in> set (succs l xs) \<and> s' \<in> ys}
    = (\<Union> s \<in> xs. Collect (E (l, s)))"

locale Reachability_Impl_invariant =
  Reachability_Impl_base where E = E +
  Unreachability_Invariant_paired_defs where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

definition "check_invariant L' \<equiv>
do {
  monadic_list_all (\<lambda>l.
  do {
    let as = M l;
    let succs = succs l as;
    monadic_list_all (\<lambda>(l', xs).
    do {
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      if xs = [] then RETURN True else do {
        b1 \<leftarrow> RETURN (l' \<in> L);
        ys \<leftarrow> SPEC (\<lambda>xs. set xs = M l');
        b2 \<leftarrow> monadic_list_all (\<lambda>x.
          monadic_list_ex (\<lambda>y. RETURN (x \<preceq> y)) ys
        ) xs;
        RETURN (b1 \<and> b2)
      }
    }
    ) succs
  }
  ) L'
}
"

definition
  "check_invariant_spec L' \<equiv>
  \<forall> l \<in> L'. \<forall> s \<in> M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')"

lemma check_invariant_correct:
  "check_invariant L' \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_spec (set L'))"
  (is "_ \<le> ?rhs")
  if assms: "\<forall>l \<in> L. \<forall>s \<in> M l. P (l, s)" "set L' \<subseteq> L"
proof -
  have *: "(\<forall> (l',ys) \<in> set (succs l xs). \<forall> s' \<in> ys. l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')) =
       (\<forall>s\<in>M l.
           \<forall>l' s'.
              E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. s' \<preceq> s''))"
    if "xs = M l" "l \<in> L"
     for l xs
    using succs_correct[of xs l] assms(1) that
    apply clarsimp
    apply safe
       apply clarsimp_all
       apply fastforce
      apply fastforce
    (* or: apply force *)
    subgoal premises prems for a b s'
    proof -
      from prems have "\<forall>s\<in>xs. P (l, s)"
        by auto
      from succs_correct[OF this] prems(3,6,7) obtain s where "s \<in> M l" "E (l, s) (a, s')"
        by fastforce
      with prems show ?thesis
        by auto
    qed
    apply fastforce
    done
  have **: "
     (\<forall> l \<in> set L'. (\<forall> (l',ys) \<in> set (succs l (M l)). \<forall> s' \<in> ys. l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')))
  =  (\<forall> l \<in> set L'. \<forall>s\<in>M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. s' \<preceq> s''))"
    by (simp add: * assms(2)[THEN subsetD])
  have "check_invariant L' \<le> SPEC (\<lambda>r. r \<longleftrightarrow>
    (\<forall> l \<in> set L'. (\<forall> (l',ys) \<in> set (succs l (M l)). (\<forall> s' \<in> ys. l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')))))"
    unfolding check_invariant_def
    by (refine_vcg monadic_list_all_rule monadic_list_ex_rule) (auto simp: list_all_iff list_ex_iff)
  also have "\<dots> \<le> ?rhs"
    unfolding check_invariant_spec_def by (auto; smt ** case_prodI2 case_prod_conv)
  finally show ?thesis .
qed

end (* Reachability Impl Invariant *)


locale Reachability_Impl_base2 =
  Reachability_Impl_base where E = E +
  Unreachability_Invariant_paired_pre_defs where E = E
  for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes P' and F
  assumes P'_P: "\<And> l s. P' (l, s) \<Longrightarrow> P (l, s)"
  assumes F_mono: "\<And>a b. P a \<Longrightarrow> F a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> s \<preceq> s') a b \<Longrightarrow> P b \<Longrightarrow> F b"


\<^cancel>\<open>locale Reachability_Impl_base2 =
  Reachability_Impl_base where E = E +
  Unreachability_Invariant_paired_pre where E = E
  for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes P' and F
  assumes P'_P: "\<And> l s. P' (l, s) \<Longrightarrow> P (l, s)"
  assumes F_mono: "\<And>a b. P a \<Longrightarrow> F a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> s \<preceq> s') a b \<Longrightarrow> P b \<Longrightarrow> F b"\<close>

\<^cancel>\<open>locale Reachability_Impl_pre =
  Reachability_Impl_invariant where E = E +
  Reachability_Impl_base2 where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin\<close>

locale Reachability_Impl_pre =
  Reachability_Impl_invariant where E = E +
  Reachability_Impl_base2 where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

definition
  "check_final \<equiv> do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L);
  monadic_list_all (\<lambda>l. do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = M l);
    monadic_list_all (\<lambda>s.
      RETURN (\<not> F (l, s))
    ) xs
    }
  ) l
  }
"

definition
  "check_final_spec = (\<forall>s'\<in>{(l, s) |l s. l \<in> L \<and> s \<in> M l}. \<not> F s')"

lemma check_final_correct:
  "check_final \<le> SPEC (\<lambda>r. r \<longleftrightarrow> check_final_spec)"
  unfolding check_final_def check_final_spec_def
  by (refine_vcg monadic_list_all_rule) (auto simp: list_all_iff list_ex_iff)

lemma check_final_nofail:
  "nofail check_final"
  by (metis check_final_correct nofail_simps(2) pwD1)

definition
  "check_init l\<^sub>0 s\<^sub>0 \<equiv> do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P' (l\<^sub>0, s\<^sub>0));
  xs \<leftarrow> SPEC (\<lambda>xs. set xs = M l\<^sub>0);
  b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (s\<^sub>0 \<preceq> s)) xs;
  RETURN (b1 \<and> b2 \<and> b3)
  }"

definition check_all_pre_alt_def:
  "check_all_pre l\<^sub>0 s\<^sub>0 \<equiv> do {
  b1 \<leftarrow> check_init l\<^sub>0 s\<^sub>0;
  b2 \<leftarrow> check_prop P';
  RETURN (b1 \<and> b2)
  }"

lemma check_all_pre_def:
  "check_all_pre l\<^sub>0 s\<^sub>0 = do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P' (l\<^sub>0, s\<^sub>0));
  xs \<leftarrow> SPEC (\<lambda>xs. set xs = M l\<^sub>0);
  b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (s\<^sub>0 \<preceq> s)) xs;
  b4 \<leftarrow> check_prop P';
  RETURN (b1 \<and> b2 \<and> b3 \<and> b4)
  }"
  unfolding check_all_pre_alt_def check_init_def by simp

definition
  "check_init_spec l\<^sub>0 s\<^sub>0 \<equiv> l\<^sub>0 \<in> L \<and> (\<exists> s' \<in> M l\<^sub>0. s\<^sub>0 \<preceq> s') \<and> P' (l\<^sub>0, s\<^sub>0)"

definition
  "check_all_pre_spec l\<^sub>0 s\<^sub>0 \<equiv>
  (\<forall>l \<in> L. \<forall>s \<in> M l. P' (l, s)) \<and> l\<^sub>0 \<in> L \<and> (\<exists> s' \<in> M l\<^sub>0. s\<^sub>0 \<preceq> s') \<and> P' (l\<^sub>0, s\<^sub>0)"

lemma check_all_pre_correct:
  "check_all_pre l\<^sub>0 s\<^sub>0 \<le> RETURN (check_all_pre_spec l\<^sub>0 s\<^sub>0)"
  unfolding check_all_pre_def check_all_pre_spec_def
  by (refine_vcg check_prop_correct monadic_list_ex_rule; standard; auto simp: list_ex_iff)

lemma check_init_correct:
  "check_init l\<^sub>0 s\<^sub>0 \<le> RETURN (check_init_spec l\<^sub>0 s\<^sub>0)"
  unfolding check_init_def check_init_spec_def
  by (refine_vcg monadic_list_ex_rule; standard; auto simp: list_ex_iff)

end


locale Reachability_Impl_pre_start =
  Reachability_Impl_pre where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes l\<^sub>0 :: 'l and s\<^sub>0 :: 's
begin

definition
  "check_all \<equiv> do {
  b \<leftarrow> check_all_pre l\<^sub>0 s\<^sub>0;
  if b then RETURN (check_invariant_spec L) else RETURN False
  }"

definition
  "certify_unreachable = do {
    b1 \<leftarrow> check_all;
    b2 \<leftarrow> check_final;
    RETURN (b1 \<and> b2)
  }"

lemma certify_unreachable_alt_def:
  "certify_unreachable = do {
    b1 \<leftarrow> check_all_pre l\<^sub>0 s\<^sub>0;
    b2 \<leftarrow> RETURN (check_invariant_spec L);
    b3 \<leftarrow> check_final;
    RETURN (b1 \<and> b2 \<and> b3)
  }"
  unfolding certify_unreachable_def check_all_def by simp (fo_rule arg_cong2, auto)

definition
  "check_all_spec \<equiv> check_all_pre_spec l\<^sub>0 s\<^sub>0 \<and> check_invariant_spec L"

lemma check_all_correct:
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_spec)"
  unfolding check_all_def check_all_spec_def check_all_pre_def check_all_pre_spec_def
  by (refine_vcg check_prop_correct check_invariant_correct monadic_list_ex_rule)
     (auto simp: list_ex_iff dest: P'_P)

end


locale Reachability_Impl_correct =
  Reachability_Impl_pre_start where E = E +
  Unreachability_Invariant_paired_pre where E = E for E :: "'l \<times> 's \<Rightarrow> _"
begin

lemma Unreachability_Invariant_pairedI[rule_format]:
  "check_all_spec
  \<longrightarrow> Unreachability_Invariant_paired (\<preceq>) (\<prec>) M L E P l\<^sub>0 s\<^sub>0 (\<lambda>(l, u) (l', u'). l' = l \<and> u \<preceq> u')"
  unfolding check_all_spec_def check_all_pre_spec_def check_invariant_spec_def
  by clarsimp (standard, auto dest: P'_P)

lemma check_all_correct':
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow>
    Unreachability_Invariant_paired (\<preceq>) (\<prec>) M L E P l\<^sub>0 s\<^sub>0 (\<lambda>(l, u) (l', u'). l' = l \<and> u \<preceq> u'))"
  by (refine_vcg Unreachability_Invariant_pairedI check_all_correct) fast

lemma certify_unreachableI:
  "check_all_spec \<and> check_final_spec \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s')"
  by (rule impI Unreachability_Invariant_paired.final_unreachable Unreachability_Invariant_pairedI)+
     (auto intro: F_mono simp: check_final_spec_def)

lemma certify_unreachable_correct:
  "certify_unreachable \<le> SPEC (\<lambda>r. r \<longrightarrow> check_all_spec \<and> check_final_spec)"
  unfolding certify_unreachable_def by (refine_vcg check_all_correct check_final_correct; fast)

lemma certify_unreachable_correct':
  "certify_unreachable \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))"
  by (refine_vcg certify_unreachableI[rule_format] certify_unreachable_correct; fast)

end


locale Buechi_Impl_invariant =
  Reachability_Impl_base where E = E for E :: "'l \<times> 's \<Rightarrow> _" +
  fixes L :: "'l set" and M :: "'l \<Rightarrow> ('s \<times> nat) set"
begin

definition "check_invariant_buechi R L' \<equiv>
  monadic_list_all (\<lambda>l.
    do {
      let as = M l;
      as \<leftarrow> SPEC (\<lambda>xs'. set xs' = as);
      monadic_list_all (\<lambda>(x, i). do {
        let succs = succs l {x};
        monadic_list_all (\<lambda>(l', xs). do {
          xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
          b1 \<leftarrow> RETURN (l' \<in> L);
          if xs = [] then RETURN True else do {
              ys \<leftarrow> SPEC (\<lambda>xs. set xs = M l');
              b2 \<leftarrow> monadic_list_all (\<lambda>y.
                monadic_list_ex (\<lambda>(z, j). RETURN (R l l' i j x y z)) ys
              ) xs;
              RETURN (b1 \<and> b2)
            }
          }) succs
      }) as
    }) L'"

definition
  "check_invariant_buechi_spec R L' \<equiv>
  \<forall>l \<in> L'. \<forall>(s, i) \<in> M l. \<forall>l' s'.
    E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s'')"

lemma check_invariant_buechi_correct:
  "check_invariant_buechi R L' \<le> SPEC (\<lambda>r. r \<longrightarrow> check_invariant_buechi_spec R (set L'))"
  (is "_ \<le> ?rhs")
  if assms: "\<forall>l \<in> L. \<forall>(s, _) \<in> M l. P (l, s)" "set L' \<subseteq> L"
proof -
  have *: "
    (case x of (s, i) \<Rightarrow> \<forall>x\<in>set (succs l {s}). case x of (l', ys) \<Rightarrow>
                  \<forall>s' \<in> ys. l' \<in> L \<and> (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s'')) =
    (case x of (s, i) \<Rightarrow>
       \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s''))"
    if "x \<in> M l" "l \<in> L" for x l using succs_correct[of "{fst x}" l] assms(1) that by fastforce
  let ?R = "\<lambda>l s i l' s'. (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s'')"
  let ?Q = "\<lambda>l s i. \<lambda>(l',ys). (\<forall>s' \<in> ys. l' \<in> L \<and> ?R l s i l' s')"
  let ?P = "\<lambda>l (s, i). \<forall>(l',ys) \<in> set (succs l {s}). ?Q l s i (l', ys)"
  have "check_invariant_buechi R L' \<le> SPEC (\<lambda>r. r \<longleftrightarrow>
    (\<forall>l \<in> set L'. \<forall>(s, i) \<in> M l. \<forall>(l',ys) \<in> set (succs l {s}). (\<forall>s' \<in> ys. l' \<in> L \<and>
      (\<exists>(s'', j) \<in> M l'. R l l' i j s s' s''))))"
    unfolding check_invariant_buechi_def
    apply (rule monadic_list_all_rule[unfolded list_all_iff])
    apply refine_vcg
    subgoal for l xs
      apply (refine_vcg monadic_list_all_rule[unfolded list_all_iff, where P = "?P l"])
      subgoal for _ s i
        apply (refine_vcg monadic_list_all_rule[unfolded list_all_iff, where P = "?Q l s i"])
          apply (auto; fail)
        subgoal for _ l'
          apply (refine_vcg monadic_list_all_rule[unfolded list_all_iff, where P = "?R l s i l'"])
          subgoal for s'
            apply (refine_vcg monadic_list_ex_rule[unfolded list_ex_iff])
            by auto
          by auto
        by auto
      by auto
    done
  also have "\<dots> \<le> ?rhs"
    unfolding check_invariant_buechi_spec_def by (auto simp: * assms(2)[THEN subsetD])
  finally show ?thesis .
qed

end


locale Buechi_Impl_pre =
  Buechi_Impl_invariant where M = M +
  Reachability_Impl_base2 for M :: "'l \<Rightarrow> ('s \<times> nat) set" +
  assumes finite: "finite L" "\<forall>l \<in> L. finite (M l)"
begin

definition
  "buechi_prop l l' i j s s' s'' \<equiv> l' \<in> L \<and> s' \<preceq> s'' \<and>
    (if F (l, s) then i < j else i \<le> j)"

text \<open>
Old alternative definition.
Slightly easier to work with but subsumptions are not deterministic.\<close>
\<comment> \<open>definition
  "SE \<equiv> \<lambda>(l, s) (l', s').
    l' = l \<and> (\<exists>j. is_arg_max (\<lambda>(s, i). i) (\<lambda>(s', j). s \<preceq> s' \<and> (s', j) \<in> M l) (s', j))"\<close>

definition
  "has_SE \<equiv> \<lambda>s l. \<exists>s' j. s \<preceq> s' \<and> (s', j) \<in> M l"

definition
  "SE \<equiv> \<lambda>(l, s) (l', s'). l' = l \<and> l \<in> L \<and> has_SE s l \<and>
    (\<exists>j. (s', j) = arg_max (\<lambda>(s, i). i) (\<lambda>(s', j). s \<preceq> s' \<and> (s', j) \<in> M l))"

lemma
  assumes "SE (l, s) (l', s')"
  shows SE_same_loc: "l' = l" and SE_subsumes: "s \<preceq> s'"
    and SE_is_arg_max: "\<exists>j. is_arg_max (\<lambda>(s, i). i) (\<lambda>(s', j). s \<preceq> s' \<and> (s', j) \<in> M l) (s', j)"
    (is "\<exists>j. is_arg_max ?f ?P (s', j)")
proof -
  from assms have "has_SE s l'" "l' \<in> L" and [simp]: "l' = l"
    unfolding SE_def by auto
  then obtain s1 j where "?P (s1, j)"
    unfolding has_SE_def by auto
  moreover have "finite (Collect ?P)"
    using finite \<open>l' \<in> L\<close> by (auto intro: finite_subset)
  moreover note arg_max_rule = arg_max_nat_lemma2[of ?P, OF calculation, of "\<lambda>(s, i). i"]
  then show "l' = l" "s \<preceq> s'" "\<exists>j. is_arg_max ?f ?P (s', j)"
    using assms unfolding is_arg_max_linorder SE_def is_arg_max_linorder by auto
qed

lemma SE_deterministic:
  assumes "\<And>s. s1 \<preceq> s \<longleftrightarrow> s2 \<preceq> s"
  assumes "SE (l, s1) (l', s1')" "SE (l, s2) (l', s2')"
  shows "s2' = s1'"
  using assms(2,3) unfolding SE_def by (clarsimp simp: assms(1)) (metis prod.inject)

lemma SE_I:
  assumes "(s'', j) \<in> M l'" "buechi_prop l l' i j s s' s''"
  shows "\<exists>(s'', j) \<in> M l'. SE (l', s') (l', s'')"
proof -
  let ?P = "\<lambda>(s1, j). s' \<preceq> s1 \<and> (s1, j) \<in> M l'"
  let ?f = "\<lambda>(s, i). i"
  from assms have "?P (s'', j)" "l' \<in> L"
    unfolding buechi_prop_def by auto
  have "finite (Collect ?P)"
    using finite \<open>l' \<in> L\<close> by (auto intro: finite_subset)
  from arg_max_nat_lemma2[OF \<open>?P (s'', j) \<close> this, of ?f] \<open>l' \<in> L\<close> show ?thesis
    unfolding has_SE_def SE_def is_arg_max_linorder by (auto 4 3)
qed

definition
  "check_all_pre_spec1 inits \<equiv>
  (\<forall>l \<in> L. \<forall>s \<in> fst ` M l. P' (l, s)) \<and>
  (\<forall>(l\<^sub>0, s\<^sub>0) \<in> inits. l\<^sub>0 \<in> L \<and> (\<exists> (s', _) \<in> M l\<^sub>0. s\<^sub>0 \<preceq> s') \<and> P' (l\<^sub>0, s\<^sub>0))"

definition
  "check_buechi inits \<equiv> do {
  b \<leftarrow> SPEC (\<lambda>r. r \<longrightarrow> check_all_pre_spec1 inits);
  if b then do {
    ASSERT (check_all_pre_spec1 inits);
    SPEC (\<lambda>r. r \<longrightarrow> check_invariant_buechi_spec (buechi_prop ) L)
  } else RETURN False
  }"

definition
  "check_buechi_spec inits \<equiv>
  check_all_pre_spec1 inits
  \<and> (\<forall>l \<in> L. \<forall>(s, i) \<in> M l. \<forall>l' s'. E (l, s) (l', s')
    \<longrightarrow> (\<exists>(s'', j) \<in> M l'. buechi_prop l l' i j s s' s''))"

definition
  "check_buechi_spec' inits \<equiv>
  (\<forall>(l\<^sub>0, s\<^sub>0) \<in> inits. Unreachability_Invariant_paired (\<preceq>) (\<prec>) (\<lambda>l. fst ` M l) L E P l\<^sub>0 s\<^sub>0 SE)
  \<and> (\<forall>l \<in> L. \<forall>(s, i) \<in> M l. \<forall>l' s'. E (l, s) (l', s')
    \<longrightarrow> (\<exists>(s'', j) \<in> M l'. buechi_prop l l' i j s s' s''))"

lemma check_buechi_correct:
  "check_buechi inits \<le> SPEC (\<lambda>r. r \<longrightarrow> check_buechi_spec inits)"
  unfolding check_buechi_def check_invariant_buechi_spec_def check_buechi_spec_def
  by (refine_vcg; blast)

end


locale Buechi_Impl_correct =
  Buechi_Impl_pre where M = M and E = E+
  Unreachability_Invariant_paired_pre where E = E for E and M :: "'l \<Rightarrow> ('s \<times> nat) set"
begin

lemma check_buechi_correct':
  "check_buechi inits \<le> SPEC (\<lambda>r. r \<longrightarrow> check_buechi_spec' inits)"
proof -
  have "Unreachability_Invariant_paired (\<preceq>) (\<prec>) (\<lambda>l. fst ` M l) L E P l\<^sub>0 s\<^sub>0 SE"
    if "(l\<^sub>0, s\<^sub>0) \<in> inits" "check_all_pre_spec1 inits" "check_invariant_buechi_spec (buechi_prop ) L"
    for l\<^sub>0 s\<^sub>0
    using that unfolding check_invariant_buechi_spec_def check_all_pre_spec1_def
    apply -
    apply standard
         apply (use SE_I SE_same_loc SE_subsumes in
          \<open>auto 4 3 dest!: P'_P simp: list_ex_iff Ball_def_raw Bex_def_raw\<close>)
    apply (smt case_prodE fst_conv)
    done
  then show ?thesis
    unfolding check_buechi_def check_invariant_buechi_spec_def check_buechi_spec'_def
    by (refine_vcg; blast)
qed

definition f where
  "f \<equiv> \<lambda>(l, s). Max {i. (s, i) \<in> M l}"

lemma
  assumes "l \<in> L" "(s, i) \<in> M l"
  shows f_in: "(s, f (l, s)) \<in> M l" (is "?P1")
    and f_ge: "\<forall>j. (s, j) \<in> M l \<longrightarrow> j \<le> f (l, s)" (is "?P2")
proof -
  have "finite {i. (s, i) \<in> M l}"
    using finite \<open>l \<in> L\<close> [[simproc add: finite_Collect]] by auto
  with assms(2) show ?P1 ?P2
    unfolding f_def by (auto intro: Max_ge dest: Max_in)
qed

lemma f_topo:
  fixes l :: \<open>'l\<close> and s :: \<open>'s\<close> and l1 :: \<open>'l\<close> and s1 :: \<open>'s\<close> and l2 :: \<open>'l\<close> and s2 :: \<open>'s\<close>
  assumes 
    "check_buechi_spec' inits"
    \<open>l \<in> L\<close> and
    \<open>s \<in> fst ` M l\<close> and
    \<open>l2 \<in> L\<close> and
    \<open>s2 \<in> fst ` M l2\<close> and
    \<open>E (l, s) (l1, s1)\<close> and
    \<open>SE (l1, s1) (l2, s2)\<close>
  shows \<open>if F (l, s) then f (l, s) < f (l2, s2) else f (l, s) \<le> f (l2, s2)\<close>
proof -
  let ?P = "\<lambda>s l' (s', j). s \<preceq> s' \<and> (s', j) \<in> M l'"
  let ?f = "\<lambda>(s, i). i"
  let ?le = "\<lambda>l s i j. if F(l, s) then i < j else i \<le> j"
  from \<open>SE _ _\<close> obtain j where "(s2, j) \<in> M l2" and [simp]: "l2 = l1"
    and is_max: "is_arg_max ?f (?P s1 l1) (s2, j)"
    using SE_is_arg_max SE_same_loc SE_subsumes
    by atomize_elim (fastforce simp: Lattices_Big.ord_class.is_arg_max_def)
  from f_in assms have "(s, f (l, s)) \<in> M l"
    by auto
  with assms obtain s' i where "(s', i) \<in> M l2" "buechi_prop l l2 (f (l, s)) i s s1 s'"
    unfolding check_buechi_spec'_def by fastforce
  then have "(s', i) \<in> M l2" "s1 \<preceq> s'" "?le l s (f (l, s)) i"
    unfolding buechi_prop_def by auto
  from is_max \<open>(s', i) \<in> _\<close> \<open>s1 \<preceq> s'\<close> have "i \<le> j"
    unfolding is_arg_max_linorder by simp
  also from f_ge \<open>(s2, j) \<in> M l2\<close> have "j \<le> f (l2, s2)"
    using assms by auto
  finally show ?thesis
    using \<open>?le l s _ _\<close> by auto
qed

lemma no_buechi_run:
  assumes check: "check_buechi_spec' inits"
  assumes accepting_run:
    "(l\<^sub>0, s\<^sub>0) \<in> inits" "Graph_Defs.run E ((l\<^sub>0, s\<^sub>0) ## xs)" "alw (ev (holds F)) ((l\<^sub>0, s\<^sub>0) ## xs)"
  shows False
proof -
  interpret Unreachability_Invariant_paired "(\<preceq>)" "(\<prec>)" "\<lambda>l. fst ` M l" L E P l\<^sub>0 s\<^sub>0 SE
    using check \<open>_ \<in> inits\<close> unfolding check_buechi_spec'_def by blast
  show ?thesis
    apply (rule no_buechi_run[where F = F and f = f])
         apply (rule F_mono; assumption)
    using finite apply blast+
      apply (rule f_topo, rule check, assumption+)
     apply (rule accepting_run)+
    done
qed

end (* Buechi Impl pre *)


locale Reachability_Impl_common =
  Reachability_Impl_pre where less_eq = less_eq and M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for less_eq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<preceq>" 50) and M :: "'k \<Rightarrow> 'b set option" +
  assumes L_finite: "finite L"
      and M_ran_finite: "\<forall>S \<in> ran M. finite S"
      and succs_finite: "\<forall>l S. \<forall>(l', S') \<in> set (succs l S). finite S \<longrightarrow> finite S'"
      and succs_empty: "\<And>l. succs l {} = []"
      (* This could be weakened to state that \<open>succs l {}\<close> only contains empty sets *)
begin

lemma M_listD:
  assumes "M l = Some S"
  shows "\<exists> xs. set xs = S"
  using M_ran_finite assms unfolding ran_def by (auto intro: finite_list)

lemma L_listD:
  shows "\<exists> xs. set xs = L"
  using L_finite by (rule finite_list)

lemma check_prop_gt_SUCCEED:
  "check_prop P' > SUCCEED"
  unfolding check_prop_def using L_listD
  by (fastforce split: option.split dest: M_listD
        intro: monadic_list_all_gt_SUCCEED bind_RES_gt_SUCCEED_I
     )

definition
  "check_final' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      monadic_list_all (\<lambda>s.
        RETURN (\<not> PR_CONST F (l, s))
      ) xs
    }
    }
  ) l
  }"

lemma check_final_alt_def:
  "check_final' L M = check_final"
  unfolding check_final'_def check_final_def
  by (fo_rule arg_cong2, simp, fo_rule arg_cong) (auto split: option.split simp: bind_RES)

definition check_prop' where
  "check_prop' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"

lemma check_prop_alt_def:
  "check_prop' L M = check_prop P'"
  unfolding check_prop_def check_prop'_def
  by (fo_rule arg_cong2, simp, fo_rule arg_cong) (auto split: option.split simp: bind_RES)

lemma check_prop'_alt_def:
  "check_prop' L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l. do {
    let (S, M) = op_map_extract l M';
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }"
  unfolding check_prop'_def
  by (fo_rule arg_cong2, simp, fo_rule arg_cong) (auto split: option.split simp: bind_RES)

end


locale Certification_Impl_base = Reachability_Impl_base2 where less = less
  for less :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<prec>" 50) +
  fixes A :: "'s \<Rightarrow> ('si :: heap) \<Rightarrow> assn"
    and K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn"
    and Fi and keyi and Pi and copyi and Lei and succsi
  assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST fst) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a K"
  assumes copyi[sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  assumes Pi_P'[sepref_fr_rules]: "(Pi,RETURN o PR_CONST P') \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes Fi_F[sepref_fr_rules]: "(Fi,RETURN o PR_CONST F) \<in> (prod_assn K A)\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  assumes succsi[sepref_fr_rules]:
    "(uncurry succsi,uncurry (RETURN oo PR_CONST succs))
    \<in> K\<^sup>k *\<^sub>a (lso_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn (K \<times>\<^sub>a lso_assn A)"
  assumes Lei[sepref_fr_rules]:
    "(uncurry Lei,uncurry (RETURN oo PR_CONST less_eq)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes pure_K: "is_pure K"
  assumes left_unique_K: "IS_LEFT_UNIQUE (the_pure K)"
  assumes right_unique_K: "IS_RIGHT_UNIQUE (the_pure K)"

locale Reachability_Impl =
  Reachability_Impl_common where M = M +
  Certification_Impl_base where K = K and A = A +
  Reachability_Impl_correct where M = "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for M :: "'k \<Rightarrow> 'a set option"
  and K :: "'k \<Rightarrow> 'ki :: {hashable,heap} \<Rightarrow> assn" and A :: "'a \<Rightarrow> 'ai :: heap \<Rightarrow> assn" +
  fixes l\<^sub>0i :: "'ki Heap" and s\<^sub>0i :: "'ai Heap"
  assumes l\<^sub>0i_l\<^sub>0[sepref_fr_rules]:
    "(uncurry0 l\<^sub>0i, uncurry0 (RETURN (PR_CONST l\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a K"
  assumes s\<^sub>0i_s\<^sub>0[sepref_fr_rules]:
    "(uncurry0 s\<^sub>0i, uncurry0 (RETURN (PR_CONST s\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"



definition
  "print_check s b = println (s + STR '': '' + (if b then STR ''passed'' else STR ''failed''))"

definition
  "PRINT_CHECK = RETURN oo print_check"

lemma [sepref_import_param]:
  "(print_check, print_check) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  by simp

sepref_definition print_check_impl is
  "uncurry PRINT_CHECK" :: "id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PRINT_CHECK_def by sepref

sepref_register PRINT_CHECK

lemmas [sepref_fr_rules] = print_check_impl.refine


paragraph \<open>Misc implementation\<close>

sepref_decl_op map_lookup_copy: "\<lambda>k (m :: _ \<rightharpoonup> _). (m k, m)"
  :: "K \<rightarrow> \<langle>K,V\<rangle>map_rel \<rightarrow> \<langle>V\<rangle>option_rel \<times>\<^sub>r \<langle>K,V\<rangle>map_rel"
  where "single_valued K" "single_valued (K\<inverse>)"
  apply (rule fref_ncI)
  apply parametricity
  unfolding map_rel_def
  apply (elim IntE)
  apply parametricity
  done

definition
  "heap_map copy xs \<equiv> do {
    xs \<leftarrow> imp_nfoldli xs (\<lambda>_. return True) (\<lambda>x xs. do {x \<leftarrow> copy x; return (x # xs)}) [];
    return (rev xs)
  }"

definition
  "monadic_map copy xs \<equiv> do {
    xs \<leftarrow> monadic_nfoldli xs (\<lambda>_. RETURN True) (\<lambda>x xs. do {x \<leftarrow> copy x; RETURN (x # xs)}) [];
    RETURN (rev xs)
  }"

context
begin

private lemma monadic_nfoldli_rev:
  "monadic_nfoldli x (\<lambda>_. RETURN True) (\<lambda>x xs. RETURN (x # xs)) [] \<le> SPEC (\<lambda>r. r = rev x)"
  unfolding nfoldli_to_monadic[where c = "\<lambda>_.True", symmetric]
  by (rule nfoldli_rule[where I = "\<lambda> xs ys zs. rev zs @ ys = x"]) auto

private lemma frame2:
  "hn_ctxt (list_assn A) x xi * hn_invalid (list_assn A) [] [] * hn_ctxt (list_assn A) xa x'
  \<Longrightarrow>\<^sub>t hn_ctxt (list_assn A) x xi * hn_ctxt (list_assn A) xa x'"
  by (simp add: frame_rem2 frame_rem3)

private lemma frame3:
  "hn_ctxt (list_assn A) x xi * hn_invalid (list_assn A) [] []
  \<Longrightarrow>\<^sub>t hn_ctxt (list_assn A) x xi * hn_ctxt (pure UNIV) xa x'"
  by (simp add: frame_rem2 frame_rem3 pure_def entt_fr_drop hn_ctxt_def)

(* XXX Copy *)
lemma list_rev_aux: "list_assn A a c \<Longrightarrow>\<^sub>A list_assn A (rev a) (rev c)"
  apply (subst list_assn_aux_len, clarsimp)
  apply (induction rule: list_induct2)
   apply (sep_auto; fail)
  apply (sep_auto, erule ent_frame_fwd, frame_inference, sep_auto)
  done

theorem copy_list_refine:
  assumes
    copy: "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  shows
    "hn_refine
      (hn_ctxt (list_assn A) x xi)
        (heap_map copy $ xi)
      (hn_ctxt (list_assn A) x xi)
      (list_assn A)
        (monadic_map (RETURN \<circ> COPY) $ x)"
  unfolding monadic_map_def heap_map_def
  apply sep_auto
  apply (rule hnr_bind)
    apply (rule monadic_nfoldli_refine_aux'[
        where S = "set x" and Rs = "list_assn A" and Rl = A and Rl' = A and Rl'' = A and \<Gamma> = emp,
          THEN hn_refine_cons_pre[rotated]])
        apply sep_auto
  subgoal
    by standard (sep_auto simp: pure_def)
  subgoal
    supply [sep_heap_rules]  = copy[to_hnr, unfolded hn_refine_def, simplified]
    apply standard
    apply sep_auto
      (* Frame *)
    by (smt assn_times_comm ent_refl ent_star_mono hn_ctxt_def invalidate_clone star_aci(3))

     apply (sep_auto; fail)
    apply (sep_auto simp: pure_def; fail)
   prefer 2
   apply (rule frame3; fail)
  apply standard
  apply sep_auto
  apply (drule order_trans, rule monadic_nfoldli_rev)
  apply (rule ent_true_drop(2))
  apply (rule ent_star_mono)
   apply sep_auto
  unfolding hn_ctxt_def
  apply (rule list_rev_aux)
  done

end

lemma monadic_map_refine':
  "(heap_map copy, monadic_map (RETURN o COPY)) \<in> (list_assn A)\<^sup>k \<rightarrow>\<^sub>a list_assn A"
  if "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  using that by (rule copy_list_refine[to_hfref])

lemma copy_list_COPY:
  "monadic_map (RETURN o COPY) = RETURN o COPY" (is "?l = ?r")
proof (rule ext)
  fix xs :: "'a list"
  have *: "
    monadic_nfoldli xs (\<lambda>_. RETURN True)
     (\<lambda>x xs. (RETURN \<circ> (\<lambda>x. x)) x \<bind> (\<lambda>x. RETURN (x # xs))) as
    = RETURN (rev xs @ as)" for as
    by (induction xs arbitrary: as) auto
  show "?l xs = ?r xs"
    unfolding monadic_map_def COPY_def by (subst *) simp
qed

lemma copy_list_lso_assn_refine:
  "(heap_map copy, RETURN o COPY) \<in> (lso_assn A)\<^sup>k \<rightarrow>\<^sub>a lso_assn A"
  if "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  supply [sep_heap_rules] =
    monadic_map_refine'[OF that, to_hnr, unfolded copy_list_COPY hn_refine_def hn_ctxt_def, simplified]
  unfolding lso_assn_def hr_comp_def by sepref_to_hoare sep_auto

end