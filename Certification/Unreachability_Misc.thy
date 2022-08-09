theory Unreachability_Misc
  imports
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

lemma RETURN_eqI:
  fixes m
  assumes "m \<le> RETURN r" "m > SUCCEED"
  shows "m = RETURN r"
  using assms
  unfolding RETURN_def
  by (cases m) auto

lemma bind_gt_SUCCEED_I:
  assumes "m \<le> SPEC \<Phi>" "m > SUCCEED" "\<And>s. \<Phi> s \<Longrightarrow> f s > SUCCEED"
  shows "do {x \<leftarrow> m; f x} > SUCCEED"
  by (metis assms bot.not_eq_extremum inres_simps(2) leD mem_Collect_eq
        nofail_simps(2) pw_bind_le_iff pw_ords_iff(1))

lemma bind_gt_SUCCEED_I':
  assumes "l \<le> RETURN r" "m \<le> SPEC \<Phi>" "\<And>s. \<Phi> s \<Longrightarrow> f s \<le> RETURN r" "m > SUCCEED"
    "\<And>s. \<Phi> s \<Longrightarrow> f s > SUCCEED"
  shows "l \<le> do {x \<leftarrow> m; f x}"
  apply (rule ord_class.ord_le_eq_trans[rotated], rule HOL.sym, rule RETURN_eqI)
  using assms by (auto simp: pw_bind_le_iff refine_pw_simps pw_ords_iff intro: bind_gt_SUCCEED_I)


named_theorems succeed_rules

lemmas [succeed_rules] = bind_RES_gt_SUCCEED_I SUCCEED_lt_RETURN

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

lemma monadic_list_all_rule [unfolded list_all_iff]:
  assumes "\<And>x. Pi x \<le> SPEC (\<lambda>r. r = P x)"
  shows "monadic_list_all Pi xs \<le> SPEC (\<lambda>r. r \<longleftrightarrow> list_all P xs)"
  using assms unfolding monadic_list_all_def
  by (intro nfoldli_rule[where I = "\<lambda>as bs b. b = list_all P as \<and> set (as @ bs) = set xs"]) auto

definition
  "monadic_list_ex P xs \<equiv> nfoldli xs Not (\<lambda>x _. P x) False"

lemma monadic_list_ex_rule [unfolded list_ex_iff]:
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

lemma monadic_list_all_gt_SUCCEED [succeed_rules]:
  "monadic_list_all g xs > SUCCEED"
  using nfoldli_gt_SUCCEED unfolding monadic_list_all_def .

lemma monadic_list_ex_gt_SUCCEED [succeed_rules]:
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


paragraph \<open>Printing utilities\<close>

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