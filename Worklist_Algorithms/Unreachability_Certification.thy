theory Unreachability_Certification
  imports
    TA_Impl.Worklist_Locales
    "../Simulation_Graphs_Certification"
    TA_Impl.Unified_PW_Impl
    TA_Impl.Leadsto_Impl
    TA_Impl.Printing
begin

paragraph \<open>Misc \<open>nres\<close>\<close>

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


locale Reachability_Impl_pre =
  Unreachability_Invariant_paired_pre _ _ +
  fixes succs :: "_ \<Rightarrow> _" and P'
  assumes P'_P: "\<And> l s. P' (l, s) \<Longrightarrow> P (l, s)"
  assumes succs_correct:
    "\<And> l. \<forall> s \<in> xs. P (l, s)
  \<Longrightarrow> {(l', s')| l' ys s'. (l', ys) \<in> set (succs l xs) \<and> s' \<in> ys}
    = (\<Union> s \<in> xs. Collect (E (l, s)))"

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

context
begin

private definition "I as bs b \<equiv> (b \<longleftrightarrow> (\<forall> l \<in> set as. \<forall>s \<in> M l. P (l, s))) \<and> set (as @ bs) = L"

lemma check_prop_correct:
  "check_prop \<le> SPEC (\<lambda>r. r \<longleftrightarrow> (\<forall>l \<in> L. \<forall>s \<in> M l. P (l, s)))"
  unfolding check_prop_def
(*
  by (refine_vcg nfoldli_rule[where I = I]) (auto simp: I_def)
*)
  by (refine_vcg monadic_list_all_rule monadic_list_ex_rule) (auto simp: list_all_iff)

end

end

end

context Reachability_Invariant_paired_pre_defs
begin

end

context Reachability_Impl_pre
begin

definition "check_invariant \<equiv>
do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L);
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
  ) l
}
"

lemma check_invariant_correct:
  "check_invariant \<le> SPEC (\<lambda>r. r \<longrightarrow>
    (\<forall> l \<in> L. \<forall> s \<in> M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')))"
  (is "_ \<le> ?rhs")
  if assms: "\<forall>l \<in> L. \<forall>s \<in> M l. P (l, s)"
proof -
  have *: "(\<forall> (l',ys) \<in> set (succs l xs). \<forall> s' \<in> ys. l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')) =
       (\<forall>s\<in>M l.
           \<forall>l' s'.
              E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. s' \<preceq> s''))"
    if "xs = M l" "l \<in> L"
     for l xs
    using succs_correct[of xs l] assms that
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
     (\<forall> l \<in> L. (\<forall> (l',ys) \<in> set (succs l (M l)). \<forall> s' \<in> ys. l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s''))) =
     (\<forall> l \<in> L. \<forall>s\<in>M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. s' \<preceq> s''))"
    by (simp add: *)
  have "check_invariant \<le> SPEC (\<lambda>r. r \<longleftrightarrow>
    (\<forall> l \<in> L. (\<forall> (l',ys) \<in> set (succs l (M l)). (\<forall> s' \<in> ys. l' \<in> L \<and> (\<exists> s'' \<in> M l'. s' \<preceq> s'')))))"
    unfolding check_invariant_def
    by (refine_vcg monadic_list_all_rule monadic_list_ex_rule) (auto simp: list_all_iff list_ex_iff)
  also have "\<dots> \<le> ?rhs"
    by (auto; smt ** case_prodI2 case_prod_conv)
  finally show ?thesis .
qed

definition
  "check_all\<equiv> do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P' (l\<^sub>0, s\<^sub>0));
  xs \<leftarrow> SPEC (\<lambda>xs. set xs = M l\<^sub>0);
  b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (s\<^sub>0 \<preceq> s)) xs;
  b4 \<leftarrow> check_prop P';
  if b1 \<and> b2 \<and> b3 \<and> b4 then check_invariant else RETURN False
  }
"

definition
  "check_final F \<equiv> do {
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

lemma check_final_correct:
  "check_final F \<le> SPEC (\<lambda>r. r \<longleftrightarrow>
    (\<forall>s'\<in>{(l, s) |l s. l \<in> L \<and> s \<in> M l}. \<not> F s'))"
  unfolding check_final_def
  by (refine_vcg monadic_list_all_rule) (auto simp: list_all_iff list_ex_iff)

definition
  "certify_unreachable F \<equiv> do {
  b1 \<leftarrow> check_all;
  b2 \<leftarrow> check_final F;
  RETURN (b1 \<and> b2)
  }"

end

context Reachability_Impl_pre
begin

lemma check_all_correct:
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow> Unreachability_Invariant_paired (\<preceq>) (\<prec>) M L l\<^sub>0 s\<^sub>0 E P)"
  unfolding check_all_def
  by (refine_vcg check_prop_correct check_invariant_correct monadic_list_ex_rule;
      standard; auto simp: list_ex_iff dest: P'_P)

lemma certify_unreachable_correct:
  assumes F_mono: "\<And>a b. F a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> s \<preceq> s') a b \<Longrightarrow> F b"
  shows "certify_unreachable F \<le> SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))"
  unfolding certify_unreachable_def
  by (refine_vcg check_all_correct check_final_correct)
     (rule Unreachability_Invariant_paired.final_unreachable, auto intro: F_mono)

end

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
  "copy_list_impl copy xs \<equiv> do {
    xs \<leftarrow> imp_nfoldli xs (\<lambda>_. return True) (\<lambda>x xs. do {x \<leftarrow> copy x; return (x # xs)}) [];
    return (rev xs)
  }"

definition
  "copy_list copy xs \<equiv> do {
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
        (copy_list_impl copy $ xi)
      (hn_ctxt (list_assn A) x xi)
      (list_assn A)
        (copy_list (RETURN \<circ> COPY) $ x)"
  unfolding copy_list_def copy_list_impl_def
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

lemma copy_list_refine':
  "(copy_list_impl copy, copy_list (RETURN o COPY)) \<in> (list_assn A)\<^sup>k \<rightarrow>\<^sub>a list_assn A"
  if "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  using that by (rule copy_list_refine[to_hfref])

lemma copy_list_COPY:
  "copy_list (RETURN o COPY) = RETURN o COPY"
proof (rule ext, goal_cases)
  case (1 xs)
  then have *: "monadic_nfoldli xs (\<lambda>_. RETURN True)
     (\<lambda>x xs. (RETURN \<circ> (\<lambda>x. x)) x \<bind> (\<lambda>x. RETURN (x # xs)))
     as = RETURN (rev xs @ as)" for as
    by (induction xs arbitrary: as) auto
  show ?case
    unfolding copy_list_def COPY_def by (subst *) simp
qed

lemma copy_list_lso_assn_refine:
  "(copy_list_impl copy, RETURN o COPY) \<in> (lso_assn A)\<^sup>k \<rightarrow>\<^sub>a lso_assn A"
  if "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  supply [sep_heap_rules] =
    copy_list_refine'[OF that, to_hnr, unfolded copy_list_COPY hn_refine_def hn_ctxt_def, simplified]
  unfolding lso_assn_def hr_comp_def by sepref_to_hoare sep_auto


context
  fixes K :: "'k \<Rightarrow> ('ki :: {heap}) \<Rightarrow> assn"
  assumes pure_K: "is_pure K"
  assumes left_unique_K: "IS_LEFT_UNIQUE (the_pure K)"
  assumes right_unique_K: "IS_RIGHT_UNIQUE (the_pure K)"
begin

lemma pure_equality_impl:
  "(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> (K\<^sup>k *\<^sub>a K\<^sup>k) \<rightarrow>\<^sub>a bool_assn"
proof -
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  have [dest]: "a = b" if "(bi, b) \<in> the_pure K" "(bi, a) \<in> the_pure K" for bi a b
    using that right_unique_K by (elim single_valuedD) auto
  have [dest]: "a = b" if "(a, bi) \<in> the_pure K" "(b, bi) \<in> the_pure K" for bi a b
    using that left_unique_K unfolding IS_LEFT_UNIQUE_def by (elim single_valuedD) auto
  show ?thesis
    by (subst 1, subst (2) 1, sepref_to_hoare, sep_auto)
qed

definition
  "is_member x L \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = L);
    monadic_list_ex (\<lambda>y. RETURN (y = x)) xs
  }"

lemma is_member_refine:
  "is_member x L \<le> mop_set_member x L"
  unfolding mop_set_member_alt is_member_def
  by (refine_vcg monadic_list_ex_rule) (auto simp: list_ex_iff)

lemma is_member_correct:
  "(uncurry is_member, uncurry (RETURN \<circ>\<circ> op_set_member)) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using is_member_refine by (force simp: pw_le_iff pw_nres_rel_iff)

lemmas [sepref_fr_rules] = lso_id_hnr

sepref_definition is_member_impl is
  "uncurry is_member" :: "K\<^sup>k *\<^sub>a (lso_assn K)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  supply [sepref_fr_rules] = pure_equality_impl
  supply [safe_constraint_rules] = pure_K left_unique_K right_unique_K
  unfolding is_member_def monadic_list_ex_def list_of_set_def[symmetric] by sepref

lemmas op_set_member_lso_hnr = is_member_impl.refine[FCOMP is_member_correct]

end


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


locale Reachability_Impl =
  Reachability_Impl_pre less_eq _ "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for less_eq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and M :: "'k \<Rightarrow> 'b set option" +
  fixes A :: "'b \<Rightarrow> ('bi :: heap) \<Rightarrow> assn"
    and K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn" and F
    and Fi and keyi and Pi and copyi and Lei and l\<^sub>0i and s\<^sub>0i and succsi
  (* and L_list :: "'ki list" and M_table :: "('ki, 'bi list) hashtable Heap" *)
  assumes L_finite: "finite L"
      and M_ran_finite: "\<forall>S \<in> ran M. finite S"
      and succs_finite: "\<forall>l S. \<forall>(l', S') \<in> set (succs l S). finite S \<longrightarrow> finite S'"
      (* This could be weakened to state that \<open>succs l {}\<close> only contains empty sets *)
      and succs_empty: "\<And>l. succs l {} = []"
  assumes F_mono: "\<And>a b. F a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> less_eq s s') a b \<Longrightarrow> F b"
(*
  assumes L_impl[sepref_fr_rules]:
    "(uncurry0 (return L_list), uncurry0 (RETURN (PR_CONST L))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a lso_assn K"
  assumes M_impl:
    "(uncurry0 M_table, uncurry0 (RETURN (PR_CONST M))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' K (lso_assn A)"
*)
  assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST fst) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a K"
  assumes copyi[sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  assumes [sepref_fr_rules]: "(Pi,RETURN o PR_CONST P') \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]: "(Fi,RETURN o PR_CONST F) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]:
    "(uncurry succsi,uncurry (RETURN oo PR_CONST succs))
    \<in> K\<^sup>k *\<^sub>a (lso_assn A)\<^sup>d \<rightarrow>\<^sub>a list_assn (K \<times>\<^sub>a lso_assn A)"
  assumes [sepref_fr_rules]:
    "(uncurry Lei,uncurry (RETURN oo PR_CONST less_eq)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]:
    "(uncurry0 l\<^sub>0i, uncurry0 (RETURN (PR_CONST l\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a K"
  assumes [sepref_fr_rules]:
    "(uncurry0 s\<^sub>0i, uncurry0 (RETURN (PR_CONST s\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"
  assumes pure_K: "is_pure K"
  assumes left_unique_K: "IS_LEFT_UNIQUE (the_pure K)"
  assumes right_unique_K: "IS_RIGHT_UNIQUE (the_pure K)"
begin

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
  "check_final' L M = check_final F"
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

lemma M_listD:
  assumes "M l = Some S"
  shows "\<exists> xs. set xs = S"
  using M_ran_finite assms unfolding ran_def by (auto intro: finite_list)

lemma L_listD:
  shows "\<exists> xs. set xs = L"
  using L_finite by (rule finite_list)

definition
  "check_invariant' L' M' \<equiv> do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all (\<lambda>l.
  do {
    case op_map_lookup l M' of None \<Rightarrow> RETURN True  | Some xs \<Rightarrow> do {
    let succs = PR_CONST succs l xs;
    monadic_list_all (\<lambda>(l', xs). do {
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      if xs = [] then RETURN True
      else do {
        b1 \<leftarrow> RETURN (l' \<in> L'); (* XXX Optimize this *)
        if b1 then do {
        case op_map_lookup l' M' of None \<Rightarrow> RETURN False | Some ys \<Rightarrow> do {
          ys \<leftarrow> SPEC (\<lambda>xs.  set xs  = ys);
          b2 \<leftarrow> monadic_list_all (\<lambda>x'.
            monadic_list_ex (\<lambda>y. RETURN (PR_CONST less_eq x' y)) ys
          ) xs;
          RETURN b2
        }
      }
      else RETURN False
    }
    }) succs
  }
  }
  ) l
}"

lemma succs_listD:
  assumes "(l', S') \<in> set (succs l S)" "finite S"
  shows "\<exists> xs. set xs = S'"
  using assms succs_finite by (force intro!: finite_list)

lemma check_invariant'_refine:
  "check_invariant' L M \<le> check_invariant"
  unfolding check_invariant_def check_invariant'_def
  unfolding PR_CONST_def
  apply refine_mono
  apply (clarsimp split: option.splits simp: succs_empty)
  apply refine_mono
  apply (clarsimp split: option.splits)
  apply safe
  subgoal
    by refine_mono (auto simp: bind_RES monadic_list_all_False dest: M_listD)
  subgoal
    apply refine_mono
    apply clarsimp
    apply ((drule M_listD)+, elim exE)
    subgoal for xs1 _ _ xs2
      using monadic_list_all_list_ex_is_RETURN[of "\<lambda> x y. less_eq x y" xs2 xs1]
      by (cases "monadic_list_all (\<lambda>x. monadic_list_ex (\<lambda>y. RETURN (less_eq x y)) xs2) xs1")
         (auto intro: le_SPEC_bindI)
    done
  done

lemmas [safe_constraint_rules] = pure_K left_unique_K right_unique_K

lemmas [sepref_fr_rules] = lso_id_hnr

sepref_register
  "PR_CONST L" "list_of_set" "PR_CONST P'" "PR_CONST F" "PR_CONST succs" "PR_CONST less_eq"
  "PR_CONST M" :: "('k, 'b set) i_map"

lemma [sepref_import_param]: "(id, id) \<in> (Id :: (bool \<times> bool) set) \<rightarrow> Id"
  by simp

(*
lemmas [sepref_fr_rules] = M_impl
*)

sepref_definition check_prop_impl_wrong is
  "uncurry check_prop'" :: "(lso_assn K)\<^sup>k *\<^sub>a (hm.hms_assn' K (lso_assn A))\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding check_prop'_alt_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  apply sepref_dbg_keep
  oops

sepref_decl_impl "map_lookup":
  copy_list_lso_assn_refine[OF copyi, THEN hms_hm.hms_lookup_hnr]
  uses op_map_lookup.fref[where V = Id] .

abbreviation "table_assn \<equiv> hm.hms_assn' K (lso_assn A)"

sepref_thm check_prop_impl is
  "uncurry (PR_CONST check_prop')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_prop'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

concrete_definition (in -) check_prop_impl
  uses Reachability_Impl.check_prop_impl.refine_raw is "(uncurry ?f,_)\<in>_"

sepref_thm check_final_impl is
  "uncurry (PR_CONST check_final')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_final'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

concrete_definition (in -) check_final_impl
  uses Reachability_Impl.check_final_impl.refine_raw is "(uncurry ?f,_)\<in>_"

lemma K_equality[sepref_fr_rules]:
  "(uncurry (return oo (=)), uncurry (RETURN oo (=))) \<in> (K\<^sup>k *\<^sub>a K\<^sup>k) \<rightarrow>\<^sub>a bool_assn"
proof -
  have 1: "K = pure (the_pure K)"
    using pure_K by auto
  have [dest]: "a = b" if "(bi, b) \<in> the_pure K" "(bi, a) \<in> the_pure K" for bi a b
    using that right_unique_K by (elim single_valuedD) auto
  have [dest]: "a = b" if "(a, bi) \<in> the_pure K" "(b, bi) \<in> the_pure K" for bi a b
    using that left_unique_K unfolding IS_LEFT_UNIQUE_def by (elim single_valuedD) auto
  show ?thesis
    by (subst 1, subst (2) 1, sepref_to_hoare, sep_auto)
qed

sepref_definition is_K_eq_impl is
  "uncurry (RETURN oo (=))" :: "(K\<^sup>k *\<^sub>a K\<^sup>k) \<rightarrow>\<^sub>a bool_assn"
  unfolding is_member_def monadic_list_ex_def list_of_set_def[symmetric] by sepref

lemmas [sepref_fr_rules] = op_set_member_lso_hnr[OF pure_K left_unique_K right_unique_K]

sepref_thm check_invariant_impl is
  "uncurry (PR_CONST check_invariant')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_invariant'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

(*
lemma check_invariant'_correct:
  "(uncurry0 check_invariant', uncurry0 (PR_CONST check_invariant)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using check_invariant'_refine by (auto simp: pw_le_iff pw_nres_rel_iff)

lemmas check_invariant_impl_refine = check_invariant_impl.refine_raw[FCOMP check_invariant'_correct]

concrete_definition (in -) check_invariant_impl
  uses Reachability_Impl.check_invariant_impl_refine is "(uncurry0 ?f,_)\<in>_"
*)

definition
  "check_all' L' M' \<equiv> do {
  b1 \<leftarrow> RETURN (PR_CONST l\<^sub>0 \<in> L');
  b2 \<leftarrow> RETURN (PR_CONST P' (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0));
  let S = op_map_lookup (PR_CONST l\<^sub>0) M';
  case S of None \<Rightarrow> RETURN False | Some S \<Rightarrow> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (PR_CONST less_eq (PR_CONST s\<^sub>0) s)) xs;
    b4 \<leftarrow> PR_CONST check_prop' L' M';
    PRINT_CHECK STR ''Start state is in state list'' b1;
    PRINT_CHECK STR ''Start state fulfills property'' b2;
    PRINT_CHECK STR ''Start state is subsumed'' b3;
    PRINT_CHECK STR ''Check property'' b4;
    if b1 \<and> b2 \<and> b3 \<and> b4
    then do {
      r \<leftarrow> PR_CONST check_invariant' L' M';
      PRINT_CHECK STR ''State set invariant check'' r;
      RETURN r
    }
    else RETURN False
  }
  }
"

definition check_init where
  "check_init S \<equiv>
  case S of None \<Rightarrow> RETURN False | Some S \<Rightarrow> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    monadic_list_ex (\<lambda>s. RETURN (PR_CONST less_eq (PR_CONST s\<^sub>0) s)) xs
  }
"

lemma check_prop_gt_SUCCEED:
  "check_prop P' > SUCCEED"
  unfolding check_prop_def using L_listD
  by (fastforce split: option.split dest: M_listD
        intro: monadic_list_all_gt_SUCCEED bind_RES_gt_SUCCEED_I
     )

lemma check_all'_refine[refine_mono]:
  "check_all' L M \<le> check_all"
  unfolding check_all_def check_all'_def PR_CONST_def Let_def
  using check_prop_gt_SUCCEED
  apply (cases "op_map_lookup l\<^sub>0 M"; simp add: bind_RES)
   apply (cases "check_prop P'")
    apply (clarsimp_all intro: less_eq_Sup simp: bind_RES check_prop_alt_def)
  apply (rule less_eq_Sup)
  subgoal for a v
    apply clarsimp
    apply (rule Sup_least)
    apply clarsimp
    supply [refine_mono] = monadic_list_ex_mono monadic_list_ex_RETURN_mono
    apply refine_mono
    apply (simp add: check_invariant'_refine PRINT_CHECK_def)
    done
  subgoal
    by (auto dest: M_listD)
  done

(*
lemma check_all'_correct:
  "(uncurry0 check_all', uncurry0 (PR_CONST check_all)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using check_all'_refine by (auto simp: pw_le_iff pw_nres_rel_iff)
*)

sepref_register
  "PR_CONST check_invariant'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres" (* check_prop: "PR_CONST (check_prop P')" *)
  "PR_CONST check_prop'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_all'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_final'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"
  "PR_CONST check_init"
  "PR_CONST l\<^sub>0" "PR_CONST s\<^sub>0"

sepref_definition check_init_impl is
  "check_init" :: "(option_assn (lso_assn A))\<^sup>d \<rightarrow>\<^sub>a bool_assn"
  unfolding check_init_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

definition
  "L_member L' \<equiv> PR_CONST l\<^sub>0 \<in> L'"

sepref_thm L_member_impl is
  "RETURN o PR_CONST L_member" :: "(lso_assn K)\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding L_member_def by sepref

lemma L_member_fold:
  "PR_CONST l\<^sub>0 \<in> L' \<equiv> PR_CONST L_member L'"
  unfolding L_member_def PR_CONST_def .

(*
lemmas [sepref_fr_rules] =
  check_prop_impl.refine[OF Reachability_Impl_axioms]
  check_invariant_impl.refine[OF Reachability_Impl_axioms]
*)

term M

definition
  "lookup (M' :: 'k \<Rightarrow> 'b set option) = op_map_lookup (PR_CONST l\<^sub>0) M'"

lemma looukp_fold:
  "op_map_lookup (PR_CONST l\<^sub>0) = PR_CONST lookup"
  unfolding lookup_def PR_CONST_def ..

sepref_register L_member lookup :: "('k, 'b set) i_map \<Rightarrow> 'b set option"

definition check2 where
  "check2 b = PR_CONST check_init (PR_CONST lookup b)"

lemma check2_fold:
  "PR_CONST check_init (PR_CONST lookup b) = PR_CONST check2 b"
  unfolding check2_def PR_CONST_def ..

sepref_register check2 :: "('k, 'b set) i_map \<Rightarrow> bool nres"

definition check1 where
  "check1 = PR_CONST P' (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0)"

lemma check1_fold:
  "PR_CONST check1 = PR_CONST P' (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0)"
  unfolding check1_def PR_CONST_def ..

sepref_register check1

sepref_thm check1_impl is
  "uncurry0 (RETURN (PR_CONST check1))" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding check1_def by sepref

sepref_thm check2_impl is
  "PR_CONST check2" :: "table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check2_def
  unfolding PR_CONST_def
  unfolding check_init_def lookup_def
  unfolding list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

lemmas [sepref_fr_rules] =
  L_member_impl.refine_raw
  check1_impl.refine_raw
  check2_impl.refine_raw
  check_prop_impl.refine_raw
  check_invariant_impl.refine_raw

sepref_thm check_all_impl is
  "uncurry (PR_CONST check_all')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_all'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

(*
lemmas check_all_impl_refine = check_all_impl.refine_raw[FCOMP check_all'_correct]
*)

(*
concrete_definition (in -) check_all_impl
  uses Reachability_Impl.check_all_impl_refine is "(uncurry0 ?f,_)\<in>_"
*)

concrete_definition (in -) check_all_impl
  uses Reachability_Impl.check_all_impl.refine_raw is "(uncurry ?f,_)\<in>_"

(*
thm check_all_impl.refine

lemmas [sepref_fr_rules] =
  check_final_impl.refine[OF Reachability_Impl_axioms]
  check_all_impl.refine[OF Reachability_Impl_axioms]
*)

lemma certify_unreachable_alt_def:
  "certify_unreachable F \<equiv> do {
  b1 \<leftarrow> PR_CONST check_all;
  b2 \<leftarrow> PR_CONST (check_final F);
  RETURN (b1 \<and> b2)
  }"
  unfolding certify_unreachable_def PR_CONST_def .

definition certify_unreachable' where
  "certify_unreachable' L' M' \<equiv> do {
  b1 \<leftarrow> PR_CONST check_all' L' M';
  b2 \<leftarrow> PR_CONST check_final' L' M';
  PRINT_CHECK STR ''All check: '' b1;
  PRINT_CHECK STR ''Target property check: '' b2;
  RETURN (b1 \<and> b2)
  }"

lemma certify_unreachable'_refine:
  "certify_unreachable' L M \<le> certify_unreachable F"
  unfolding certify_unreachable'_def certify_unreachable_def PR_CONST_def check_final_alt_def
  unfolding PRINT_CHECK_def
  by simp refine_mono

sepref_register "PR_CONST check_all" "PR_CONST (check_final F)"

lemmas [sepref_fr_rules] =
  check_all_impl.refine_raw
  check_final_impl.refine_raw

sepref_thm certify_unreachable_impl' is
  "uncurry (PR_CONST certify_unreachable')" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding certify_unreachable'_def by sepref

lemma certify_unreachable_correct':
  "(uncurry0 (certify_unreachable' L M), uncurry0 (SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) s' \<and> F s'))))
    \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using certify_unreachable_correct[OF F_mono] certify_unreachable'_refine
  by (clarsimp simp: pw_le_iff pw_nres_rel_iff) fast

lemmas certify_unreachable_impl'_refine =
  certify_unreachable_impl'.refine_raw[
    unfolded is_member_impl_def[OF pure_K left_unique_K right_unique_K]
  ]

concrete_definition (in -) certify_unreachable_impl_inner
  uses Reachability_Impl.certify_unreachable_impl'_refine is "(uncurry ?f,_)\<in>_"

lemmas certify_unreachable'_impl_hnr =
  certify_unreachable_impl_inner.refine[OF Reachability_Impl_axioms]

(* lemmas certify_unreachable_impl_refine =
  certify_unreachable_impl.refine_raw[
    unfolded PR_CONST_def is_member_impl_def[OF pure_K left_unique_K right_unique_K]
  ]

concrete_definition (in -) certify_unreachable_impl
  uses Reachability_Impl.certify_unreachable_impl_refine is "(uncurry ?f,_)\<in>_"
 *)

context
  fixes L_list and M_table
  assumes L_impl[sepref_fr_rules]:
    "(uncurry0 (return L_list), uncurry0 (RETURN (PR_CONST L))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a lso_assn K"
  assumes M_impl[sepref_fr_rules]:
    "(uncurry0 M_table, uncurry0 (RETURN (PR_CONST M))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' K (lso_assn A)"
begin

lemmas [sepref_fr_rules] = certify_unreachable'_impl_hnr

sepref_register "PR_CONST certify_unreachable'" :: "'k set \<Rightarrow> ('k, 'b set) i_map \<Rightarrow> bool nres"

sepref_thm certify_unreachable_impl is
  "uncurry0 (PR_CONST certify_unreachable' (PR_CONST L) (PR_CONST M))" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  by sepref

lemmas certify_unreachable_impl_refine =
  certify_unreachable_impl.refine_raw[
    unfolded PR_CONST_def is_member_impl_def[OF pure_K left_unique_K right_unique_K],
    FCOMP certify_unreachable_correct'
  ]

end

concrete_definition (in -) certify_unreachable_impl
  uses Reachability_Impl.certify_unreachable_impl_refine is "(uncurry0 ?f,_)\<in>_"

(*
lemmas certify_unreachable_impl_refine =
  certify_unreachable_impl.refine_raw[FCOMP certify_unreachable_correct']
*)

(*
concrete_definition (in -) certify_unreachable_impl
  uses Reachability_Impl.certify_unreachable_impl is "(uncurry0 ?f,_)\<in>_"
*)

paragraph \<open>Debugging\<close>



definition (in -)
  "mk_st_string s1 s2 \<equiv> STR ''<'' + s1 + STR '', '' + s2 + STR ''>''"

(* XXX Error: 'Tactic failed' inside context *)
lemma [sepref_import_param]: "(mk_st_string, mk_st_string) \<in> Id \<rightarrow> Id \<rightarrow> Id"
  by simp

definition (in -)
  "PRINTLN = RETURN o println"

lemma (in -) [sepref_import_param]:
  "(println, println) \<in> Id \<rightarrow> Id"
  by simp

sepref_definition (in -) print_line_impl is
  "PRINTLN" :: " id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PRINTLN_def by sepref

sepref_register (in -) PRINTLN

lemmas [sepref_fr_rules] = print_line_impl.refine

context
  fixes show_loc :: "'k \<Rightarrow> String.literal nres" and show_dbm :: "'b \<Rightarrow> String.literal nres"
    and show_dbm_impl and show_loc_impl
  assumes show_dbm_impl: "(show_dbm_impl, show_dbm) \<in> A\<^sup>d \<rightarrow>\<^sub>a id_assn"
  assumes show_loc_impl: "(show_loc_impl, show_loc) \<in> K\<^sup>d \<rightarrow>\<^sub>a id_assn"
begin

lemma [sepref_fr_rules]: "(show_dbm_impl, PR_CONST show_dbm) \<in> A\<^sup>d \<rightarrow>\<^sub>a id_assn"
  using show_dbm_impl unfolding PR_CONST_def .

lemma [sepref_fr_rules]: "(show_loc_impl, PR_CONST show_loc) \<in> K\<^sup>d \<rightarrow>\<^sub>a id_assn"
  using show_loc_impl unfolding PR_CONST_def .

definition
  "show_st \<equiv> \<lambda> (l, M).  do {
    s1 \<leftarrow> PR_CONST show_loc l;
    s2 \<leftarrow> PR_CONST show_dbm M;
    RETURN (mk_st_string s1 s2)
  }"

sepref_register "PR_CONST show_st" "PR_CONST show_loc" "PR_CONST show_dbm"

sepref_thm show_st_impl is
  "PR_CONST show_st" :: "(K \<times>\<^sub>a A)\<^sup>d \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def unfolding show_st_def by sepref

lemmas [sepref_fr_rules] = show_st_impl.refine_raw

definition check_prop_fail where
  "check_prop_fail L' M' = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  r \<leftarrow> monadic_list_all_fail' (\<lambda>l. do {
    let S = op_map_lookup l M';
    case S of None \<Rightarrow> RETURN None | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all_fail (\<lambda>s.
        RETURN (PR_CONST P' (l, s))
      ) xs;
      RETURN (case r of None \<Rightarrow> None | Some r \<Rightarrow> Some (l, r))
      (* case r of None \<Rightarrow> RETURN None | Some r \<Rightarrow> RETURN (Some (l, r)) *)
    }
    }
  ) l;
  case r of None \<Rightarrow> RETURN None |
    Some (l, M) \<Rightarrow> do {
    s \<leftarrow> PR_CONST show_st (l, COPY M);
    PRINTLN (STR ''Prop failed for: '');
    PRINTLN s;
    RETURN (Some (l, M))
  }
  }"

sepref_thm check_prop_fail_impl is
  "uncurry check_prop_fail" :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>d \<rightarrow>\<^sub>a option_assn (K \<times>\<^sub>a A)"
  unfolding check_prop_fail_def list_of_set_def[symmetric]
  unfolding monadic_list_all_fail'_alt_def monadic_list_all_fail_alt_def
  by sepref

end (* Anonymous context *)

definition
  "check_invariant_fail L' M' \<equiv> do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L');
  monadic_list_all_fail' (\<lambda>l.
  do {
    case op_map_lookup l M' of None \<Rightarrow> RETURN None  | Some xs \<Rightarrow> do {
    let succs = PR_CONST succs l xs;
    monadic_list_all_fail' (\<lambda>(l', xs). do {
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      if xs = [] then RETURN None
      else do {
        b1 \<leftarrow> RETURN (l' \<in> L'); (* XXX Optimize this *)
        if b1 then do {
        case op_map_lookup l' M' of None \<Rightarrow> RETURN (Some (Inl (Inr (l, l', xs)))) | Some ys \<Rightarrow> do {
          ys \<leftarrow> SPEC (\<lambda>xs.  set xs  = ys);
          b2 \<leftarrow> monadic_list_all_fail (\<lambda>x'.
            monadic_list_ex (\<lambda>y. RETURN (PR_CONST less_eq x' y)) ys
          ) xs;
          case b2 of None \<Rightarrow> RETURN None | Some M \<Rightarrow> RETURN (Some (Inr (l, M)))
        }
      }
      else RETURN (Some (Inl (Inl (l, l', xs))))
    }
    }) succs
  }
  }
  ) l
}"

sepref_thm check_invariant_fail_impl is
  "uncurry check_invariant_fail"
  :: "(lso_assn K)\<^sup>k *\<^sub>a table_assn\<^sup>k \<rightarrow>\<^sub>a
      option_assn ((K \<times>\<^sub>a K \<times>\<^sub>a (list_assn A) +\<^sub>a K \<times>\<^sub>a K \<times>\<^sub>a (list_assn A)) +\<^sub>a K \<times>\<^sub>a A)"
  unfolding PR_CONST_def
  unfolding check_invariant_fail_def list_of_set_def[symmetric]
  unfolding monadic_list_all_fail'_alt_def monadic_list_all_fail_alt_def
  unfolding monadic_list_all_def monadic_list_ex_def
  by sepref

lemmas check_invariant_fail_impl_refine = check_invariant_fail_impl.refine_raw[
  unfolded is_member_impl_def[OF pure_K left_unique_K right_unique_K]
]

end (* Reachability Impl *)

concrete_definition (in -) check_prop_fail_impl
  uses Reachability_Impl.check_prop_fail_impl.refine_raw is "(uncurry ?f,_)\<in>_"

concrete_definition (in -) check_invariant_fail_impl
  uses Reachability_Impl.check_invariant_fail_impl_refine is "(uncurry ?f,_)\<in>_"

export_code certify_unreachable_impl check_prop_fail_impl check_invariant_fail_impl
in SML module_name Test

end (* Theory *)