theory Unreachability_Certification
  imports Worklist_Locales "../Simulation_Graphs_Certification" Unified_PW_Impl Leadsto_Impl
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

lemma monadic_list_all_is_RETURN:
  "\<exists> r. monadic_list_all (\<lambda>x. RETURN (P x)) xs = RETURN r"
proof (induction xs)
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  then show ?case
    by (cases "P x") (auto simp: monadic_list_all_def)
qed

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
    by simp (rule monadic_list_all_is_RETURN)
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
  fixes succs :: "_ \<Rightarrow> _"
  assumes succs_correct:
    "\<And> l. \<forall> s \<in> xs. P (l, s)
  \<Longrightarrow> {(l', s')| l' ys s'. (l', ys) \<in> set (succs l xs) \<and> s' \<in> ys}
    = (\<Union> s \<in> xs. Collect (E (l, s)))"

context Reachability_Invariant_paired_defs
begin

context
  fixes P :: "('l \<times> 's) \<Rightarrow> bool"
begin

(*
definition "check_prop \<equiv>
do {
  l \<leftarrow> SPEC (\<lambda>l. set l = L);
  nfoldli l (\<lambda>b. b) (\<lambda>l _. RETURN (\<forall> s \<in> M l. P (l, s))) True
}
"
*)

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

context Reachability_Impl_pre
begin

definition "check_invariant \<equiv>
do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = L);
  monadic_list_all (\<lambda>l.
  do {
    (* as    \<leftarrow> SPEC (\<lambda>xs. set xs = M l); *)
    let as = M l;
    (* succs \<leftarrow> SPEC (\<lambda>xs. set xs = succs l as); *)
    let succs = succs l as;
    monadic_list_all (\<lambda>(l', xs).
    do {
      b1 \<leftarrow> RETURN (l' \<in> L);
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      ys \<leftarrow> SPEC (\<lambda>xs. set xs = M l');
      b2 \<leftarrow> monadic_list_all (\<lambda>x.
        monadic_list_ex (\<lambda>y. RETURN (x \<preceq> y)) ys
      ) xs;
      RETURN (b1 \<and> b2)
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
    (\<forall> l \<in> L. (\<forall> (l',ys) \<in> set (succs l (M l)). l' \<in> L \<and> (\<forall> s' \<in> ys. (\<exists> s'' \<in> M l'. s' \<preceq> s'')))))"
    unfolding check_invariant_def
    by (refine_vcg monadic_list_all_rule monadic_list_ex_rule) (auto simp: list_all_iff list_ex_iff)
  also have "\<dots> \<le> ?rhs"
    by (auto; smt ** case_prodI2 case_prod_conv)
  finally show ?thesis .
qed

definition
  "check_all \<equiv> do {
  b1 \<leftarrow> RETURN (l\<^sub>0 \<in> L);
  b2 \<leftarrow> RETURN (P (l\<^sub>0, s\<^sub>0));
  xs \<leftarrow> SPEC (\<lambda>xs. set xs = M l\<^sub>0);
  b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (s\<^sub>0 \<preceq> s)) xs;
  b4 \<leftarrow> check_prop P;
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

end

context Reachability_Impl_pre
begin

lemma check_all_correct:
  "check_all \<le> SPEC (\<lambda>r. r \<longrightarrow> Unreachability_Invariant_paired (\<preceq>) (\<prec>) M L l\<^sub>0 s\<^sub>0 E P)"
  unfolding check_all_def
  by (refine_vcg check_prop_correct check_invariant_correct monadic_list_ex_rule;
      standard; auto simp: list_ex_iff)

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
  apply (subst list_assn_aux_len; clarsimp)
  apply (induction rule: list_induct2)
  apply sep_auto
  apply sep_auto
  apply (erule ent_frame_fwd, frame_inference)
  apply sep_auto
  done

theorem copy_list_refine:
  fixes A :: "'b \<Rightarrow> 'a \<Rightarrow> assn"
    and x :: "'b list"
    and xi :: "'a list"
    and copy :: "'a \<Rightarrow> 'a Heap"
  assumes
    copy: "(copy, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  shows
    "hn_refine (hn_ctxt (list_assn A) x xi) (copy_list_impl copy $ xi) (hn_ctxt (list_assn A) x xi)
      (list_assn A) (copy_list (RETURN \<circ> COPY) $ x)"
  unfolding copy_list_def copy_list_impl_def
  apply sep_auto
  apply (rule hnr_bind)
    apply (rule monadic_nfoldli_refine_aux'[
        where S = "set x" and Rs = "list_assn A" and Rl = A and Rl' = A and Rl'' = A and \<Gamma> = emp,
          THEN hn_refine_cons_pre[rotated]])
        apply sep_auto
       apply sep_auto
  subgoal
    apply standard
    apply (sep_auto simp: pure_def)
    done
      apply sep_auto
      prefer 3
  subgoal
    apply (sep_auto simp: pure_def)
    done
  subgoal
    supply [sep_heap_rules]  = copy[to_hnr, unfolded hn_refine_def, simplified]
    apply standard
    apply sep_auto
      (* Frame *)
    by (smt assn_times_comm ent_refl ent_star_mono hn_ctxt_def invalidate_clone star_aci(3))

    apply sep_auto
   apply sep_auto
   defer
   apply (rule frame3)
  apply rule
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

locale Reachability_Impl =
  Reachability_Impl_pre less_eq _ "\<lambda>x. case M x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  for less_eq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and M :: "'k \<Rightarrow> 'b set option" +
  fixes A :: "'b \<Rightarrow> ('bi :: heap) \<Rightarrow> assn"
    and K :: "'k \<Rightarrow> ('ki :: {hashable,heap}) \<Rightarrow> assn" and F
    and Fi and keyi and Pi and copyi and Lei and l\<^sub>0i and s\<^sub>0i
  and L_list :: "'ki list" and M_table :: "('ki, 'bi list) hashtable"
  assumes L_impl[sepref_fr_rules]:
    "(uncurry0 (return L_list), uncurry0 (RETURN (PR_CONST L))) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a lso_assn K"
  assumes M_impl:
    "(uncurry0 (return M_table),
      uncurry0 (RETURN (PR_CONST M))
     ) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' K (lso_assn A)"
  assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST fst) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a K"
  assumes copyi[sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  assumes [sepref_fr_rules]: "(Pi,RETURN o PR_CONST P) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]: "(Fi,RETURN o PR_CONST F) \<in> (prod_assn K A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  assumes [sepref_fr_rules]:
    "(uncurry succsi,uncurry (RETURN oo PR_CONST succs)) \<in> K\<^sup>k *\<^sub>a (lso_assn A)\<^sup>k \<rightarrow>\<^sub>a list_assn (K \<times>\<^sub>a lso_assn A)"
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

abbreviation "hm_assn \<equiv> hm.hms_assn' K (lso_assn A)"

lemma check_final_alt_def:
  "check_final F = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l (PR_CONST M);
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      monadic_list_all (\<lambda>s.
        RETURN (\<not> PR_CONST F (l, s))
      ) xs
    }
    }
  ) l
  }
"
  unfolding check_final_def
  apply (rule arg_cong2[where f = Refine_Basic.bind])
   apply simp
  apply (fo_rule arg_cong)
  apply (auto split: option.split simp: monadic_list_all_def bind_RES)
  done

lemma check_prop_alt_def:
  "check_prop P = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l. do {
    let (S, M) = op_map_extract l (PR_CONST M);
    if is_None S then RETURN True else do {
      let S = the S;
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P (l, s))
      ) xs;
      let M = (M(l \<mapsto> S));
      RETURN r
    }
    }
  ) l
  }
"
  unfolding check_prop_def
  apply auto
  apply (rule arg_cong2[where f = Refine_Basic.bind])
   apply simp
  apply (fo_rule arg_cong)
  apply (rule ext)
  apply (auto split: option.split_asm simp: )
  unfolding monadic_list_all_def
  unfolding bind_RES
  apply auto
  oops

lemma check_prop_alt_def:
  "check_prop P = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l. do {
    let S = op_map_lookup l (PR_CONST M);
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P (l, s))
      ) xs;
      RETURN r
    }
    }
  ) l
  }
"
  unfolding check_prop_def
  apply auto
  apply (rule arg_cong2[where f = Refine_Basic.bind])
   apply simp
  apply (fo_rule arg_cong)
  apply (rule ext)
  apply (auto split: option.split simp: bind_RES)
  done

lemma check_prop_alt_def2:
  "check_prop P = do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l. do {
    let (S, M) = op_map_extract l (PR_CONST M);
    case S of None \<Rightarrow> RETURN True | Some S \<Rightarrow> do {
      xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
      r \<leftarrow> monadic_list_all (\<lambda>s.
        RETURN (PR_CONST P (l, s))
      ) xs;
      (* let M = (M(l \<mapsto> S)); *)
      RETURN r
    }
    }
  ) l
  }
"
  unfolding check_prop_def
  apply auto
  apply (rule arg_cong2[where f = Refine_Basic.bind])
   apply simp
  apply (fo_rule arg_cong)
  apply (rule ext)
  apply (auto split: option.split simp: bind_RES)
  done

lemma M_listD:
  assumes "M l = Some S"
  shows "\<exists> xs. set xs = S"
  sorry

lemma L_listD:
  shows "\<exists> xs. set xs = L"
  sorry

lemma succs_empty:
  "succs l {} = []"
  sorry

definition
  "check_invariant' \<equiv> do {
  l \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
  monadic_list_all (\<lambda>l.
  do {
    case op_map_lookup l  (PR_CONST M) of None \<Rightarrow> RETURN True  | Some xs \<Rightarrow> do {
    let succs = PR_CONST succs l xs;
    monadic_list_all (\<lambda>(l', xs).
    do {
      b1 \<leftarrow> RETURN (l' \<in> PR_CONST L);
      if b1 then do {
      xs \<leftarrow> SPEC (\<lambda>xs'. set xs' = xs);
      case op_map_lookup l' (PR_CONST M) of None \<Rightarrow> RETURN (xs = []) | Some ys \<Rightarrow> do {
      ys \<leftarrow> SPEC (\<lambda>xs.  set xs  = ys);
      b2 \<leftarrow> monadic_list_all (\<lambda>x'.
        monadic_list_ex (\<lambda>y. RETURN (PR_CONST less_eq x' y)) ys
      ) xs;
      RETURN b2
      }}
      else RETURN False
    }
    ) succs
  }
  }
  ) l
}"

lemma check_invariant'_refine:
  "check_invariant' \<le> check_invariant"
  unfolding check_invariant_def check_invariant'_def
  unfolding PR_CONST_def
  apply refine_mono
  apply (auto split: option.splits simp: succs_empty)
   defer
   apply refine_mono
   apply auto
    apply refine_mono
    apply auto
    apply (auto split: option.splits)
  subgoal
    apply (auto simp: bind_RES monadic_list_all_False dest: M_listD)
    done
subgoal
  apply (auto simp: bind_RES monadic_list_all_False dest: M_listD)
  apply (rule less_eq_Sup)
   apply auto
  sorry
  apply (auto simp: bind_RES monadic_list_all_False dest: M_listD)
  apply (intro less_eq_Sup)
  apply auto
  apply (intro less_eq_Sup)
   apply auto
subgoal for x xa x2 a xs ys
    apply (cases "monadic_list_all
     (\<lambda>x. monadic_list_ex (\<lambda>y. RETURN (less_eq x y)) ys)
     xs")
     apply (auto simp: bind_RES)
     apply (intro less_eq_Sup)
      apply (auto dest: )
    using monadic_list_all_list_ex_is_RETURN[of "\<lambda> x y. less_eq x y" ys xs]
    apply auto
    done
  subgoal
    by (auto dest: M_listD)
  subgoal
    sorry
  done

lemmas [safe_constraint_rules] = pure_K left_unique_K right_unique_K

lemmas [sepref_fr_rules] = lso_id_hnr

sepref_register "PR_CONST L" "list_of_set" "PR_CONST P" "PR_CONST F" "PR_CONST succs"
  "PR_CONST less_eq"
  "PR_CONST M" :: "('k, 'b set) i_map"

lemma [sepref_import_param]: "(id, id) \<in> (Id :: (bool \<times> bool) set) \<rightarrow> Id"
  by simp

lemmas [sepref_fr_rules] = M_impl

sepref_definition check_prop_impl_wrong is
  "uncurry0 (check_prop P)" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding check_prop_alt_def2 list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

sepref_decl_impl "map_lookup":
  copy_list_lso_assn_refine[OF copyi, THEN hms_hm.hms_lookup_hnr]
  uses op_map_lookup.fref[where V = Id] .

sepref_definition check_prop_impl is
  "uncurry0 (PR_CONST (check_prop P))" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_prop_alt_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

sepref_definition check_final_impl is
  "uncurry0 (PR_CONST (check_final F))" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding PR_CONST_def
  unfolding check_final_alt_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def
  by sepref

definition
  "is_member x \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = PR_CONST L);
    monadic_list_ex (\<lambda>y. RETURN (y = x)) xs
  }"

definition
  "L_member x \<equiv> x \<in> PR_CONST L"

lemma is_member_refine:
  "is_member x \<le> RETURN (x \<in> L)"
  unfolding is_member_def by (refine_vcg monadic_list_ex_rule) (auto simp: list_ex_iff)

lemma is_member_correct:
  "(is_member, \<lambda>x. RETURN (x \<in> PR_CONST L)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using is_member_refine by (auto simp: pw_le_iff pw_nres_rel_iff)

lemma is_member_correct'':
  "(is_member, RETURN o PR_CONST L_member) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using is_member_refine by (auto simp: L_member_def pw_le_iff pw_nres_rel_iff)

lemma is_member_refine':
  "is_member x \<le> SPEC (\<lambda> r. r \<longleftrightarrow> x \<in> L)"
  unfolding is_member_def by (refine_vcg monadic_list_ex_rule) (auto simp: list_ex_iff)

lemma is_member_correct':
  "(is_member, \<lambda>x. SPEC (\<lambda>r. r \<longleftrightarrow> (x \<in> L))) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using is_member_refine by (auto simp: pw_le_iff pw_nres_rel_iff)

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

sepref_thm is_member_impl is
  "is_member" :: "K\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding is_member_def monadic_list_ex_def list_of_set_def[symmetric] by sepref

lemmas [sepref_fr_rules] = is_member_impl.refine_raw[FCOMP is_member_correct'']

sepref_register L_member

sepref_definition check_invariant_impl is
  "uncurry0 check_invariant'" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding check_invariant'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  unfolding L_member_def[symmetric]
  by sepref

lemma check_invariant'_correct:
  "(uncurry0 check_invariant', uncurry0 (PR_CONST check_invariant)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using check_invariant'_refine by (auto simp: pw_le_iff pw_nres_rel_iff)

lemmas check_invariant_impl_refine = check_invariant_impl.refine[FCOMP check_invariant'_correct]

definition
  "check_all' \<equiv> do {
  b1 \<leftarrow> RETURN (PR_CONST l\<^sub>0 \<in> PR_CONST L);
  b2 \<leftarrow> RETURN (PR_CONST P (PR_CONST l\<^sub>0, PR_CONST s\<^sub>0));
  let S = op_map_lookup (PR_CONST l\<^sub>0) (PR_CONST M);
  case S of None \<Rightarrow> RETURN False | Some S \<Rightarrow> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    b3 \<leftarrow> monadic_list_ex (\<lambda>s. RETURN (PR_CONST less_eq (PR_CONST s\<^sub>0) s)) xs;
    b4 \<leftarrow> PR_CONST (check_prop P);
    if b1 \<and> b2 \<and> b3 \<and> b4 then PR_CONST check_invariant else RETURN False
  }
  }
"

lemma monadic_list_all_gt_SUCCEED':
  "monadic_list_all (\<lambda>x. RETURN (PP x)) xs > SUCCEED" for PP
  by (rule monadic_list_all_gt_SUCCEED) auto

lemma check_prop_gt_SUCCEED:
  "check_prop P > SUCCEED"
  unfolding check_prop_def using L_listD
  by (fastforce split: option.split dest: M_listD
        intro: monadic_list_all_gt_SUCCEED bind_RES_gt_SUCCEED_I
     )

lemma check_all'_refine:
  "check_all' \<le> check_all"
  unfolding check_all_def check_all'_def PR_CONST_def Let_def
  apply refine_mono
  apply (cases "op_map_lookup l\<^sub>0 M"; simp add: bind_RES)
  apply (cases "check_prop P")
  using check_prop_gt_SUCCEED
   apply (auto intro: less_eq_Sup simp: bind_RES)
  done

lemma check_all'_correct:
  "(uncurry0 check_all', uncurry0 (PR_CONST check_all)) \<in> Id \<rightarrow> \<langle>bool_rel\<rangle>nres_rel"
  using check_all'_refine by (auto simp: pw_le_iff pw_nres_rel_iff)

sepref_register "PR_CONST check_invariant" check_prop: "PR_CONST (check_prop P)"

sepref_register "PR_CONST l\<^sub>0" "PR_CONST s\<^sub>0"

lemmas [sepref_fr_rules] =
  check_prop_impl.refine
  check_invariant_impl_refine

sepref_definition check_all_impl is
  "uncurry0 check_all'" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  unfolding check_all'_def list_of_set_def[symmetric]
  unfolding monadic_list_all_def monadic_list_ex_def
  unfolding L_member_def[symmetric]
  by sepref

lemmas check_all_impl_refine = check_all_impl.refine[FCOMP check_all'_correct]

end (* Reachability Impl *)

end (* Theory *)