theory Worklist_Subsumption_Impl1
  imports "../IICF/IICF" Worklist_Subsumption1
begin

  subsection \<open>Implementation on Lists\<close>

  (* XXX Duplication, see DBM_Operations_Impl *)
  lemma list_ex_foldli:
    "list_ex P xs = foldli xs Not (\<lambda> x y. P x \<or> y) False"
   apply (induction xs)
   apply (simp; fail)
   subgoal for x xs
    apply simp
    apply (induction xs)
   by auto
  done

  lemma list_filter_foldli:
    "[x \<leftarrow> xs. P x] = rev (foldli xs (\<lambda> x. True) (\<lambda> x xs. if P x then x # xs else xs) [])"
    (is "_ = rev (foldli xs ?c ?f [])")
  proof -
    have *:
      "rev (foldli xs ?c ?f (ys @ zs)) = rev zs @ rev (foldli xs ?c ?f ys)" for xs ys zs
    proof (induction xs arbitrary: ys)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs)
      from Cons[of "x # ys"] Cons[of ys] show ?case by simp
    qed
    show ?thesis
      apply (induction xs)
       apply (simp; fail)
      apply simp
      apply (subst (2) *[of _ "[]", simplified])
      by simp
  qed

  (* XXX Move *)
  context notes [split!] = list.split begin
  sepref_decl_op list_hdtl: "\<lambda> (x # xs) \<Rightarrow> (x, xs)" :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel"
    by auto
  end

  context Worklist4_Impl
  begin
    sepref_register "PR_CONST a\<^sub>0" "PR_CONST F'" "PR_CONST op \<unlhd>" "PR_CONST succs" "PR_CONST empty"

    lemma [def_pat_rules]:
      "a\<^sub>0 \<equiv> UNPROTECT a\<^sub>0" "F' \<equiv> UNPROTECT F'" "op \<unlhd> \<equiv> UNPROTECT op \<unlhd>" "succs \<equiv> UNPROTECT succs"
      "empty \<equiv> UNPROTECT empty"
      by simp_all

    (* XXX Now obsolete *)
    lemma take_from_mset_as_mop_mset_pick: "take_from_mset = mop_mset_pick"
      apply (intro ext)
      unfolding take_from_mset_def[abs_def]
      by (auto simp: pw_eq_iff refine_pw_simps)

    lemma take_from_list_alt_def:
      "take_from_list xs = do {_ \<leftarrow> ASSERT (xs \<noteq> []); RETURN (hd_tl xs)}"
      unfolding take_from_list_def by (auto simp: pw_eq_iff refine_pw_simps)

    lemma [safe_constraint_rules]: "CN_FALSE is_pure A \<Longrightarrow> is_pure A" by simp


    sepref_thm filter_insert_wait_impl is
      "uncurry (RETURN oo PR_CONST filter_insert_wait)" :: "(list_assn A)\<^sup>d *\<^sub>a A\<^sup>d \<rightarrow>\<^sub>a list_assn A"
      unfolding filter_insert_wait_alt_def list_ex_foldli list_filter_foldli
      unfolding HOL_list.fold_custom_empty
      unfolding PR_CONST_def
      by sepref

    concrete_definition (in -) filter_insert_wait_impl
      uses Worklist4_Impl.filter_insert_wait_impl.refine_raw is "(uncurry ?f, _) \<in> _"

    lemmas [sepref_fr_rules] = filter_insert_wait_impl.refine[OF Worklist4_Impl_axioms]

    sepref_register filter_insert_wait


    lemmas [sepref_fr_rules] = hd_tl_hnr

    sepref_thm worklist_algo2_impl is "uncurry0 worklist_algo2" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding worklist_algo2_def worklist_algo2'_def add_succ2_alt_def PR_CONST_def
      supply [[goals_limit = 1]]
      supply conv_to_is_Nil[simp]
      apply (rewrite in "Let \<hole> _" lso_fold_custom_empty)
      unfolding fold_lso_bex
      unfolding take_from_list_alt_def
      apply (rewrite in "[a\<^sub>0]" HOL_list.fold_custom_empty)
      by sepref

    concrete_definition (in -) worklist_algo2_impl
    for Lei a\<^sub>0i Fi succsi emptyi
    uses Worklist4_Impl.worklist_algo2_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"

    lemma worklist_algo2_impl_hnr_F_reachable:
      "(uncurry0 (worklist_algo2_impl Lei a\<^sub>0i Fi succsi emptyi), uncurry0 (RETURN F_reachable))
      \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      using worklist_algo2_impl.refine[OF Worklist4_Impl_axioms,
        FCOMP worklist_algo2_ref[THEN nres_relI],
        FCOMP worklist_algo''_correct[THEN Id_SPEC_refine, THEN nres_relI]]
      by (simp add: RETURN_def)

  end -- \<open>Worklist4 Impl\<close>

  context Worklist4 begin

    sepref_decl_op F_reachable :: "bool_rel" .
    lemma [def_pat_rules]: "F_reachable \<equiv> op_F_reachable" by simp


    lemma hnr_op_F_reachable:
      assumes "GEN_ALGO a\<^sub>0i (\<lambda>a\<^sub>0i. (uncurry0 a\<^sub>0i, uncurry0 (RETURN a\<^sub>0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A)"
      assumes "GEN_ALGO Fi (\<lambda>Fi. (Fi,RETURN o F') \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO Lei (\<lambda>Lei. (uncurry Lei,uncurry (RETURN oo op \<unlhd>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO succsi (\<lambda>succsi. (succsi,RETURN o succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A)"
      assumes "GEN_ALGO emptyi (\<lambda>Fi. (Fi,RETURN o empty) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      shows
        "(uncurry0 (worklist_algo2_impl Lei a\<^sub>0i Fi succsi emptyi), uncurry0 (RETURN (PR_CONST op_F_reachable)))
        \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    proof -
      from assms interpret Worklist4_Impl E a\<^sub>0 F "op\<preceq>" succs empty "op \<unlhd>" F' A succsi a\<^sub>0i Fi Lei emptyi
        by (unfold_locales; simp add: GEN_ALGO_def)

      from worklist_algo2_impl_hnr_F_reachable show ?thesis by simp
    qed

    sepref_decl_impl hnr_op_F_reachable .

  end -- \<open>Worklist4\<close>

end -- \<open>End of Theory\<close>