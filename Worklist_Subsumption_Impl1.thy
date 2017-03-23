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

  locale Worklist2_Defs = Worklist1_Defs +
    fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn"
    fixes succsi :: "'ai \<Rightarrow> 'ai list Heap"
    fixes a\<^sub>0i :: "'ai Heap"
    fixes Fi :: "'ai \<Rightarrow> bool Heap"
    fixes Lei :: "'ai \<Rightarrow> 'ai \<Rightarrow> bool Heap"

  locale Worklist2 = Worklist2_Defs + Worklist1 +
    (* TODO: This is the easy variant: Operations cannot depend on additional heap. *)
    assumes [sepref_fr_rules]: "(uncurry0 a\<^sub>0i, uncurry0 (RETURN (PR_CONST a\<^sub>0))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A"
    assumes [sepref_fr_rules]: "(Fi,RETURN o PR_CONST F) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    assumes [sepref_fr_rules]: "(uncurry Lei,uncurry (RETURN oo PR_CONST op \<preceq>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    assumes [sepref_fr_rules]: "(succsi,RETURN o PR_CONST succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A"
  begin
    sepref_register "PR_CONST a\<^sub>0" "PR_CONST F" "PR_CONST op \<preceq>" "PR_CONST succs"

    lemma [def_pat_rules]:
      "a\<^sub>0 \<equiv> UNPROTECT a\<^sub>0" "F \<equiv> UNPROTECT F" "op \<preceq> \<equiv> UNPROTECT op \<preceq>" "succs \<equiv> UNPROTECT succs"
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
      uses Worklist2.filter_insert_wait_impl.refine_raw is "(uncurry ?f, _) \<in> _"

    lemmas [sepref_fr_rules] = filter_insert_wait_impl.refine[OF Worklist2_axioms]

    sepref_register filter_insert_wait


    lemmas [sepref_fr_rules] = hd_tl_hnr

    sepref_thm worklist_algo2_impl is "uncurry0 worklist_algo1" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding worklist_algo1_def add_succ1_alt_def PR_CONST_def
      supply [[goals_limit = 1]]
      supply conv_to_is_Nil[simp]
      apply (rewrite in "Let \<hole> _" lso_fold_custom_empty)
      unfolding fold_lso_bex
      unfolding take_from_list_alt_def
      apply (rewrite in "[a\<^sub>0]" HOL_list.fold_custom_empty)
      by sepref

    concrete_definition (in -) worklist_algo2_impl
    for Lei a\<^sub>0i Fi succsi
    uses Worklist2.worklist_algo2_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"

  end

  context Worklist2 begin

    lemma hnr_F_reachable: "(uncurry0 (worklist_algo2_impl Lei a\<^sub>0i Fi succsi), uncurry0 (RETURN F_reachable))
      \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      using worklist_algo2_impl.refine[OF Worklist2_axioms,
        FCOMP worklist_algo1_ref[THEN nres_relI],
        FCOMP worklist_algo_correct[THEN Id_SPEC_refine, THEN nres_relI]]
      by (simp add: RETURN_def)

  end

  context Worklist1 begin
    sepref_decl_op F_reachable :: "bool_rel" .
    lemma [def_pat_rules]: "F_reachable \<equiv> op_F_reachable" by simp


    lemma hnr_op_F_reachable:
      assumes "GEN_ALGO a\<^sub>0i (\<lambda>a\<^sub>0i. (uncurry0 a\<^sub>0i, uncurry0 (RETURN a\<^sub>0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A)"
      assumes "GEN_ALGO Fi (\<lambda>Fi. (Fi,RETURN o F) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO Lei (\<lambda>Lei. (uncurry Lei,uncurry (RETURN oo op \<preceq>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO succsi (\<lambda>succsi. (succsi,RETURN o succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A)"
      shows "(uncurry0 (worklist_algo2_impl Lei a\<^sub>0i Fi succsi), uncurry0 (RETURN (PR_CONST op_F_reachable)))
        \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    proof -
      from assms interpret Worklist2 E a\<^sub>0 F "op\<preceq>" succs A succsi a\<^sub>0i Fi Lei
        by (unfold_locales; simp add: GEN_ALGO_def)

      from hnr_F_reachable show ?thesis by simp
    qed

    sepref_decl_impl hnr_op_F_reachable .
  end

end
