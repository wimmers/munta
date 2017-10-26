theory Unified_PW_Impl
  imports Refine_Imperative_HOL.IICF Unified_PW_Hashing Heap_Hash_Map
begin

  subsection \<open>Implementation on Lists\<close>

  (* XXX Move *)
  context notes [split!] = list.split begin
  sepref_decl_op list_hdtl: "\<lambda> (x # xs) \<Rightarrow> (x, xs)" :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>list_rel"
    by auto
  end

  context Worklist_Map2_Defs
  begin

  lemma add_pw'_map2_alt_def:
    "add_pw'_map2 passed wait a =
     nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
      (\<lambda>a (passed, wait, _).
        do {
        (* ASSERT (\<forall> wait \<in> ran wait. \<forall> x \<in> set wait. \<not> empty x); *)
        RETURN (
          if empty a then
              (passed, wait, False)
          else if F' a then (passed, wait, True)
          else
            let
              k = key a;
              (v, passed) = op_map_extract k passed
            in
              case v of
                None \<Rightarrow> (passed(k \<mapsto> {COPY a}), a # wait, False) |
                Some passed' \<Rightarrow>
                  if \<exists> x \<in> passed'. a \<unlhd> x then
                    (passed(k \<mapsto> passed'), wait, False)
                  else
                    (passed(k \<mapsto> (insert (COPY a) passed')), a # wait, False)
          )
        }
      )
      (passed,wait,False)"
    unfolding add_pw'_map2_def id_def op_map_extract_def
    supply [simp del] = map_upd_eq_restrict
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    apply (rule ext)+
    by (auto 4 3 simp: Let_def split: option.split)

  end

  locale Worklist_Map2_Impl =
     Worklist4_Impl + Worklist_Map2_Impl_Defs + Worklist_Map2 +
    assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST key) \<in> A\<^sup>k \<rightarrow>\<^sub>a id_assn"
    assumes [sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
  begin
    sepref_register
      "PR_CONST a\<^sub>0" "PR_CONST F'" "PR_CONST op \<unlhd>" "PR_CONST succs" "PR_CONST empty" "PR_CONST key"
      "PR_CONST F"

    lemma [def_pat_rules]:
      "a\<^sub>0 \<equiv> UNPROTECT a\<^sub>0" "F' \<equiv> UNPROTECT F'" "op \<unlhd> \<equiv> UNPROTECT op \<unlhd>" "succs \<equiv> UNPROTECT succs"
      "empty \<equiv> UNPROTECT empty" "keyi \<equiv> UNPROTECT keyi" "F \<equiv> UNPROTECT F" "key \<equiv> UNPROTECT key"
      by simp_all

    lemma take_from_list_alt_def:
      "take_from_list xs = do {_ \<leftarrow> ASSERT (xs \<noteq> []); RETURN (hd_tl xs)}"
      unfolding take_from_list_def by (auto simp: pw_eq_iff refine_pw_simps)

    lemma [safe_constraint_rules]: "CN_FALSE is_pure A \<Longrightarrow> is_pure A" by simp

    lemmas [sepref_fr_rules] = hd_tl_hnr

    sepref_thm pw_algo_map2_impl is
      "uncurry0 (do {(r, p) \<leftarrow> pw_algo_map2; RETURN r})" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding pw_algo_map2_def add_pw'_map2_alt_def PR_CONST_def
      supply [[goals_limit = 1]]
      supply conv_to_is_Nil[simp]
      unfolding fold_lso_bex
      unfolding take_from_list_alt_def
      apply (rewrite in "{a\<^sub>0}" lso_fold_custom_empty)
      unfolding hm.hms_fold_custom_empty
      apply (rewrite in "[a\<^sub>0]" HOL_list.fold_custom_empty)
       apply (rewrite in "{}" lso_fold_custom_empty)
      unfolding F_split (* XXX Why? F only appears in the invariant *)
      by sepref

    concrete_definition (in -) pw_impl
    for Lei a\<^sub>0i Fi succsi emptyi
    uses Worklist_Map2_Impl.pw_algo_map2_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"

  end -- \<open>Worklist Map2 Impl\<close>

  locale Worklist_Map2_Impl_finite = Worklist_Map2_Impl + Worklist_Map2_finite
  begin

  (* XXX Missing review from Peter *)
  lemma pw_algo_map2_correct':
    "(do {(r, p) \<leftarrow> pw_algo_map2; RETURN r}) \<le> SPEC (\<lambda>brk. brk = F_reachable)"
    using pw_algo_map2_correct
    apply auto
    apply (cases pw_algo_map2)
     apply simp
    apply simp
    unfolding RETURN_def
    apply auto
      subgoal for X
      apply (cases "do {(r, p) \<leftarrow> RES X; RES {r}}")
         apply simp
         apply (subst (asm) Refine_Basic.bind_def)
         apply force
        subgoal premises prems for X'
        proof -
          have "r = F_reachable" if "(r, p) \<in> X" for r p
            using that prems(1) by auto
          then show ?thesis
            (* XXX Fix SMT *)
            by (smt
                bind_rule_complete inres_simps(2) mem_Collect_eq nofail_simps(2) prod_rule
                pw_ords_iff(1) singleton_conv2
               )
        qed
        done
      done

  lemma pw_impl_hnr_F_reachable:
    "(uncurry0 (pw_impl keyi copyi Lei a\<^sub>0i Fi succsi emptyi), uncurry0 (RETURN F_reachable))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    using
      pw_impl.refine[
        OF Worklist_Map2_Impl_axioms,
        FCOMP pw_algo_map2_correct'[THEN Id_SPEC_refine, THEN nres_relI]
        ]
    by (simp add: RETURN_def)

  end

  locale Worklist_Map2_Hashable =
    Worklist_Map2_Impl_finite  _ _ _ _ _ _ _ _ _ _ _ _ _ _ key
    for key :: "'a \<Rightarrow> 'ki :: {hashable, heap}"
  begin

    sepref_decl_op F_reachable :: "bool_rel" .
    lemma [def_pat_rules]: "F_reachable \<equiv> op_F_reachable" by simp


    lemma hnr_op_F_reachable:
      assumes "GEN_ALGO a\<^sub>0i (\<lambda>a\<^sub>0i. (uncurry0 a\<^sub>0i, uncurry0 (RETURN a\<^sub>0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A)"
      assumes "GEN_ALGO Fi (\<lambda>Fi. (Fi,RETURN o F') \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO Lei (\<lambda>Lei. (uncurry Lei,uncurry (RETURN oo op \<unlhd>)) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO succsi (\<lambda>succsi. (succsi,RETURN o succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A)"
      assumes "GEN_ALGO emptyi (\<lambda>Fi. (Fi,RETURN o empty) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST key) \<in> A\<^sup>k \<rightarrow>\<^sub>a id_assn"
      assumes [sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
      shows
        "(uncurry0 (pw_impl keyi copyi Lei a\<^sub>0i Fi succsi emptyi), uncurry0 (RETURN (PR_CONST op_F_reachable)))
        \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    proof -
      from assms interpret
        Worklist_Map2_Impl
          E a\<^sub>0 F "op \<preceq>" succs empty "op \<unlhd>" F' A succsi a\<^sub>0i Fi Lei emptyi key keyi copyi
        by (unfold_locales; simp add: GEN_ALGO_def)

      from pw_impl_hnr_F_reachable show ?thesis by simp
    qed

    sepref_decl_impl hnr_op_F_reachable .

  end -- \<open>Worklist Map 2\<close>

end -- \<open>End of Theory\<close>