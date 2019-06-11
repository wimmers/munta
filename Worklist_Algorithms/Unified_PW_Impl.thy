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

  definition trace where
    "trace \<equiv> \<lambda>type a. RETURN ()"

  definition
    "explored_string = ''Explored''"

  definition
    "final_string = ''Final''"

  definition
    "added_string = ''Add''"

  definition
    "subsumed_string = ''Subsumed''"

  definition
    "empty_string = ''Empty''"

  lemma add_pw'_map2_alt_def:
    "add_pw'_map2 passed wait a = do {
     trace explored_string a;
     nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
      (\<lambda>a (passed, wait, _).
        do {
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
      (passed,wait,False)
    }"
    unfolding add_pw'_map2_def id_def op_map_extract_def trace_def
    supply [simp del] = map_upd_eq_restrict
    apply simp
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    apply (rule ext)+
    by (auto 4 3 simp: Let_def split: option.split)

    lemma add_pw'_map2_full_trace_def:
    "add_pw'_map2 passed wait a = do {
     trace explored_string a;
     nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
      (\<lambda>a (passed, wait, _).
        do {
          if empty a then
              do {trace empty_string a; RETURN (passed, wait, False)}
          else if F' a then do {trace final_string a; RETURN (passed, wait, True)}
          else
            let
              k = key a;
              (v, passed) = op_map_extract k passed
            in
              case v of
                None \<Rightarrow> do {trace added_string a; RETURN (passed(k \<mapsto> {COPY a}), a # wait, False)} |
                Some passed' \<Rightarrow>
                  if \<exists> x \<in> passed'. a \<unlhd> x then
                    do {trace subsumed_string a; RETURN (passed(k \<mapsto> passed'), wait, False)}
                  else do {
                      trace added_string a;
                      RETURN (passed(k \<mapsto> (insert (COPY a) passed')), a # wait, False)
                    }
        }
      )
      (passed,wait,False)
    }"
      unfolding add_pw'_map2_alt_def
      unfolding trace_def
      apply (simp add:)
      apply (fo_rule fun_cong)
      apply (fo_rule arg_cong)
      apply (rule ext)+
      apply (auto simp add: Let_def split: option.split)
      done

  end

  locale Worklist_Map2_Impl =
     Worklist4_Impl + Worklist_Map2_Impl_Defs + Worklist_Map2 +
    fixes K
    assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST key) \<in> A\<^sup>k \<rightarrow>\<^sub>a K"
    assumes [sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
    assumes [sepref_fr_rules]: "(uncurry tracei,uncurry trace) \<in> id_assn\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a id_assn"
    assumes pure_K: "is_pure K"
    assumes left_unique_K: "IS_LEFT_UNIQUE (the_pure K)"
    assumes right_unique_K: "IS_RIGHT_UNIQUE (the_pure K)"
  begin
    sepref_register
      "PR_CONST a\<^sub>0" "PR_CONST F'" "PR_CONST (\<unlhd>)" "PR_CONST succs" "PR_CONST empty" "PR_CONST key"
      "PR_CONST F" trace

    lemma [def_pat_rules]:
      "a\<^sub>0 \<equiv> UNPROTECT a\<^sub>0" "F' \<equiv> UNPROTECT F'" "(\<unlhd>) \<equiv> UNPROTECT (\<unlhd>)" "succs \<equiv> UNPROTECT succs"
      "empty \<equiv> UNPROTECT empty" "keyi \<equiv> UNPROTECT keyi" "F \<equiv> UNPROTECT F" "key \<equiv> UNPROTECT key"
      by simp_all

    lemma take_from_list_alt_def:
      "take_from_list xs = do {_ \<leftarrow> ASSERT (xs \<noteq> []); RETURN (hd_tl xs)}"
      unfolding take_from_list_def by (auto simp: pw_eq_iff refine_pw_simps)

    lemma [safe_constraint_rules]: "CN_FALSE is_pure A \<Longrightarrow> is_pure A" by simp

    lemmas [sepref_fr_rules] = hd_tl_hnr

    lemmas [safe_constraint_rules] = pure_K left_unique_K right_unique_K

    lemma [sepref_import_param]:
      "(explored_string, explored_string) \<in> Id"
      "(subsumed_string, subsumed_string) \<in> Id"
      "(added_string, added_string) \<in> Id"
      "(final_string, final_string) \<in> Id"
      "(empty_string, empty_string) \<in> Id"
      unfolding
        explored_string_def subsumed_string_def added_string_def final_string_def empty_string_def
      by simp+
    
    lemmas [sepref_opt_simps] =
      explored_string_def
      subsumed_string_def
      added_string_def
      final_string_def
      empty_string_def

    sepref_thm pw_algo_map2_impl is
      "uncurry0 (do {(r, p) \<leftarrow> pw_algo_map2; RETURN r})" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding pw_algo_map2_def add_pw'_map2_full_trace_def PR_CONST_def TRACE'_def[symmetric]
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

  end \<comment> \<open>Worklist Map2 Impl\<close>

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
            by (auto simp: pw_le_iff refine_pw_simps)
        qed
        done
      done

  lemma pw_impl_hnr_F_reachable:
    "(uncurry0 (pw_impl keyi copyi tracei Lei a\<^sub>0i Fi succsi emptyi), uncurry0 (RETURN F_reachable))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    using
      pw_impl.refine[
        OF Worklist_Map2_Impl_axioms,
        FCOMP pw_algo_map2_correct'[THEN Id_SPEC_refine, THEN nres_relI]
        ]
    by (simp add: RETURN_def)

  end

  locale Worklist_Map2_Hashable =
    Worklist_Map2_Impl_finite
  begin

    sepref_decl_op F_reachable :: "bool_rel" .
    lemma [def_pat_rules]: "F_reachable \<equiv> op_F_reachable" by simp


    lemma hnr_op_F_reachable:
      assumes "GEN_ALGO a\<^sub>0i (\<lambda>a\<^sub>0i. (uncurry0 a\<^sub>0i, uncurry0 (RETURN a\<^sub>0)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a A)"
      assumes "GEN_ALGO Fi (\<lambda>Fi. (Fi,RETURN o F') \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO Lei (\<lambda>Lei. (uncurry Lei,uncurry (RETURN oo (\<unlhd>))) \<in> A\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes "GEN_ALGO succsi (\<lambda>succsi. (succsi,RETURN o succs) \<in> A\<^sup>k \<rightarrow>\<^sub>a list_assn A)"
      assumes "GEN_ALGO emptyi (\<lambda>Fi. (Fi,RETURN o empty) \<in> A\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
      assumes [sepref_fr_rules]: "(keyi,RETURN o PR_CONST key) \<in> A\<^sup>k \<rightarrow>\<^sub>a K"
      assumes [sepref_fr_rules]: "(copyi, RETURN o COPY) \<in> A\<^sup>k \<rightarrow>\<^sub>a A"
      shows
        "(uncurry0 (pw_impl keyi copyi tracei Lei a\<^sub>0i Fi succsi emptyi),
          uncurry0 (RETURN (PR_CONST op_F_reachable)))
        \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    proof -
      from assms interpret
        Worklist_Map2_Impl
          E a\<^sub>0 F "(\<preceq>)" succs empty "(\<unlhd>)" F' A succsi a\<^sub>0i Fi Lei emptyi key keyi copyi
        by (unfold_locales; simp add: GEN_ALGO_def)

      from pw_impl_hnr_F_reachable show ?thesis by simp
    qed

    sepref_decl_impl hnr_op_F_reachable .

  end \<comment> \<open>Worklist Map 2\<close>

end \<comment> \<open>End of Theory\<close>