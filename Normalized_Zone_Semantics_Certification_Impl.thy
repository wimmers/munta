theory Normalized_Zone_Semantics_Certification_Impl
  imports
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    Normalized_Zone_Semantics_Certification
    "Worklist_Algorithms/Unreachability_Certification"
    Deadlock_Impl
    "library/More_Methods"
begin

paragraph \<open>Misc\<close>

lemma Simulation_Composition:
  fixes A B C
  assumes
    "Simulation A B sim1" "Simulation B C sim2" "\<And>a c. (\<exists> b. sim1 a b \<and> sim2 b c) \<longleftrightarrow> sim a c"
  shows "Simulation A C sim"
proof -
  interpret A: Simulation A B sim1
    by (rule assms)
  interpret B: Simulation B C sim2
    by (rule assms)
  show ?thesis
    by standard (auto dest!: B.A_B_step A.A_B_step simp: assms(3)[symmetric])
qed

lemma fold_generalize_start:
  assumes "\<And>a. P a \<Longrightarrow> Q (fold g xs a)" "P a"
  shows "Q (fold g xs a)"
  using assms by auto

definition
  "set_of_list xs = SPEC (\<lambda>S. set xs = S)"

(* XXX Move *)
lemma set_of_list_hnr:
  "(return o id, set_of_list) \<in> (list_assn A)\<^sup>d \<rightarrow>\<^sub>a lso_assn A"
  unfolding set_of_list_def lso_assn_def hr_comp_def br_def by sepref_to_hoare sep_auto

lemma set_of_list_alt_def:
  "set_of_list = RETURN o set"
  unfolding set_of_list_def by auto

lemmas set_of_list_hnr' = set_of_list_hnr[unfolded set_of_list_alt_def]


lemmas amtx_copy_hnr = amtx_copy_hnr[unfolded op_mtx_copy_def, folded COPY_def[abs_def]]

lemma lso_op_set_is_empty_hnr[sepref_fr_rules]:
  "(return o (\<lambda>xs. xs = []), RETURN o op_set_is_empty) \<in> (lso_assn AA)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding lso_assn_def hr_comp_def br_def by sepref_to_hoare sep_auto

context
  fixes n :: nat
begin

private definition
  "dbm_tab M \<equiv> \<lambda> (i, j). if i \<le> n \<and> j \<le> n then M ! (n * i + j) else 0"

private lemma
  shows mtx_nonzero_dbm_tab_1: "(a, b) \<in> mtx_nonzero (dbm_tab M) \<Longrightarrow> a < Suc n"
    and mtx_nonzero_dbm_tab_2: "(a, b) \<in> mtx_nonzero (dbm_tab M) \<Longrightarrow> b < Suc n"
  unfolding mtx_nonzero_def dbm_tab_def by (auto split: if_split_asm)

definition
  "list_to_dbm M = op_amtx_new (Suc n) (Suc n) (dbm_tab M)"

lemma [sepref_fr_rules]:
  "(return o dbm_tab, RETURN o PR_CONST dbm_tab) \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
  by sepref_to_hoare sep_auto

lemmas [sepref_opt_simps] = dbm_tab_def

sepref_register dbm_tab

sepref_definition list_to_dbm_impl
  is "RETURN o PR_CONST list_to_dbm" :: "id_assn\<^sup>k \<rightarrow>\<^sub>a mtx_assn n"
  supply mtx_nonzero_dbm_tab_1[simp] mtx_nonzero_dbm_tab_2[simp]
  unfolding PR_CONST_def list_to_dbm_def by sepref

end


context Reachability_Problem_Impl
begin

sepref_definition E_precise_op'_impl is
  "uncurry4 (\<lambda> l r. RETURN ooo E_precise_op' l r)" :: "op_impl_assn"
  unfolding
    E_precise_op'_def FW''_def[symmetric] reset'_upd_def inv_of_A_def[symmetric] PR_CONST_def
    filter_diag_def
  by sepref

end


locale Reachability_Problem_Impl_Precise =
  Reachability_Problem_Impl _ _ _ _ _ _ l\<^sub>0i _ l\<^sub>0
  + op_precise: E_Precise_Bisim l\<^sub>0 for l\<^sub>0 :: 's and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes op_impl and states_mem_impl
  assumes op_impl: "(uncurry4 op_impl, uncurry4 (\<lambda> l r. RETURN ooo PR_CONST f l r)) \<in> op_impl_assn"
      and states_mem_impl: "(states_mem_impl, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"
begin

lemma E_precise_E_op:
  "E_precise = (\<lambda>(l, M) (l', M'''). \<exists>g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_precise_op l r g l' M)"
  unfolding E_precise_op_def E_precise_def by (intro ext) (auto elim!: step_impl.cases)

definition succs_precise where
  "succs_precise \<equiv> \<lambda>l S.
    if S = {} then [] else rev [(l', (\<lambda>D. f l r g l' D) ` S). (g,a,r,l') \<leftarrow> trans_fun l]"

definition succs_precise_inner where
  "succs_precise_inner l r g l' S \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    p \<leftarrow> nfoldli xs (\<lambda>_. True) (\<lambda>D xs.
      RETURN (PR_CONST f l r g l' D # xs)
    ) [];
    S' \<leftarrow> SPEC (\<lambda>S. set p = S);
    RETURN S'
}
"

definition succs_precise' where
  "succs_precise' \<equiv> \<lambda>l S. if S = {} then RETURN [] else do {
    nfoldli (trans_fun l) (\<lambda> _. True) (\<lambda> (g,a,r,l') xxs.
      do {
        S' \<leftarrow> PR_CONST succs_precise_inner l r g l' (COPY S);
        RETURN ((l', S') # xxs)
      }
    ) []
  }"

lemma succs_precise_inner_rule:
  "succs_precise_inner l r g l' S \<le> RETURN ((\<lambda>D. f l r g l' D) ` S)"
  unfolding succs_precise_inner_def
  by (refine_vcg nfoldli_rule[where I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev (map (f l r g l') l1)"]) auto

lemma succs_precise'_refine:
  "succs_precise' l S \<le> RETURN (succs_precise l S)"
  unfolding succs_precise_def succs_precise'_def
  unfolding rev_map_fold fold_eq_nfoldli PR_CONST_def
  apply (cases "S = {}")
   apply (simp; fail)
  apply (simp only: if_False fold_eq_nfoldli)
  apply (refine_vcg nfoldli_mono)
  apply (rule order.trans)
   apply (rule succs_precise_inner_rule)
  apply auto
  done

lemma succs_precise'_correct:
  "(uncurry succs_precise', uncurry (RETURN oo PR_CONST succs_precise)) \<in> Id \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using succs_precise'_refine by (clarsimp simp: pw_le_iff pw_nres_rel_iff)

sepref_register "PR_CONST f" ::
  "'s \<Rightarrow> nat list \<Rightarrow> (nat, int) acconstraint list \<Rightarrow> 's \<Rightarrow> int DBMEntry i_mtx \<Rightarrow> int DBMEntry i_mtx"

lemma aux:
  "b ::\<^sub>i TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) set) \<Longrightarrow>
       ID b b TYPE(int DBMEntry i_mtx set)"
  unfolding ID_def by simp

lemma aux':
  "(b ::\<^sub>i TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) set)) = (b ::\<^sub>i TYPE(int DBMEntry i_mtx set))"
  by simp

lemma aux'':
  "(b ::\<^sub>i TYPE((nat \<times> nat \<Rightarrow> int DBMEntry) )) = (b ::\<^sub>i TYPE(int DBMEntry i_mtx))"
  by simp

lemma aux3:
  "ID D x'a TYPE(nat \<times> nat \<Rightarrow> int DBMEntry) = ID D x'a TYPE(int DBMEntry i_mtx)"
  by simp

lemmas [sepref_fr_rules] =
  set_of_list_hnr Leadsto_Impl.lso_id_hnr
  op_impl

sepref_definition succs_precise_inner_impl is
  "uncurry4 (PR_CONST succs_precise_inner)"
  :: "location_assn\<^sup>k *\<^sub>a (list_assn (clock_assn n))\<^sup>k *\<^sub>a
      (list_assn (acconstraint_assn (clock_assn n) int_assn))\<^sup>k *\<^sub>a
      location_assn\<^sup>k *\<^sub>a (lso_assn (mtx_assn n))\<^sup>d
  \<rightarrow>\<^sub>a lso_assn (mtx_assn n)"
  unfolding PR_CONST_def
  unfolding succs_precise_inner_def
    list_of_set_def[symmetric] set_of_list_def[symmetric]
  apply (rewrite "HOL_list.fold_custom_empty")
  apply sepref_dbg_keep
     apply sepref_dbg_id_keep
  unfolding aux3
         apply sepref_dbg_id_step+
     apply sepref_dbg_monadify
     apply sepref_dbg_opt_init
      apply sepref_dbg_trans_keep
     apply sepref_dbg_opt
    apply sepref_dbg_cons_solve
   apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

sepref_register succs_precise_inner

lemmas [sepref_fr_rules] = succs_precise_inner_impl.refine

lemmas [sepref_fr_rules] = copy_list_lso_assn_refine[OF amtx_copy_hnr]

(* The d can also be a k *)
sepref_definition succs_precise'_impl is
  "uncurry succs_precise'"
  :: "location_assn\<^sup>k *\<^sub>a (lso_assn (mtx_assn n))\<^sup>d
      \<rightarrow>\<^sub>a list_assn (prod_assn location_assn (lso_assn (mtx_assn n)))"
  unfolding PR_CONST_def
  unfolding
    comp_def succs_precise'_def
    FW''_def[symmetric] rev_map_fold inv_of_A_def[symmetric]
    list_of_set_def[symmetric] set_of_list_def[symmetric]
  unfolding HOL_list.fold_custom_empty by sepref

lemmas succs_precise_impl_refine = succs_precise'_impl.refine[FCOMP succs_precise'_correct]

lemma succs_precise_finite:
  "\<forall>l S. \<forall>(l', S')\<in>set (succs_precise l S). finite S \<longrightarrow> finite S'"
  unfolding succs_precise_def by auto

sepref_definition F_impl' is
  "RETURN o PR_CONST F_rel" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def F_rel_def by sepref

definition
  "wf_dbm' D \<equiv> (canonical' D \<or> check_diag n D) \<and>
     (list_all (\<lambda>i. D (i, i) \<le> 0) [0..<n+1]) \<and> list_all (\<lambda>i. D (0, i) \<le> 0) [0..<n+1]"

theorem wf_dbm'_wf_dbm:
  fixes D :: "nat \<times> nat \<Rightarrow> int DBMEntry"
  assumes "wf_dbm' D"
  shows "wf_dbm D"
  using assms
  unfolding wf_dbm'_def wf_dbm_def valid_dbm_def list_all_iff canonical'_conv_M_iff
  unfolding valid_dbm.simps
  apply (elim conjE)
  apply (rule conjI)
   apply blast
  apply (rule conjI)
  subgoal
    by (intro impI diag_conv_M) auto
  apply (inst_existentials "curry (conv_M D)")
    apply (rule HOL.refl)
   apply (rule V_I)
  subgoal
    apply (auto del: disjE)
    subgoal for i
      apply (subgoal_tac "D (0, i) \<le> Le 0")
       apply (auto dest: conv_dbm_entry_mono simp: neutral del: disjE)
      apply (cases "i = n")
       apply auto
      done
    done
  apply (rule dbm_int_conv)
  done

lemma canonical'_compute:
  "canonical' M =
  list_all (\<lambda>i.
    list_all (\<lambda>j.
      list_all (\<lambda>k.
        M (i, k) \<le> M (i, j) + M (j, k)
  )[0..<n+1]) [0..<n+1]) [0..<n+1]
  "
  unfolding list_all_iff by auto force

sepref_definition canonical'_impl is
  "RETURN o PR_CONST canonical'" :: "(mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding canonical'_compute list_all_foldli PR_CONST_def by sepref

sepref_thm wf_dbm'_impl is
  "RETURN o PR_CONST wf_dbm'" :: "(mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding wf_dbm'_def canonical'_compute list_all_foldli PR_CONST_def by sepref

definition
  "states_mem l \<equiv> l \<in> states'"

definition
  "P \<equiv> \<lambda> (l, M). PR_CONST states_mem l \<and> wf_dbm' M"

lemma P_correct:
  "l \<in> states' \<and> wf_dbm M" if "P (l, M)"
  using that unfolding P_def states_mem_def by (auto intro: wf_dbm'_wf_dbm)

(* lemma [sepref_import_param]:
  "(states_mem, states_mem) \<in> Id \<rightarrow> Id"
  by simp *)

lemmas [sepref_import_param] = states_mem_impl[folded states_mem_def]

sepref_register states_mem

(* sepref_thm is_in_states_impl is
  "RETURN o PR_CONST states_mem" :: "(pure loc_rel)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def by sepref *)

sepref_register wf_dbm' :: "'c DBMEntry i_mtx \<Rightarrow> bool"

lemmas [sepref_fr_rules] =
  (* is_in_states_impl.refine_raw *)
  wf_dbm'_impl.refine_raw

sepref_definition P_impl is
  "RETURN o PR_CONST P" :: "(prod_assn (pure loc_rel) (mtx_assn n))\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def P_def by sepref

(* XXX Better proof technique? *)
lemma P_impl_refine:
  "(P_impl, (RETURN \<circ>\<circ> PR_CONST) P) \<in> (location_assn \<times>\<^sub>a mtx_assn n)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_to_hoare
  apply sep_auto
  subgoal for l M l' M'
    using P_impl.refine[to_hnr, unfolded hn_refine_def hn_ctxt_def, rule_format, of "(l, M)"]
    by (sep_auto simp: pure_def)
  done

lemma E_from_op_states:
  "l' \<in> states'" if "op_precise.E_from_op (l, M) (l', M')" "l \<in> states'"
  using that unfolding op_precise.E_from_op_def by auto

context
  fixes L_list :: "'si list" and P_loc and M_list :: "('si \<times> int DBMEntry list list) list"
  assumes state_impl_abstract: "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
  assumes P_loc: "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      (* and dbm_len: "list_all (\<lambda> (l, M). length M = n * n) M_list" *)
begin

definition
  "L \<equiv> map (\<lambda>li. SOME l. (li, l) \<in> loc_rel) L_list"

lemma mem_states'I:
  "l \<in> states'" if "states_mem_impl li" "(li, l) \<in> loc_rel" for l li
  using states_mem_impl that by (auto dest: fun_relD)

lemma L_list_rel:
  "(L_list, L) \<in> \<langle>location_rel\<rangle>list_rel"
  unfolding list_rel_def L_def
  using P_loc
  apply (clarsimp simp: list.pred_rel list.rel_map)
  apply (elim list_all2_mono)
  apply (clarsimp simp: eq_onp_def)
  apply (meson someI_ex state_impl_abstract)
  apply (erule mem_states'I, meson someI_ex state_impl_abstract)
  done

lemma L_list_hnr:
  "(uncurry0 (return L_list), uncurry0 (RETURN (PR_CONST (set L))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a lso_assn location_assn"
proof -
  have "(\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) = pure location_rel"
    unfolding pure_def by auto
  then have "list_assn (\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) = pure (\<langle>location_rel\<rangle>list_rel)"
    by (simp add: fcomp_norm_unfold)
  then have "emp \<Longrightarrow>\<^sub>A list_assn (\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) L L_list * true"
    by (sep_auto simp: pure_def intro: L_list_rel)
  then show ?thesis
    by sepref_to_hoare (sep_auto simp: lso_assn_def hr_comp_def br_def)
qed

definition
  "M_list' \<equiv> map (\<lambda>(li, xs). (SOME l. (li, l) \<in> loc_rel, xs)) M_list"

definition
  "M = fold (\<lambda>p M.
    let s = fst p; xs = snd p; xs = rev (map (list_to_dbm n) xs); S = set xs in fun_upd M s (Some S)
  ) (PR_CONST M_list') op_map_empty"

lemma M_finite:
  "\<forall>S\<in>ran M. finite S"
  unfolding M_def
  apply (rule fold_generalize_start[where P = "\<lambda>M. \<forall>S\<in>ran M. finite S"])
  subgoal for a
    unfolding M_list'_def
    apply (induction M_list arbitrary: a)
    apply (simp; fail)
    apply (simp, rprem, auto dest: ran_upd_cases)
    done
  apply (simp; fail)
  done

lemma P_loc':
  "list_all (\<lambda>(l, M). P_loc l \<and> states_mem_impl l) M_list"
  using P_loc \<open>_ \<subseteq> set L_list\<close> unfolding list_all_iff by auto

lemma M_list_rel:
  "(M_list, M_list') \<in> \<langle>location_rel \<times>\<^sub>r Id\<rangle>list_rel"
  unfolding list_rel_def M_list'_def
  using P_loc'
  apply (clarsimp simp: list.pred_rel list.rel_map)
  apply (elim list_all2_mono)
  apply (clarsimp simp: eq_onp_def)
  apply (meson someI_ex state_impl_abstract)
  apply (erule mem_states'I, meson someI_ex state_impl_abstract)
  done

lemma M_list_hnr[sepref_fr_rules]:
  "(uncurry0 (return M_list), uncurry0 (RETURN (PR_CONST M_list')))
    \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (location_assn \<times>\<^sub>a list_assn id_assn)"
proof -
  let ?R = "(\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) \<times>\<^sub>a list_assn (\<lambda>a c. \<up> (c = a))"
  have *: "list_assn (\<lambda>a c. \<up> (c = a)) = pure (\<langle>Id\<rangle>list_rel)"
    unfolding fcomp_norm_unfold by (simp add: pure_def)
  have "(\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) \<times>\<^sub>a list_assn (\<lambda>a c. \<up> (c = a))
    = pure (location_rel \<times>\<^sub>r Id)"
    unfolding * pure_def prod_assn_def by (intro ext) auto
  then have **: "list_assn ?R = pure (\<langle>location_rel \<times>\<^sub>r Id\<rangle>list_rel)"
    apply (simp add: fcomp_norm_unfold)
    apply (rule HOL.arg_cong[where f = list_assn])
    apply assumption
    done
  have "emp \<Longrightarrow>\<^sub>A list_assn ?R M_list' M_list * true"
    using M_list_rel unfolding ** by (sep_auto simp: pure_def)
  then show ?thesis
    by sepref_to_hoare (sep_auto simp: lso_assn_def hr_comp_def br_def)
qed

sepref_register "PR_CONST M_list'"

sepref_register "list_to_dbm n"

lemmas [sepref_fr_rules] = list_to_dbm_impl.refine

sepref_register set

lemmas [sepref_fr_rules] = set_of_list_hnr'

sepref_definition M_table is
  "uncurry0 (RETURN M)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' location_assn (lso_assn (mtx_assn n))"
  unfolding M_def set_of_list_def[symmetric] rev_map_fold
    HOL_list.fold_custom_empty hm.op_hms_empty_def[symmetric]
  by sepref

interpretation
  Reachability_Impl
  where A = "mtx_assn n"
    and F = F_rel
    and l\<^sub>0i = "return l\<^sub>0i"
    and s\<^sub>0 = init_dbm
    and s\<^sub>0i = init_dbm_impl
    and succs = succs_precise
    and succsi = succs_precise'_impl
    and less = "\<lambda> x y. dbm_subset n x y \<and> \<not> dbm_subset n y x"
    and less_eq = "dbm_subset n"
    and Lei = "dbm_subset_impl n"
    and E = op_precise.E_from_op
    and Fi = F_impl'
    and K = location_assn
    and keyi = "return o fst"
    and copyi = amtx_copy
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
    and L = "set L"
    and M = M
    and M_table = M_table
  apply standard
                      apply (rule HOL.refl; fail)
                      apply (rule dbm_subset_refl; fail)
                      apply (rule dbm_subset_trans; assumption)
    (* E_precise mono *)
  subgoal
    by (auto dest: op_precise.E_from_op_mono')
  subgoal (* E_precise invariant *)
    by (frule op_precise.E_from_op_wf_state[rotated])
       (auto dest: E_from_op_states simp: wf_state_def)
  subgoal (* P correct *)
    by (auto dest: P_correct)
  subgoal (* succs correct *)
    unfolding succs_precise_def op_precise.E_from_op_def
    apply (auto dest!: trans_impl_trans_of)
     apply (auto dest!: trans_of_trans_impl)
    apply force
    done
  subgoal (* L finite *)
    ..
  subgoal (* M finite *)
    by (rule M_finite)
  subgoal (* succs finite *)
    by (rule succs_precise_finite)
  subgoal (* succs empty *)
    unfolding succs_precise_def by auto
  subgoal (* F mono *)
    using op.F_mono subsumes_simp_1 by fastforce
  subgoal (* L refine *)
    by (rule L_list_hnr)
  subgoal (* M refine *)
    unfolding PR_CONST_def by (rule M_table.refine)
  subgoal (* key refine *)
    by sepref_to_hoare sep_auto
           apply (rule amtx_copy_hnr; fail)
  subgoal (* P refine *)
    by (rule P_impl_refine)
  subgoal (* F refine *)
    by (rule F_impl'.refine)
  subgoal (* succs refine *)
    using succs_precise_impl_refine unfolding b_assn_pure_conv .
       apply (rule dbm_subset_impl.refine; fail)
  subgoal (* init loc refine *)
    using init_impl states'_states by sepref_to_hoare sep_auto
     apply (unfold PR_CONST_def, rule init_dbm_impl.refine; fail)
    apply (rule location_assn_constraints; fail)+
  done

lemmas step_z_dbm_complete = step_z_dbm_complete[OF global_clock_numbering']

interpretation A:
  Simulation
  "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  "\<lambda> (l, Z) (l', Z'). \<exists> a. conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>"
  "\<lambda> (l, u) (l', Z). l' = l \<and> u \<in> Z"
  by standard (auto dest: step_z_complete')

interpretation B:
  Simulation
  "\<lambda> (l, Z) (l', Z'). \<exists> a. conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>"
  "\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D'"
  "\<lambda> (l, Z) (l', M). l' = l \<and> Z = [M]\<^bsub>v,n\<^esub>"
  by standard (force simp: step_z'_def step_z_dbm'_def elim!: step_z_dbm_DBM)

interpretation
  Simulation
  "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  "\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D'"
  "\<lambda> (l, u) (l', M). l' = l \<and> u \<in> [M]\<^bsub>v,n\<^esub>"
  by (rule Simulation_Composition, rule A.Simulation_axioms, rule B.Simulation_axioms) auto

lemma op_precise_unreachable_correct:
  assumes "\<nexists>s'. op_precise.E_from_op\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) s' \<and> F_rel s'"
  shows "\<nexists>u l' u'. (\<forall>c \<le> n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'"
proof -
  interpret Bisimulation_Invariant
    "\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D'"
    op_precise.E_from_op
    "\<lambda>(l, M) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
    "\<lambda>(l, y). valid_dbm y"
    "wf_state"
    by (rule op_precise.step_z_dbm'_E_from_op_bisim)
  have 1: "reaches (l\<^sub>0, u) (l', u')" if "conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" for u u' l'
    by (simp add: steps'_iff that)
  have 2: "u \<in> dbm.zone_of (curry init_dbm)" if "\<forall>c \<le> n. u c = 0" for u :: "_ \<Rightarrow> real"
    by (simp add: init_dbm_zone that)
  let ?E = "(\<lambda> (l, D) (l', D'). \<exists> a. step_z_dbm' (conv_A A) l D v n a l' D')"
  from assms have "\<nexists>l' M'. ?E\<^sup>*\<^sup>* (l\<^sub>0, curry (conv_M init_dbm)) (l', M') \<and> F l' \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
    apply (clarsimp simp: F_rel_def)
    apply (drule bisim.A_B_reaches[where b = "(l\<^sub>0, init_dbm)"])
    subgoal
      using valid_init_dbm unfolding equiv'_def
      by (auto simp: wf_state_def)
    unfolding equiv'_def using canonical_check_diag_empty_iff by blast
  then show ?thesis
    using simulation_reaches by (force dest!: 1 2 dest: dbm.check_diag_empty)
qed

lemma op_precise_unreachable_correct':
  "(uncurry0 (SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>s'. op_precise.E_from_op\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) s' \<and> F_rel s'))),
    uncurry0 (SPEC (\<lambda>r. r \<longrightarrow> (\<nexists>u l' u'. (\<forall>c \<le> n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'))))
  \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using op_precise_unreachable_correct by (clarsimp simp: pw_le_iff pw_nres_rel_iff)

lemmas certify_unreachable_impl_hnr =
  certify_unreachable_impl.refine[OF Reachability_Impl_axioms, FCOMP op_precise_unreachable_correct']

end

end

end