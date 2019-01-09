theory Normalized_Zone_Semantics_Certification_Impl
  imports
    Normalized_Zone_Semantics_Impl_Refine
    Normalized_Zone_Semantics_Certification
    "Worklist_Algorithms/Unreachability_Certification"
    Deadlock_Impl
begin

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

locale Reachability_Problem_Impl_Precise =
  Reachability_Problem_Impl _ _ _ _ _ _ l\<^sub>0i _ l\<^sub>0
  + op_precise: E_Precise_Bisim l\<^sub>0 for l\<^sub>0 :: 's and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes op_impl
  assumes op_impl: "(uncurry4 op_impl, uncurry4 (\<lambda> l r. RETURN ooo f l r)) \<in> op_impl_assn"

definition
  "set_of_list xs = SPEC (\<lambda>S. set xs = S)"

(* XXX Move *)
lemma set_of_list_hnr:
  "(return o id, set_of_list) \<in> (list_assn A)\<^sup>d \<rightarrow>\<^sub>a lso_assn A"
  unfolding set_of_list_def lso_assn_def hr_comp_def br_def by sepref_to_hoare sep_auto

context Reachability_Problem_Impl_Precise
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
      RETURN (f l r g l' D # xs)
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

sepref_register f ::
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
  unfolding succs_precise_inner_def PR_CONST_def
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

lemmas amtx_copy_hnr = amtx_copy_hnr[unfolded op_mtx_copy_def, folded COPY_def[abs_def]]

lemmas [sepref_fr_rules] = copy_list_lso_assn_refine[OF amtx_copy_hnr]

lemma lso_op_set_is_empty_hnr[sepref_fr_rules]:
  "(return o (\<lambda>xs. xs = []), RETURN o op_set_is_empty) \<in> (lso_assn AA)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding lso_assn_def hr_comp_def br_def by sepref_to_hoare sep_auto

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
  unfolding HOL_list.fold_custom_empty
  by sepref

lemmas succs_precise_impl_refine = succs_precise'_impl.refine[FCOMP succs_precise'_correct]

lemma succs_precise_finite:
  "\<forall>l S. \<forall>(l', S')\<in>set (succs_precise l S). finite S \<longrightarrow> finite S'"
  unfolding succs_precise_def by auto

term op_precise.E_from_op

lemma E_from_op_states:
  "l' \<in> states" if "op_precise.E_from_op (l, M) (l', M')" "l \<in> states"
proof -
  from that(1) obtain g a r where "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    unfolding op_precise.E_from_op_def by auto
  then show ?thesis
    using \<open>l \<in> states\<close> by (rule trans_of_states)
qed

sepref_definition F_impl' is
  "RETURN o PR_CONST F_rel" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def F_rel_def by sepref

thm wf_dbm_def valid_dbm_def

print_statement wf_dbm_def

thm V_I

definition
  "wf_dbm' D \<equiv> (canonical' D \<or> check_diag n D) \<and>
     (list_all (\<lambda>i. D (i, i) \<le> 0) [0..<n+1]) \<and> list_all (\<lambda>i. D (0, i) \<le> 0) [0..<n+1]
    "

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

(* Merge with is_start_in_states *)
definition
  "is_in_states l = (trans_fun l \<noteq> [])"

definition
  "P \<equiv> \<lambda> (l, M). is_in_states l \<and> wf_dbm' M"

lemma is_state_in_states:
  "l \<in> states" if "is_in_states l"
proof -
  from that obtain g a r l' where "(g, a, r, l') \<in> set (trans_fun l)"
    by (cases "hd (trans_fun l)" rule: prod_cases4)
       (auto dest: hd_in_set simp: is_in_states_def)
  from trans_impl_trans_of[OF this] have "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
    (* wrong *)
    by simp
  then show ?thesis
    unfolding Simulation_Graphs_TA.state_set_def trans_of_def
    unfolding Normalized_Zone_Semantics_Impl_Refine.state_set_def
    by auto
qed

lemma P_correct:
  "l \<in> states \<and> wf_dbm M" if "P (l, M)"
  using that unfolding P_def by (auto intro: wf_dbm'_wf_dbm dest: is_state_in_states)

sepref_thm is_in_states_impl is
  "RETURN o PR_CONST is_in_states" :: "location_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def is_in_states_def by sepref

sepref_register is_in_states
sepref_register wf_dbm' :: "'b DBMEntry i_mtx \<Rightarrow> bool"

lemmas [sepref_fr_rules] =
  is_in_states_impl.refine_raw
  wf_dbm'_impl.refine_raw

sepref_definition P_impl is
  "RETURN o PR_CONST P" :: "state_assn'\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def P_def by sepref






sublocale
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
    and P = "\<lambda>(l, M). l \<in> states \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
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
    sorry
  subgoal (* M finite *)
    sorry
  subgoal (* succs finite *)
    by (rule succs_precise_finite)
  subgoal (* succs empty *)
    unfolding succs_precise_def by auto
  subgoal (* F mono *)
    using op.F_mono subsumes_simp_1 by fastforce
  subgoal (* L refine *)
    sorry
  subgoal (* M refine *)
    sorry
  subgoal (* key refine *)
    by sepref_to_hoare sep_auto
           apply (rule amtx_copy_hnr; fail)
  subgoal (* P refine *)
    by (rule P_impl.refine)
  subgoal (* F refine *)
    by (rule F_impl'.refine)
  subgoal (* succs refine *)
    using succs_precise_impl_refine unfolding b_assn_pure_conv .
       apply (rule dbm_subset_impl.refine; fail)
  subgoal (* init loc refine *)
    using init_impl by sepref_to_hoare sep_auto
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