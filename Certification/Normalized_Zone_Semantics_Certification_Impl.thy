theory Normalized_Zone_Semantics_Certification_Impl
  imports
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    Normalized_Zone_Semantics_Certification
    Collections.Refine_Dflt_ICF
    Certification.Unreachability_Certification2
    Certification.Unreachability_Certification
    "HOL-Library.IArray"
    Deadlock.Deadlock_Impl
    TA_Library.More_Methods
    "HOL-Library.Rewrite"
    Unreachability_TA_Misc
begin

context TA_Impl
begin

interpretation DBM_Impl n .

sepref_definition E_precise_op'_impl is
  "uncurry4 (\<lambda> l r. RETURN ooo E_precise_op' l r)" :: "op_impl_assn"
  unfolding
    E_precise_op'_def FW''_def[symmetric] reset'_upd_def inv_of_A_def[symmetric] PR_CONST_def
    filter_diag_def
  by sepref

end

(*
locale Reachability_Problem_Impl_Precise =
  Reachability_Problem_Impl _ _ _ _ _ _ l\<^sub>0i _ l\<^sub>0
  + op_precise: E_Precise_Bisim l\<^sub>0 for l\<^sub>0 :: 's and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes op_impl and states_mem_impl
  assumes op_impl: "(uncurry4 op_impl, uncurry4 (\<lambda> l r. RETURN ooo PR_CONST f l r)) \<in> op_impl_assn"
      and states_mem_impl: "(states_mem_impl, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"
begin
*)

locale TA_Impl_Ext =
  TA_Impl +
  fixes states_mem_impl
  assumes states_mem_impl: "(states_mem_impl, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"

locale TA_Impl_Precise =
  TA_Impl _ _ _ l\<^sub>0 _ _ _ _ _ l\<^sub>0i
  + op_precise: E_Precise_Bisim _ l\<^sub>0 for l\<^sub>0 :: 's and l\<^sub>0i :: "'si:: {hashable,heap}" +
  fixes op_impl and states_mem_impl
  assumes op_impl: "(uncurry4 op_impl, uncurry4 (\<lambda> l r. RETURN ooo PR_CONST f l r)) \<in> op_impl_assn"
      and states_mem_impl: "(states_mem_impl, (\<lambda>l. l \<in> states')) \<in> loc_rel \<rightarrow> bool_rel"
begin

sublocale TA_Impl_Ext
  by (standard) (rule states_mem_impl)

end

locale Reachability_Problem_Impl_Precise =
  TA_Impl_Precise _ show_state A
  for show_state :: "'si:: {hashable,heap} \<Rightarrow> string" and A :: "('a, nat, int, 's) ta"+
  fixes F :: "'s \<times> (nat \<times> nat \<Rightarrow> int DBMEntry) \<Rightarrow> bool" and F' and F1 and F_impl
  assumes F_mono: "\<And> a b.
    (\<lambda>(l, M). l \<in> states' \<and> wf_dbm M) a \<Longrightarrow> F a \<Longrightarrow>
    (\<lambda>(l, s) (l', s'). l' = l \<and> dbm_subset n s s') a b \<Longrightarrow> (\<lambda>(l, M). l \<in> states' \<and> wf_dbm M) b
    \<Longrightarrow> F b"
      and F_F1: "\<And>l D Z. op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) (l, D)
          \<Longrightarrow> dbm.zone_of (curry (conv_M D)) = Z \<Longrightarrow> F (l, D) = F1 (l, Z)"
      and F'_F1: "\<And>l u Z. u \<in> Z \<Longrightarrow> F' (l, u) \<Longrightarrow> F1 (l, Z)"
      and F_impl: "(F_impl, RETURN o PR_CONST F) \<in> state_assn'\<^sup>d \<rightarrow>\<^sub>a bool_assn"


paragraph \<open>Successor Implementation\<close>
context TA_Impl_Precise
begin

lemma E_precise_E_op:
  "E_precise = (\<lambda>(l, M) (l', M'''). \<exists>g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> M''' = E_precise_op l r g l' M)"
  unfolding E_precise_op_def E_precise_def by (intro ext) (auto elim!: step_impl.cases)

definition succs_precise where
  "succs_precise \<equiv> \<lambda>l S.
    if S = {} then []
    else rev [
      (l', {D' | D' D. D \<in> S \<and> D' = f l r g l' D \<and> \<not> check_diag n D'}). (g,a,r,l') \<leftarrow> trans_fun l]"

definition succs_precise_inner where
 "succs_precise_inner l r g l' S \<equiv> do {
    xs \<leftarrow> SPEC (\<lambda>xs. set xs = S);
    p \<leftarrow> nfoldli xs (\<lambda>_. True) (\<lambda>D xs.
      do {let D' = PR_CONST f l r g l' D; if check_diag n D' then RETURN xs else RETURN (D' # xs)}
    ) [];
    S' \<leftarrow> SPEC (\<lambda>S. set p = S);
    RETURN S'
  }"

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
  "succs_precise_inner l r g l' S
  \<le> RETURN {D' | D' D. D \<in> S \<and> D' = f l r g l' D \<and> \<not> check_diag n D'}"
  unfolding succs_precise_inner_def
  by (refine_vcg nfoldli_rule[where
        I = "\<lambda>l1 l2 \<sigma>. \<sigma> = rev (filter (\<lambda>D'. \<not> check_diag n D') (map (f l r g l') l1))"
     ]) auto

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

interpretation DBM_Impl n .

sepref_definition succs_precise_inner_impl is
  "uncurry4 (PR_CONST succs_precise_inner)"
  :: "location_assn\<^sup>k *\<^sub>a (list_assn clock_assn)\<^sup>k *\<^sub>a
      (list_assn (acconstraint_assn clock_assn int_assn))\<^sup>k *\<^sub>a
      location_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>d
  \<rightarrow>\<^sub>a lso_assn mtx_assn"
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
  :: "location_assn\<^sup>k *\<^sub>a (lso_assn mtx_assn)\<^sup>d
      \<rightarrow>\<^sub>a list_assn (prod_assn location_assn (lso_assn mtx_assn))"
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

lemma E_from_op_states:
  "l' \<in> states'" if "op_precise.E_from_op (l, M) (l', M')" "l \<in> states'"
  using that unfolding op_precise.E_from_op_def by auto

end (* TA Impl Precise *)


context TA_Impl_Ext
begin

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

interpretation DBM_Impl n .

sepref_definition canonical'_impl is
  "RETURN o PR_CONST canonical'" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding canonical'_compute list_all_foldli PR_CONST_def by sepref

sepref_thm wf_dbm'_impl is
  "RETURN o PR_CONST wf_dbm'" :: "mtx_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
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

sepref_register wf_dbm' :: "'fresh DBMEntry i_mtx \<Rightarrow> bool"

lemmas [sepref_fr_rules] =
  (* is_in_states_impl.refine_raw *)
  wf_dbm'_impl.refine_raw

sepref_definition P_impl is
  "RETURN o PR_CONST P" :: "(prod_assn (pure loc_rel) mtx_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding PR_CONST_def P_def by sepref

(* XXX Better proof technique? *)
lemma P_impl_refine:
  "(P_impl, (RETURN \<circ>\<circ> PR_CONST) P) \<in> (location_assn \<times>\<^sub>a mtx_assn)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_to_hoare
  apply sep_auto
  subgoal for l M l' M'
    using P_impl.refine[to_hnr, unfolded hn_refine_def hn_ctxt_def, rule_format, of "(l, M)"]
    by (sep_auto simp: pure_def)
  done

lemmas [safe_constraint_rules] = location_assn_constraints

end (* TA Impl Ext *)


paragraph \<open>Deriving the Main Simulation Theorems\<close>
context Reachability_Problem_Impl_Precise
begin

lemmas step_z_dbm_complete = step_z_dbm_complete[OF global_clock_numbering']

interpretation A:
  Simulation
  "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  "\<lambda> (l, Z) (l', Z'). \<exists> a. conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  "\<lambda> (l, u) (l', Z). l' = l \<and> u \<in> Z"
  by standard (auto dest!: step_z_complete')

interpretation B:
  Simulation
  "\<lambda> (l, Z) (l', Z'). \<exists> a. conv_A A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  "\<lambda> (l, M) (l', M'). \<exists> a. conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
  "\<lambda> (l, Z) (l', M). l' = l \<and> Z = [M]\<^bsub>v,n\<^esub>"
  by standard (force simp: step_z'_def step_z_dbm'_def elim!: step_z_dbm_DBM)

interpretation
  Simulation
  "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  "\<lambda> (l, M) (l', M'). \<exists> a. conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
  "\<lambda> (l, u) (l', M). l' = l \<and> u \<in> [M]\<^bsub>v,n\<^esub>"
  by (rule Simulation_Composition, rule A.Simulation_axioms, rule B.Simulation_axioms) auto

lemma op_precise_buechi_run_correct:
  assumes
    "(\<nexists>xs.
    Graph_Defs.run op_precise.E_from_op_empty ((l\<^sub>0', init_dbm) ## xs)
    \<and> alw (ev (holds F)) ((l\<^sub>0', init_dbm) ## xs))"
  and F_F1: "\<And>l D Z. op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0', init_dbm) (l, D)
          \<Longrightarrow> dbm.zone_of (curry (conv_M D)) = Z \<Longrightarrow> F (l, D) = F1 (l, Z)"
  shows
    "\<nexists>u xs. (\<forall>c \<le> n. u c = 0)
    \<and> Graph_Defs.run (\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>) ((l\<^sub>0', u) ## xs)
    \<and> alw (ev (holds F')) ((l\<^sub>0', u) ## xs)"
proof -
  let ?E = "\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  define E where "E \<equiv> \<lambda>(l, M) (l', M'). \<exists>a. conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
  interpret Bisimulation_Invariant
    E
    op_precise.E_from_op_empty
    "\<lambda>(l, M) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
    "\<lambda>(l, y). valid_dbm y"
    "wf_state"
    unfolding E_def by (rule op_precise.step_z_dbm'_E_from_op_bisim_empty)
  have init: "u \<in> dbm.zone_of (curry init_dbm)" if "\<forall>c \<le> n. u c = 0" for u :: "_ \<Rightarrow> real"
    by (simp add: init_dbm_zone that)
  let ?F1 = "\<lambda>(l, M). F1 (l, [M]\<^bsub>v,n\<^esub>)"
  have "alw (ev (holds F)) ys"
    if "stream_all2 equiv' xs ys"
      "alw (ev (holds (\<lambda>(l, M). F1 (l, dbm.zone_of M)))) xs"
      "B.run ((l\<^sub>0', init_dbm) ## ys)"
    for xs ys
  proof -
    from that(3) have "pred_stream (B.reaches (l\<^sub>0', init_dbm)) ys"
      by (rule B.run_first_reaches)
    with that(1) have "stream_all2 (\<lambda>x y. equiv' x y \<and> B.reaches (l\<^sub>0', init_dbm) y) xs ys"
      by (rule stream_all2_pred_stream_combine) (rule conjI)
    with that(2) show ?thesis
      apply (rule alw_ev_lockstep)
      unfolding equiv'_def using F_F1 by blast
  qed
  with assms have "\<nexists>xs.
    Graph_Defs.run E ((l\<^sub>0', curry (conv_M init_dbm)) ## xs)
  \<and> alw (ev (holds ?F1)) ((l\<^sub>0', curry (conv_M init_dbm)) ## xs)"
    apply safe
    apply (drule bisim.A_B.simulation_run[where y = "(l\<^sub>0', init_dbm)"])
    using valid_init_dbm unfolding equiv'_def
    by (auto simp: wf_state_def dest: bisim.A_B.simulation_run[where y = "(l\<^sub>0', init_dbm)"])
  then show ?thesis
    unfolding E_def
    by (auto
        intro: F'_F1
        dest: alw_ev_lockstep[where R = ?F1]
        dest!: simulation_run[where y = "(l\<^sub>0', curry init_dbm)"] init
        )
qed

lemma op_precise_unreachable_correct:
  assumes "\<nexists>s'. op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) s' \<and> F s'"
  shows "\<nexists>u l' u'. (\<forall>c \<le> n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F' (l', u')"
proof -
  define E where "E \<equiv> \<lambda>(l, M) (l', M'). \<exists> a. conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
  interpret Bisimulation_Invariant
    E
    op_precise.E_from_op_empty
    "\<lambda>(l, M) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
    "\<lambda>(l, y). valid_dbm y"
    "wf_state"
    unfolding E_def by (rule op_precise.step_z_dbm'_E_from_op_bisim_empty)
  have 1: "reaches (l\<^sub>0, u) (l', u')" if "conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" for u u' l'
    by (simp add: steps'_iff that)
  have 2: "u \<in> dbm.zone_of (curry init_dbm)" if "\<forall>c \<le> n. u c = 0" for u :: "_ \<Rightarrow> real"
    by (simp add: init_dbm_zone that)
  from assms have
    "\<nexists>l' M'. E\<^sup>*\<^sup>* (l\<^sub>0, curry (conv_M init_dbm)) (l', M') \<and> F1 (l', [M']\<^bsub>v,n\<^esub>) \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
    apply (clarsimp simp: )
    apply (drule bisim.A_B_reaches[where b = "(l\<^sub>0, init_dbm)"])
    subgoal
      using valid_init_dbm unfolding equiv'_def
      by (auto simp: wf_state_def)
    unfolding equiv'_def using canonical_check_diag_empty_iff
    using F_F1 by blast
  then show ?thesis
    unfolding E_def by (fastforce dest: dbm.check_diag_empty F'_F1 dest!: simulation_reaches 1 2)
qed

lemma op_precise_unreachable_correct':
  "(uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
      (\<nexists>s'. op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) s' \<and> F s'))),
    uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
      (\<nexists>u l' u'. (\<forall>c \<le> n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F' (l', u')))))
  \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using op_precise_unreachable_correct by (clarsimp simp: pw_le_iff pw_nres_rel_iff)

(*
lemma op_precise_unreachable_correct:
  assumes "\<nexists>s'. op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) s' \<and> (\<lambda> (l, M). F l) s'"
  shows "\<nexists>u l' u'. (\<forall>c \<le> n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'"
proof -
  define E where "E \<equiv> \<lambda>(l, M) (l', M'). \<exists> a. conv_A A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l', M'\<rangle> \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
  interpret Bisimulation_Invariant
    E
    op_precise.E_from_op_empty
    "\<lambda>(l, M) (l', D). l' = l \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>"
    "\<lambda>(l, y). valid_dbm y"
    "wf_state"
    unfolding E_def by (rule op_precise.step_z_dbm'_E_from_op_bisim_empty)
  have 1: "reaches (l\<^sub>0, u) (l', u')" if "conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" for u u' l'
    by (simp add: steps'_iff that)
  have 2: "u \<in> dbm.zone_of (curry init_dbm)" if "\<forall>c \<le> n. u c = 0" for u :: "_ \<Rightarrow> real"
    by (simp add: init_dbm_zone that)
  from assms have "\<nexists>l' M'. E\<^sup>*\<^sup>* (l\<^sub>0, curry (conv_M init_dbm)) (l', M') \<and> F l' \<and> [M']\<^bsub>v,n\<^esub> \<noteq> {}"
    apply (clarsimp simp: F_rel_def)
    apply (drule bisim.A_B_reaches[where b = "(l\<^sub>0, init_dbm)"])
    subgoal
      using valid_init_dbm unfolding equiv'_def
      by (auto simp: wf_state_def)
    unfolding equiv'_def using canonical_check_diag_empty_iff by blast
  then show ?thesis
    unfolding E_def using simulation_reaches by (force dest!: 1 2 dest: dbm.check_diag_empty)
qed

lemma op_precise_unreachable_correct':
  "(uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
      (\<nexists>s'. op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) s' \<and> (\<lambda>(l, M). F l) s'))),
    uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
      (\<nexists>u l' u'. (\<forall>c \<le> n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'))))
  \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using op_precise_unreachable_correct by (clarsimp simp: pw_le_iff pw_nres_rel_iff)
*)

end




paragraph \<open>Refinement setup: \<open>list_to_dbm\<close>/\<open>set\<close>\<close>
context TA_Impl
begin

term placeholder

sepref_register "list_to_dbm n"

lemmas [sepref_fr_rules] = of_list_list_to_dbm[of n]

sepref_register set

lemmas [sepref_fr_rules] = set_of_list_hnr'


lemma IArray_list_to_dbm_rel[param]:
  "(IArray, list_to_dbm n)
  \<in> {(xs, ys). xs = ys \<and> length xs = Suc n * Suc n} \<rightarrow> {(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}"
  unfolding list_to_dbm_def op_amtx_new_def iarray_mtx_rel_def Unreachability_TA_Misc.dbm_tab_def
  by (auto simp: algebra_simps)

lemma IArray_list_to_dbm_rel':
  "(map IArray xs, list_to_dbm n ` set xs)
  \<in> \<langle>{(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}\<rangle>list_set_rel"
  if "list_all (\<lambda>xs. length xs = Suc n * Suc n) xs"
  using that by (rule map_set_rel) (rule IArray_list_to_dbm_rel)

end


paragraph \<open>Implementing Invariants as Tables\<close>
context Reachability_Problem_Impl_Precise
begin

text \<open>Note: These table implementations could be made independent from
\<open>Reachability_Problem_Impl_Precise\<close> by generalizing over \<^term>\<open>states_mem_impl\<close>/\<^term>\<open>loc_rel\<close> and
derived constants. See what we started for locale \<open>TA_Impl_Ext\<close>.
\<close>
context
  fixes L_list :: "'si list" and P_loc
  assumes state_impl_abstract: "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
  assumes P_loc: "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"
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





context
  fixes M_list :: "('si \<times> 'v list) list" and g :: "'v \<Rightarrow> 'v1" and h :: "'v \<Rightarrow> 'v2"
    and P :: "'v \<Rightarrow> bool" and R :: "('v2 \<times> 'v1) set"
begin

definition
  "M_list1 \<equiv> map (\<lambda>(li, xs). (SOME l. (li, l) \<in> loc_rel, xs)) M_list"

definition
  "M1 = fold (\<lambda>p M.
    let
      s = fst p; xs = snd p;
      xs = rev (map g xs);
      S = set xs in fun_upd M s (Some S)
  ) (PR_CONST M_list1) IICF_Map.op_map_empty"

definition
  "M1i = hashmap_of_list (map (\<lambda>(k, dbms). (k, map h dbms)) M_list)"

context
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      and M_P: "list_all (\<lambda>(l, xs). list_all P xs) M_list"
    assumes g_h_param: "(h, g) \<in> {(x, y). x = y \<and> P x} \<rightarrow> R"
begin

lemma M1_finite:
  "\<forall>S\<in>ran M1. finite S"
  unfolding M1_def
  apply (rule fold_generalize_start[where P = "\<lambda>M. \<forall>S\<in>ran M. finite S"])
  subgoal for a
    unfolding M_list1_def
    apply (induction M_list arbitrary: a)
     apply (simp; fail)
    apply (simp, rprem, auto dest: ran_upd_cases)
    done
  apply (simp; fail)
  done

lemma P_loc1:
  "list_all
    (\<lambda>(l, xs). P_loc l \<and> states_mem_impl l \<and> list_all P xs) M_list"
  using P_loc \<open>_ \<subseteq> set L_list\<close> M_P unfolding list_all_iff by auto

lemma M_list_rel1:
  "(M_list, M_list1) \<in> \<langle>location_rel \<times>\<^sub>r \<langle>br id P\<rangle>list_rel\<rangle>list_rel"
  unfolding list_rel_def M_list1_def
  using P_loc1
  apply (clarsimp simp: list.pred_rel list.rel_map br_def)
  apply (elim list_all2_mono)
  apply (clarsimp simp: eq_onp_def)
  apply (meson someI_ex state_impl_abstract)
   apply (erule mem_states'I, meson someI_ex state_impl_abstract)
  apply (elim list_all2_mono, clarsimp)
  done

lemma dom_M_eq1_aux:
  "dom (fold (\<lambda>p M.
    let s = fst p; xs = snd p;
    xs = rev (map g xs); S = set xs in fun_upd M s (Some S)
  ) xs m) = dom m \<union> fst ` set xs" for xs m
    by (induction xs arbitrary: m) auto

lemma dom_M_eq1:
  "dom M1 = fst ` set M_list1"
  unfolding dom_M_eq1_aux M1_def by simp

lemma L_dom_M_eqI1:
  assumes "fst ` set M_list = set L_list"
  shows "set L = dom M1"
proof -
  show ?thesis
    unfolding dom_M_eq1
  proof (safe; clarsimp?)
    fix l assume "l \<in> set L"
    with L_list_rel assms obtain l' where "l' \<in> fst ` set M_list" "(l', l) \<in> location_rel"
      by (fastforce simp: list_all2_append2 list_all2_Cons2 list_rel_def elim!: in_set_list_format)
    with M_list_rel1 obtain l1 where "l1 \<in> fst ` set M_list1" "(l', l1) \<in> location_rel"
      by (fastforce simp: list_all2_append1 list_all2_Cons1 list_rel_def elim!: in_set_list_format)
    with \<open>(l', l) \<in> location_rel\<close> show "l \<in> fst ` set M_list1"
      using loc_rel_right_unique by auto
  next
    fix l M assume "(l, M) \<in> set M_list1"
    with M_list_rel1 assms obtain l' where "l' \<in> set L_list" "(l', l) \<in> location_rel"
      by (fastforce simp: list_all2_append2 list_all2_Cons2 list_rel_def elim!: in_set_list_format)
    with L_list_rel obtain l1 where "l1 \<in> set L" "(l', l1) \<in> location_rel"
      by (fastforce simp: list_all2_append1 list_all2_Cons1 list_rel_def elim!: in_set_list_format)
    with \<open>(l', l) \<in> location_rel\<close> show "l \<in> set L"
      using loc_rel_right_unique by auto
  qed
qed

lemma map_of_M_list_M_rel1:
  "(map_of_list (map (\<lambda>(k, dbms). (k, map h dbms)) M_list), M1)
\<in> location_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_set_rel\<rangle>option_rel"
  unfolding M1_def M_list1_def
  unfolding map_of_list_def
  unfolding PR_CONST_def
proof goal_cases
  case 1
  let "(fold ?f ?xs Map.empty, fold ?g ?ys _) \<in> ?R" = ?case
  have *: "l' = (SOME l'. (l, l') \<in> loc_rel)"
    if "(l, l') \<in> loc_rel" "states_mem_impl l" "l' \<in> states'" for l l'
  proof -
    from that have "(l, SOME l'. (l, l') \<in> loc_rel) \<in> loc_rel"
      by (intro someI)
    moreover then have "(SOME l'. (l, l') \<in> loc_rel) \<in> states'"
      using that(2) by (elim mem_states'I)
    ultimately show ?thesis
      using that right_unique_location_rel unfolding single_valued_def by auto
  qed
  have "(fold ?f ?xs m, fold ?g ?ys m') \<in> ?R"
    if "(m, m') \<in> ?R" for m m'
    using that P_loc1
  proof (induction M_list arbitrary: m m')
    case Nil
    then show ?case
      by simp
  next
    case (Cons x M_list)
    obtain l M where "x = (l, M)"
      by force
    from Cons.IH \<open>list_all _ (x # M_list)\<close> show ?case
      apply (simp split:)
      apply rprems
      unfolding \<open>x = _\<close>
      apply simp
      apply (rule fun_relI)
      apply (clarsimp; safe)
      subgoal
        using g_h_param by (auto dest!: fun_relD intro!: map_set_rel)
      subgoal
        by (frule *) auto
      subgoal
        using left_unique_location_rel unfolding IS_LEFT_UNIQUE_def single_valued_def
        by (auto dest: someI_ex[OF state_impl_abstract])
      subgoal
        using Cons.prems(1)
        apply -
        apply (drule fun_relD)
        by simp
      done
  qed
  then show ?case
    by rprems auto
qed

lemma Mi_M1:
  "(\<lambda>k. Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k M1i, M1)
  \<in> location_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_set_rel\<rangle>option_rel"
(is "(?f, M1) \<in> ?R")
proof -
  let ?g = "map_of_list (map (\<lambda>(k, dbms). (k, map h dbms)) M_list)"
  have "(?f, ?g) \<in> Id \<rightarrow> \<langle>Id\<rangle>option_rel"
    unfolding M1i_def by (rule hashmap_of_list_lookup)
  moreover have "(?g, M1) \<in> ?R"
    by (rule map_of_M_list_M_rel1)
  ultimately show ?thesis
    by auto
qed

end (* Assumptions *)

end (* Defs *)



context
  fixes M_list :: "('si \<times> int DBMEntry list list) list"
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      and M_dbm_len: "list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = Suc n * Suc n) xs) M_list"
begin

lemmas M_assms = M_list_covered M_dbm_len IArray_list_to_dbm_rel

definition
  "M_list' \<equiv> M_list1 M_list"

definition
  "M = fold (\<lambda>p M.
    let s = fst p; xs = snd p; xs = rev (map (list_to_dbm n) xs); S = set xs in fun_upd M s (Some S)
  ) (PR_CONST M_list') IICF_Map.op_map_empty"

lemma M_alt_def:
  "M = M1 TYPE(int DBMEntry list) M_list (list_to_dbm n)"
  unfolding M_def M1_def M_list'_def ..

lemma M_finite:
  "\<forall>S\<in>ran M. finite S"
  unfolding M_alt_def by (rule M1_finite[OF M_assms])

lemmas M_list_rel = M_list_rel1[OF M_assms, folded M_list'_def]

lemma M_list_hnr[sepref_fr_rules]:
  "(uncurry0 (return M_list), uncurry0 (RETURN (PR_CONST M_list')))
    \<in> id_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (
        location_assn \<times>\<^sub>a list_assn (pure (b_rel Id (\<lambda>xs. length xs = Suc n * Suc n))))"
proof -
  let ?R1 = "\<langle>br id (\<lambda>xs. length xs = Suc n * Suc n)\<rangle>list_rel"
  let ?R2 = "\<lambda>a c. \<up> (a = c \<and> length c = Suc (n + (n + n * n)))"
  let ?R = "(\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states')) \<times>\<^sub>a list_assn ?R2"
  have "b_rel Id = br id"
    unfolding br_def b_rel_def by auto
  have *: "list_assn (\<lambda>a c. \<up> (a = c \<and> length c = Suc (n + (n + n * n)))) = pure ?R1"
    unfolding fcomp_norm_unfold by (simp add: pure_def br_def)
  have "?R = pure (location_rel \<times>\<^sub>r ?R1)"
    unfolding * pure_def prod_assn_def by (intro ext) auto
  then have **: "list_assn ?R = pure (\<langle>location_rel \<times>\<^sub>r ?R1\<rangle>list_rel)"
    unfolding fcomp_norm_unfold by simp (fo_rule HOL.arg_cong)
  have "emp \<Longrightarrow>\<^sub>A list_assn ?R M_list' M_list * true"
    using M_list_rel unfolding ** by (sep_auto simp: pure_def)
  then show ?thesis
    by sepref_to_hoare (sep_auto simp: lso_assn_def hr_comp_def br_def \<open>b_rel Id = br id\<close>)
qed

sepref_register "PR_CONST M_list'"

interpretation DBM_Impl n .

sepref_definition M_table is
  "uncurry0 (RETURN M)" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a hm.hms_assn' location_assn (lso_assn mtx_assn)"
  unfolding M_def set_of_list_def[symmetric] rev_map_fold
    HOL_list.fold_custom_empty hm.op_hms_empty_def[symmetric]
  by sepref

lemmas dom_M_eq = dom_M_eq1[OF M_assms, folded M_alt_def M_list'_def]

definition
  "Mi = hashmap_of_list (map (\<lambda>(k, dbms). (k, map IArray dbms)) M_list)"

lemma Mi_alt_def:
  "Mi = M1i TYPE(int DBMEntry list) M_list IArray"
  unfolding Mi_def M1i_def ..

lemmas map_of_M_list_M_rel = map_of_M_list_M_rel1[OF M_assms, folded M_alt_def]

lemmas Mi_M = Mi_M1[OF M_assms, folded M_alt_def Mi_alt_def]

lemmas L_dom_M_eqI = L_dom_M_eqI1[OF M_assms, folded M_alt_def]


paragraph \<open>Deriving the Reachability Checker\<close>
interpretation
  Reachability_Impl
  where A = mtx_assn
    and F = F
    and l\<^sub>0i = "return l\<^sub>0i"
    and s\<^sub>0 = init_dbm
    and s\<^sub>0i = init_dbm_impl
    and succs = succs_precise
    and succsi = succs_precise'_impl
    and less = "\<lambda> x y. dbm_subset n x y \<and> \<not> dbm_subset n y x"
    and less_eq = "dbm_subset n"
    and Lei = "dbm_subset_impl n"
    and E = op_precise.E_from_op_empty
    and Fi = F_impl
    and K = location_assn
    and keyi = "return o fst"
    and copyi = amtx_copy
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
    and L = "set L"
    and M = M
  apply standard
  subgoal (* L finite *)
    ..
  subgoal (* M finite *)
    by (rule M_finite)
  subgoal (* succs finite *)
    by (rule succs_precise_finite)
  subgoal (* succs empty *)
    unfolding succs_precise_def by auto
    (* using op.F_mono subsumes_simp_1 by fastforce *)
      (* subgoal (* L refine *)
    by (rule L_list_hnr) *)
      (* subgoal (* M refine *)
    unfolding PR_CONST_def by (rule M_table.refine) *)
  subgoal (* succs correct *)
    unfolding succs_precise_def op_precise.E_from_op_empty_def op_precise.E_from_op_def
    apply (auto dest!: trans_impl_trans_of)
    apply (auto dest!: trans_of_trans_impl)
    apply (intro exI conjI, erule image_eqI[rotated])
     apply auto
    done
  subgoal (* P correct *)
    by (auto dest: P_correct)
  subgoal (* key refine *)
    by sepref_to_hoare sep_auto
  apply (rule amtx_copy_hnr; fail) (* COPY implementation for dbms *)
  subgoal (* P refine *)
    by (rule P_impl_refine)
  subgoal (* F refine *)
    by (rule F_impl)
  subgoal (* succs refine *)
    using succs_precise_impl_refine unfolding b_assn_pure_conv .
  apply (rule location_assn_constraints; fail)+ (* location assn is correct *)
  subgoal (* init loc refine *)
    using init_impl states'_states by sepref_to_hoare sep_auto
  (* init dbm refine *)
         apply (unfold PR_CONST_def, rule init_dbm_impl.refine; fail)
  (* dbm subset relation is an ordering *)
  apply (rule HOL.refl; fail)
  apply (rule dbm_subset_refl; fail)
  apply (rule dbm_subset_trans; assumption)
  subgoal (* F mono *)
    by (rule F_mono)
  subgoal (* E_precise mono *)
    by (auto dest: op_precise.E_from_op_empty_mono')
  subgoal (* E_precise invariant *)
    by (clarsimp simp: op_precise.E_from_op_empty_def, frule op_precise.E_from_op_wf_state[rotated])
      (auto dest: E_from_op_states simp: wf_state_def)
  apply (rule dbm_subset_impl.refine; fail) (* dbm subset refinement *)
  done

lemmas reachability_impl = Reachability_Impl_axioms

context
  fixes Li_split :: "'si list list"
  assumes full_split: "set L_list = (\<Union>xs \<in> set Li_split. set xs)"
begin

interpretation Reachability_Impl_imp_to_pure_correct
  where A = mtx_assn
    and F = F
    and l\<^sub>0i = "return l\<^sub>0i"
    and s\<^sub>0 = init_dbm
    and s\<^sub>0i = init_dbm_impl
    and succs = succs_precise
    and succsi = succs_precise'_impl
    and less = "\<lambda> x y. dbm_subset n x y \<and> \<not> dbm_subset n y x"
    and less_eq = "dbm_subset n"
    and Lei = "dbm_subset_impl n"
    and lei = "\<lambda>as bs.
      (\<exists>i\<le>n. IArray.sub as (i + i * n + i) < Le 0) \<or> array_all2 (Suc n * Suc n) (\<le>) as bs"
    and E = op_precise.E_from_op_empty
    and Fi = F_impl
    and K = location_assn
    and keyi = "return o fst"
    and copyi = amtx_copy
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
    and L = "set L"
    and M = M
    and to_loc = id
    and from_loc = id
    and L_list = L_list
    and K_rel = location_rel
    and L' = L
    and Li = L_list
    and to_state = array_unfreeze
    and from_state = array_freeze
    and A_rel = "{(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}"
    and Mi = "\<lambda>k. Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k Mi"
  apply standard
  subgoal
    using L_list_rel by simp
  subgoal
    by (rule L_list_rel)
  subgoal
    ..
  subgoal for s1 s
    by (rule array_unfreeze_ht) simp
  subgoal for si s
    by (sep_auto heap: array_freeze_ht)
  subgoal
    by simp
  subgoal
    by simp
  subgoal
    by (rule right_unique_location_rel)
  subgoal
    using left_unique_location_rel unfolding IS_LEFT_UNIQUE_def .
  subgoal
    unfolding dbm_subset_def check_diag_def
    by (auto simp: array_all2_iff_pointwise_cmp[symmetric] iarray_mtx_relD)
  subgoal
    using full_split .
  using Mi_M .

concrete_definition certify_unreachable_pure
  uses pure.certify_unreachable_impl_pure_correct[unfolded to_pair_def get_succs_def] is "?f \<longrightarrow> _"

lemma certify_unreachable_pure_refine:
  assumes "fst ` set M_list = set L_list" certify_unreachable_pure
  shows "\<nexists>u l' u'. (\<forall>c\<le>n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F' (l', u')"
  using certify_unreachable_pure.refine[OF L_dom_M_eqI] assms op_precise_unreachable_correct by simp

end (* Fixed splitter *)

context
  fixes splitter :: "'s list \<Rightarrow> 's list list" and splitteri :: "'si list \<Rightarrow> 'si list list"
  assumes full_split: "set xs = (\<Union>xs \<in> set (splitter xs). set xs)"
      and same_split:
  "\<And>L Li.
    list_assn (list_assn location_assn) (splitter L) (splitteri Li) = list_assn location_assn L Li"
begin

lemmas certify_unreachable_impl_hnr =
  certify_unreachable_impl.refine[
    OF Reachability_Impl_axioms L_list_hnr, unfolded PR_CONST_def, OF M_table.refine,
    OF full_split same_split,
    FCOMP op_precise_unreachable_correct'
  ]

definition
  "unreachability_checker \<equiv>
  let
    Fi = F_impl;
    Pi = P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl n;
    l\<^sub>0i = Heap_Monad.return l\<^sub>0i;
    s\<^sub>0i = init_dbm_impl;
    succsi = succs_precise'_impl;
    M_table = M_table
  in
    certify_unreachable_impl Fi Pi copyi succsi l\<^sub>0i s\<^sub>0i Lei L_list M_table splitteri"

lemma unreachability_checker_alt_def:
  "unreachability_checker \<equiv>
  let
    Fi = F_impl;
    Pi = P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl n;
    l\<^sub>0i = Heap_Monad.return l\<^sub>0i;
    s\<^sub>0i = init_dbm_impl;
    succsi = succs_precise'_impl
  in do {
    M_table \<leftarrow> M_table;
    certify_unreachable_impl_inner Fi Pi copyi succsi l\<^sub>0i s\<^sub>0i Lei splitteri L_list M_table
  }"
  unfolding unreachability_checker_def certify_unreachable_impl_def Let_def .

lemmas unreachability_checker_hnr =
  certify_unreachable_impl_hnr[folded unreachability_checker_def[unfolded Let_def]]

lemmas unreachability_checker_alt_def' = unreachability_checker_alt_def[unfolded M_table_def]

definition
  "unreachability_checker2 \<equiv>
  let
    Fi = F_impl;
    Pi = P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl n;
    l\<^sub>0i = Heap_Monad.return l\<^sub>0i;
    s\<^sub>0i = init_dbm_impl;
    succsi = succs_precise'_impl;
    M_table = M_table
  in
    certify_unreachable_impl2 Fi Pi copyi succsi l\<^sub>0i s\<^sub>0i Lei splitteri L_list M_table"

lemmas unreachability_checker2_refine = certify_unreachable_impl2_refine[
    of L_list M_table splitter splitteri,
    OF L_list_hnr _ full_split same_split L_dom_M_eqI[symmetric],
    unfolded PR_CONST_def, OF M_table.refine,
    folded unreachability_checker2_def[unfolded Let_def],
    THEN mp, THEN op_precise_unreachable_correct
]

end (* Splitter *)

end (* M *)


paragraph \<open>Tables for Indexed Invariants\<close>
context
  fixes M_list :: "('si \<times> (int DBMEntry list \<times> nat) list) list"
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      and M_dbm_len: "list_all (\<lambda>(l, xs). list_all (\<lambda>(M, _). length M = Suc n * Suc n) xs) M_list"
begin

lemma conversions_param:
  "(\<lambda>(M, i). (IArray M, i), \<lambda>(M, i). (list_to_dbm n M, i))
\<in> {(x, y). x = y \<and> (\<lambda>(M, _). length M = Suc n * Suc n) x} \<rightarrow>
   {(a, b). iarray_mtx_rel (Suc n) (Suc n) b a} \<times>\<^sub>r Id"
  using IArray_list_to_dbm_rel by (auto dest!: fun_relD)

lemmas M2_assms =
  M_list_covered
  M_dbm_len
  conversions_param

definition
  "M_list2 \<equiv> map (\<lambda>(li, xs). (SOME l. (li, l) \<in> loc_rel, xs)) M_list"

definition
  "M2 = fold (\<lambda>p M.
    let
      s = fst p; xs = snd p;
      xs = rev (map (\<lambda>(M, i). (list_to_dbm n M, i)) xs);
      S = set xs in fun_upd M s (Some S)
  ) (PR_CONST M_list2) IICF_Map.op_map_empty"

lemma M_list2_alt_def:
  "M_list2 = M_list1 M_list"
  unfolding M_list2_def M_list1_def ..

lemma M2_alt_def:
  "M2 = M1 TYPE(int DBMEntry list \<times> nat) M_list (\<lambda>(M, i). (list_to_dbm n M, i))"
  unfolding M1_def M2_def M_list1_def M_list2_def ..

lemmas M2_finite = M1_finite[OF M2_assms, folded M2_alt_def]

lemmas L_dom_M_eqI2 = L_dom_M_eqI1[OF M2_assms, folded M2_alt_def M_list2_alt_def]

definition
  "M2i = hashmap_of_list (map (\<lambda>(k, dbms). (k, map (\<lambda>(M, i). (IArray M, i)) dbms)) M_list)"

lemma M2i_alt_def:
  "M2i = M1i TYPE(int DBMEntry list \<times> nat) M_list (\<lambda>(M, i). (IArray M, i))"
  unfolding M2i_def M1i_def ..

lemmas map_of_M_list_M_rel2 = map_of_M_list_M_rel1[OF M2_assms, folded M2_alt_def]

lemmas Mi_M2 = Mi_M1[OF M2_assms, folded M2i_alt_def M2_alt_def]


paragraph \<open>Deriving the Büchi Checker\<close>
interpretation
  Buechi_Impl_pre
  where F = F
    and succs = succs_precise
    and less = "\<lambda> x y. dbm_subset n x y \<and> \<not> dbm_subset n y x"
    and less_eq = "dbm_subset n"
    and E = op_precise.E_from_op_empty
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and L = "set L"
    and M = "\<lambda>x. case M2 x of None \<Rightarrow> {} | Some S \<Rightarrow> S"
  apply standard
  subgoal (* succs correct *)
    unfolding succs_precise_def op_precise.E_from_op_empty_def op_precise.E_from_op_def
    apply (auto dest!: trans_impl_trans_of)
    apply (auto dest!: trans_of_trans_impl)
    apply (intro exI conjI, erule image_eqI[rotated])
     apply auto
    done
  (* dbm subset relation is an ordering *)
  apply (rule HOL.refl; fail)
  apply (rule dbm_subset_refl; fail)
  apply (rule dbm_subset_trans; assumption)
  subgoal (* P correct *)
    by (auto dest: P_correct)
  subgoal (* F mono *)
    by (rule F_mono)
  subgoal (* L finite *)
    ..
  subgoal (* M finite *)
    using M2_finite by (auto split: option.split intro: ranI)
  done


context
  fixes Li_split :: "'si list list"
  assumes full_split: "set L_list = (\<Union>xs \<in> set Li_split. set xs)"
  fixes init_locsi :: "'si list" and init_locs :: "'s set"
  assumes init_locs_in_states: "init_locs \<subseteq> states'"
  assumes initsi_inits:
    "(init_locsi, init_locs) \<in> \<langle>loc_rel\<rangle>list_set_rel"
begin

definition
  "init_locs1 = (SOME xs. set xs = init_locs \<and> (init_locsi, xs) \<in> \<langle>loc_rel\<rangle>list_rel)"

lemma init_locs1:
  "set init_locs1 = init_locs \<and> (init_locsi, init_locs1) \<in> \<langle>loc_rel\<rangle>list_rel"
  using initsi_inits unfolding list_set_rel_def
  apply (elim relcompE)
  unfolding init_locs1_def
  apply (rule someI)
  apply auto
  done

lemma init_locsi_init_locs1:
  "(init_locsi, init_locs1) \<in> \<langle>location_rel\<rangle>list_rel"
  using init_locs1 init_locs_in_states unfolding b_rel_def
  unfolding list_rel_def by (auto elim!: list.rel_mono_strong)

lemma [sepref_fr_rules]:
  "(uncurry0 (return li), uncurry0 (RETURN (PR_CONST l)))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a location_assn" if "(li, l) \<in> loc_rel" "l \<in> states'"
  using that by sepref_to_hoare sep_auto

lemma init_locsi_refine[sepref_fr_rules]:
  "(uncurry0 (return init_locsi), uncurry0 (RETURN (PR_CONST init_locs1)))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn location_assn"
proof -
  let ?x = "list_assn (\<lambda>a c. \<up> ((c, a) \<in> loc_rel \<and> a \<in> states'))"
  have "?x = pure (\<langle>location_rel\<rangle>list_rel)"
    unfolding fcomp_norm_unfold unfolding b_assn_def pure_def by simp
  then have "emp \<Longrightarrow>\<^sub>A ?x init_locs1 init_locsi * true"
    using init_locsi_init_locs1 by (simp add: pure_app_eq)
  then show ?thesis
    by sepref_to_hoare sep_auto
qed

definition
  "inits = map (\<lambda>l. (l, init_dbm)) init_locs1"

interpretation DBM_Impl n .

sepref_register init_locs1

sepref_definition initsi
  is "uncurry0 (RETURN (PR_CONST inits))"
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (prod_assn location_assn mtx_assn)"
  unfolding inits_def PR_CONST_def
  unfolding map_by_foldl[symmetric] foldl_conv_fold HOL_list.fold_custom_empty
  by sepref

interpretation Buechi_Impl_imp_to_pure_correct
  where A = mtx_assn
    and F = F
    and succs = succs_precise
    and succsi = succs_precise'_impl
    and less = "\<lambda> x y. dbm_subset n x y \<and> \<not> dbm_subset n y x"
    and less_eq = "dbm_subset n"
    and Lei = "dbm_subset_impl n"
    and lei = "\<lambda>as bs.
      (\<exists>i\<le>n. IArray.sub as (i + i * n + i) < Le 0) \<or> array_all2 (Suc n * Suc n) (\<le>) as bs"
    and E = op_precise.E_from_op_empty
    and Fi = F_impl
    and K = location_assn
    and keyi = "return o fst"
    and copyi = amtx_copy
    and P = "\<lambda>(l, M). l \<in> states' \<and> wf_dbm M"
    and P' = P
    and Pi = P_impl
    and L = "set L"
    and M = M2
    and to_loc = id
    and from_loc = id
    and L_list = L_list
    and K_rel = location_rel
    and L' = L
    and Li = L_list
    and to_state = array_unfreeze
    and from_state = array_freeze
    and A_rel = "{(a, b). iarray_mtx_rel (Suc n) (Suc n) b a}"
    and Mi = "\<lambda>k. Impl_Array_Hash_Map.ahm_lookup (=) bounded_hashcode_nat k M2i"
    and inits = inits
    and initsi = "initsi"
  apply standard
  subgoal (* key refine *)
    by sepref_to_hoare sep_auto
           apply (rule amtx_copy_hnr; fail)
  subgoal (* P refine *)
    by (rule P_impl_refine)
  subgoal (* F refine *)
    by (rule F_impl)
  subgoal (* succs refine *)
    using succs_precise_impl_refine unfolding b_assn_pure_conv .
       apply (rule dbm_subset_impl.refine; fail)
    apply (rule location_assn_constraints; fail)+
  subgoal
    using L_list_rel by simp
  subgoal
    by (rule L_list_rel)
  subgoal
    ..
  subgoal for s1 s
    by (rule array_unfreeze_ht) simp
  subgoal for si s
    by (sep_auto heap: array_freeze_ht)
  subgoal
    by simp
  subgoal
    by simp
  subgoal
    by (rule right_unique_location_rel)
  subgoal
    using left_unique_location_rel unfolding IS_LEFT_UNIQUE_def .
  subgoal
    unfolding dbm_subset_def check_diag_def
    by (auto simp: array_all2_iff_pointwise_cmp[symmetric] iarray_mtx_relD)
  subgoal
    using full_split .
  subgoal
    using initsi.refine .
  subgoal
    using Mi_M2 .
  subgoal (* E_precise mono *)
    by (auto dest: op_precise.E_from_op_empty_mono')
  subgoal (* E_precise invariant *)
    by (clarsimp simp: op_precise.E_from_op_empty_def, frule op_precise.E_from_op_wf_state[rotated])
       (auto dest: E_from_op_states simp: wf_state_def)
  done

concrete_definition certify_no_buechi_run_pure
  uses pure.certify_no_buechi_run_impl_pure_correct[unfolded to_pair_def get_succs_def]
  is "?f \<longrightarrow> _"

lemma certify_no_buechi_run_pure_refine:
  assumes "fst ` set M_list = set L_list" certify_no_buechi_run_pure
  and F_F1: "\<And>l\<^sub>0 l D Z. l\<^sub>0 \<in> init_locs \<Longrightarrow> op_precise.E_from_op_empty\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) (l, D)
          \<Longrightarrow> dbm.zone_of (curry (conv_M D)) = Z \<Longrightarrow> F (l, D) = F1 (l, Z)"
  shows "\<nexists>l\<^sub>0 u xs. l\<^sub>0 \<in> init_locs \<and> (\<forall>c\<le>n. u c = 0) \<and> run ((l\<^sub>0, u) ## xs) \<and> alw (ev (holds F')) ((l\<^sub>0, u) ## xs)"
  using certify_no_buechi_run_pure.refine[OF L_dom_M_eqI2] assms(1,2)
    op_precise_buechi_run_correct[OF _ F_F1]
  unfolding inits_def using init_locs1 by simp

end (* Fixed splitter *)

end (* M *)

end (* L *)

end (* Reachability Problem Impl Precise *)


paragraph \<open>Deriving the Deadlock Checker\<close>

context TA_Impl_Precise
begin

lemma (in TA_Impl) dbm_subset_correct:
  assumes "wf_dbm D" and "wf_dbm M"
  shows "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<subseteq> [curry (conv_M M)]\<^bsub>v,n\<^esub> \<longleftrightarrow> dbm_subset n D M"
  unfolding dbm_subset_correct''[OF assms] using dbm_subset_conv_rev dbm_subset_conv ..

lemma empty_steps_states':
  "l' \<in> states'" if "op_precise.E_from_op_empty\<^sup>*\<^sup>* (l, D) (l', D')" "l \<in> states'"
  using that
proof (induction "(l, D)" "(l', D')" arbitrary: l' D')
  case rtrancl_refl
  then show ?case
    by simp
next
  case (rtrancl_into_rtrancl b)
  then show ?case
    by (cases b) (auto simp add: op_precise.E_from_op_empty_def intro: E_from_op_states)
qed

interpretation deadlock: Reachability_Problem_Impl_Precise where
  F = "\<lambda>(l, D). \<not> (check_deadlock_dbm l D)" and
  F1 = "\<lambda>(l, Z). \<not> (TA.check_deadlock l Z)" and
  F' = deadlocked and
  F_impl = "\<lambda>(l, M). do {r \<leftarrow> check_deadlock_impl l M; return (\<not> r)}"
  apply standard
(* mono *)
  subgoal for a b
    apply clarsimp
    apply (auto dest: TA.check_deadlock_anti_mono simp:
        dbm_subset_correct[symmetric] check_deadlock_dbm_correct'[symmetric, unfolded wf_state_def])
    done
(* compatible zone *)
  subgoal
    using
      Bisimulation_Invariant.B_steps_invariant[OF op_precise.step_z_dbm'_E_from_op_bisim_empty]
      wf_state_init states'_states
    unfolding a\<^sub>0_def
    by simp (subst check_deadlock_dbm_correct'[symmetric], auto elim: empty_steps_states')
(* compatible semantics *)
  subgoal for l u Z
    unfolding TA.check_deadlock_correct_step' deadlocked_def by auto
(* implementation correct *)
  subgoal
  proof -
    define location_assn' where "location_assn' = location_assn"
    define mtx_assn' :: "_ \<Rightarrow> int DBMEntry Heap.array \<Rightarrow> _" where "mtx_assn' = mtx_assn n"
    note [sep_heap_rules] = check_deadlock_impl.refine[
        to_hnr, unfolded hn_refine_def hn_ctxt_def,
        folded location_assn'_def mtx_assn'_def, simplified]
    show ?thesis
      unfolding location_assn'_def[symmetric] mtx_assn'_def[symmetric]
      by sepref_to_hoare (sep_auto simp: pure_def)
  qed
  done

lemma deadlock_unreachability_checker2_hnr:
  fixes P_loc :: "'si \<Rightarrow> bool"
    and L_list :: "'si list"
    and M_list :: "('si \<times> int DBMEntry list list) list"
  fixes splitter :: "'s list \<Rightarrow> 's list list" and splitteri :: "'si list \<Rightarrow> 'si list list"
  assumes "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
    and "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"
    and "list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = Suc n * Suc n) xs) M_list"
    and "fst ` set M_list = set L_list"
  assumes full_split: "\<And>xs. set xs = (\<Union>xs \<in> set (splitter xs). set xs)"
    and same_split:
    "\<And>L Li.
      list_assn (list_assn location_assn) (splitter L) (splitteri Li) = list_assn location_assn L Li"
  shows
    "deadlock.unreachability_checker2 L_list M_list splitteri
    \<longrightarrow> (\<forall>u. (\<forall>c\<le>n. u c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u))"
  using deadlock.unreachability_checker2_refine[
      OF assms(1-2) assms(4)[THEN equalityD1] assms(3) full_split same_split assms(4)
      ]
  unfolding deadlock_def steps'_iff[symmetric] by auto

lemma deadlock_unreachability_checker3_hnr:
  fixes P_loc :: "'si \<Rightarrow> bool"
    and L_list :: "'si list"
    and M_list :: "('si \<times> int DBMEntry list list) list"
  fixes Li_split :: "'si list list"
  assumes "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
    and "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"
    and "list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = Suc n * Suc n) xs) M_list"
    and "fst ` set M_list = set L_list"
  assumes full_split: "set L_list = (\<Union>xs \<in> set Li_split. set xs)"
  shows
    "deadlock.certify_unreachable_pure L_list M_list Li_split
    \<longrightarrow> (\<forall>u. (\<forall>c\<le>n. u c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u))"
  using deadlock.certify_unreachable_pure_refine[
      OF assms(1-2) assms(4)[THEN equalityD1] assms(3) full_split assms(4)
      ]
  unfolding deadlock_def steps'_iff[symmetric] by auto

lemmas deadlock_unreachability_checker2_def = deadlock.unreachability_checker2_def

lemmas deadlock_unreachability_checker_alt_def = deadlock.unreachability_checker_alt_def

lemmas deadlock_unreachability_checker3_def = deadlock.certify_unreachable_pure_def

lemma deadlock_unreachability_checker_hnr:
  fixes P_loc :: "'si \<Rightarrow> bool"
    and L_list :: "'si list"
    and M_list :: "('si \<times> int DBMEntry list list) list"
  fixes splitter :: "'s list \<Rightarrow> 's list list" and splitteri :: "'si list \<Rightarrow> 'si list list"
  assumes "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
    and "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"
    and "fst ` set M_list \<subseteq> set L_list"
    and "list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = Suc n * Suc n) xs) M_list"
    and "set (deadlock.L L_list) = dom (deadlock.M M_list)"
  assumes full_split: "\<And>xs. set xs = (\<Union>xs \<in> set (splitter xs). set xs)"
      and same_split:
    "\<And>L Li.
      list_assn (list_assn location_assn) (splitter L) (splitteri Li) = list_assn location_assn L Li"
  shows
    "(uncurry0
       (Reachability_Problem_Impl_Precise.unreachability_checker n trans_impl l\<^sub>0i op_impl
         states_mem_impl (\<lambda>(l, M). check_deadlock_impl l M \<bind> (\<lambda>r. return (\<not> r))) L_list M_list splitteri),
      uncurry0
       (SPEC
         (\<lambda>r. r \<longrightarrow> (\<forall>u. (\<forall>c\<le>n. u c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u)))))
     \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using deadlock.unreachability_checker_hnr[OF assms(1-4), OF _ full_split same_split assms(5)]
  unfolding deadlock_def steps'_iff[symmetric] by simp linarith

end (* TA Impl Precise *)

concrete_definition (in -) unreachability_checker
  uses Reachability_Problem_Impl_Precise.unreachability_checker_alt_def

end