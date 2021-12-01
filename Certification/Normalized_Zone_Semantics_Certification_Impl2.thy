theory Normalized_Zone_Semantics_Certification_Impl2
  imports
    Normalized_Zone_Semantics_Certification_Impl
    Certification.Unreachability_Certification
begin


context Reachability_Problem_Impl_Precise
begin

context
  fixes L_list :: "'si list" and P_loc and M_list :: "('si \<times> int DBMEntry list list) list"
  assumes state_impl_abstract: "\<And>li. P_loc li \<Longrightarrow> \<exists>l. (li, l) \<in> loc_rel"
  assumes P_loc: "list_all (\<lambda>x. P_loc x \<and> states_mem_impl x) L_list"
  assumes M_list_covered: "fst ` set M_list \<subseteq> set L_list"
      and M_dbm_len: "list_all (\<lambda>(l, xs). list_all (\<lambda>M. length M = Suc n * Suc n) xs) M_list"
begin

lemmas table_axioms = state_impl_abstract P_loc M_list_covered M_dbm_len

context
  fixes splitter :: "'s list \<Rightarrow> 's list list" and splitteri :: "'si list \<Rightarrow> 'si list list"
  assumes full_split: "set xs = (\<Union>xs \<in> set (splitter xs). set xs)"
      and same_split:
  "\<And>L Li.
    list_assn (list_assn location_assn) (splitter L) (splitteri Li) = list_assn location_assn L Li"
begin

lemma certify_unreachable_impl_hnr:
  assumes "set (L L_list) = dom (M M_list)"
  shows
  "(uncurry0
    (certify_unreachable_impl F_impl P_impl amtx_copy (dbm_subset_impl n) succs_precise'_impl
    (return l\<^sub>0i) init_dbm_impl L_list (M_table M_list) splitteri),
    uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
      (\<nexists>u l' u'. (\<forall>c\<le>n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F' (l', u')))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  by (rule certify_unreachable_impl_hnr)
     (rule table_axioms full_split same_split L_dom_M_eqI[symmetric] assms | assumption)+

definition
  "unreachability_checker' \<equiv>
  let
    Fi = F_impl;
    Pi = P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl n;
    l\<^sub>0i = Heap_Monad.return l\<^sub>0i;
    s\<^sub>0i = init_dbm_impl;
    succsi = succs_precise'_impl;
    M_table = M_table M_list
  in
    certify_unreachable_impl Fi Pi copyi Lei succsi l\<^sub>0i s\<^sub>0i L_list M_table splitteri"

lemma unreachability_checker_alt_def:
  "unreachability_checker' \<equiv>
  let
    Fi = F_impl;
    Pi = P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl n;
    l\<^sub>0i = Heap_Monad.return l\<^sub>0i;
    s\<^sub>0i = init_dbm_impl;
    succsi = succs_precise'_impl
  in do {
    M_table \<leftarrow> M_table M_list;
    certify_unreachable_impl_inner Fi Pi copyi Lei succsi l\<^sub>0i s\<^sub>0i splitteri L_list M_table
  }"
  unfolding unreachability_checker'_def certify_unreachable_impl_def Let_def .

lemmas unreachability_checker_hnr =
  certify_unreachable_impl_hnr[folded unreachability_checker'_def[unfolded Let_def]]

lemmas unreachability_checker_alt_def' = unreachability_checker_alt_def[unfolded M_table_def]

definition
  "unreachability_checker2' \<equiv>
  let
    Fi = F_impl;
    Pi = P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl n;
    l\<^sub>0i = Heap_Monad.return l\<^sub>0i;
    s\<^sub>0i = init_dbm_impl;
    succsi = succs_precise'_impl;
    M_table = M_table M_list
  in
    certify_unreachable_impl2 Fi Pi copyi Lei succsi l\<^sub>0i s\<^sub>0i splitteri L_list M_table"

lemma unreachability_checker2_refine:
  assumes "fst ` set M_list = set L_list" "unreachability_checker2 L_list M_list splitteri"
  shows "\<nexists>u l' u'. (\<forall>c\<le>n. u c = 0) \<and> conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F' (l', u')"
  by (rule unreachability_checker2_refine table_axioms assms full_split same_split | assumption)+

lemma unreachability_checker2'_is_unreachability_checker2:
  "unreachability_checker2' = unreachability_checker2 L_list M_list splitteri"
  unfolding unreachability_checker2'_def
  by (subst unreachability_checker2_def)
     (rule table_axioms full_split same_split HOL.refl | assumption)+

end (* Splitter *)

end (* L and M *)

end (* Reachability Problem Impl Precise *)



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
       (Reachability_Problem_Impl_Precise.unreachability_checker' n trans_impl l\<^sub>0i op_impl
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