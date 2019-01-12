theory Simple_Network_Language_Certificate_Checking
  imports
    "../Normalized_Zone_Semantics_Certification_Impl"
    Simple_Network_Language_Model_Checking
begin

(* XXX Merge proof with Ex_ev *)
lemma (in Graph_Defs) Ex_ev_reaches:
  "\<exists> y. x \<rightarrow>* y \<and> \<phi> y" if "Ex_ev \<phi> x"
  using that unfolding Ex_ev_def
proof safe
  fix xs assume prems: "run (x ## xs)" "ev (holds \<phi>) (x ## xs)"
  show "\<exists>y. x \<rightarrow>* y \<and> \<phi> y"
  proof (cases "\<phi> x")
    case True
    then show ?thesis
      by auto
  next
    case False
    with prems obtain y ys zs where
      "\<phi> y" "xs = ys @- y ## zs" "y \<notin> set ys"
      unfolding ev_holds_sset by (auto elim!:split_stream_first)
    with prems have "steps (x # ys @ [y])"
      by (auto intro: run_decomp[THEN conjunct1]) (* XXX *)
    with \<open>\<phi> y\<close> show ?thesis
      including graph_automation by (auto 4 3)
  qed
qed

context Simple_Network_Impl_nat_ceiling_start_state
begin

sublocale impl: Reachability_Problem_Impl_Precise
  where trans_fun = trans_from
  and inv_fun = inv_fun
  and F_fun = Fi
  and ceiling = k_impl
  and A = prod_ta
  and l\<^sub>0 = l\<^sub>0
  and l\<^sub>0i = l\<^sub>0i
  and F = "PR_CONST F"
  and n = m
  and k = k_fun
  and trans_impl = trans_impl
  and states' = states'
  and loc_rel = loc_rel
  and f = impl.E_precise_op'
  and op_impl = "PR_CONST impl.E_precise_op'_impl"
  and states_mem_impl = states'_memi
  by standard (unfold PR_CONST_def, rule impl.E_precise_op'_impl.refine, rule states'_memi_correct)

definition
  "unreachability_checker L_list M_list \<equiv>
  let
    Fi = impl.F_impl';
    Pi = impl.P_impl;
    copyi = amtx_copy;
    Lei = dbm_subset_impl m;
    l\<^sub>0i = return l\<^sub>0i;
    s\<^sub>0i = impl.init_dbm_impl;
    succsi = impl.succs_precise'_impl;
    M_table = impl.M_table M_list
  in
  certify_unreachable_impl Fi Pi copyi Lei l\<^sub>0i s\<^sub>0i succsi L_list M_table"

lemma state_impl_abstract':
  assumes "states'_memi li"
  shows "\<exists>l. (li, l) \<in> loc_rel"
proof -
  obtain Li si where "li = (Li, si)"
    by force
  with state_impl_abstract[of Li si] show ?thesis
    using assms unfolding states'_memi_def states_def by auto
qed

lemmas unreachability_checker_hnr' =
  impl.certify_unreachable_impl_hnr[folded unreachability_checker_def[unfolded Let_def],
    OF state_impl_abstract']

interpretation Bisimulation_Invariant
  "(\<lambda>(l, u) (l', u'). conv_A prod_ta \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(L, s, u) (L', s', u'). Simple_Network_Language.conv A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
  "(\<lambda>((L, s), u) (L', s', u'). L = L' \<and> u = u' \<and> s = s')"
  "(\<lambda>((L, s), u). conv.all_prop L s)"
  "(\<lambda>(L, s, u). conv.all_prop L s)"
  by (rule prod_bisim)

lemma unreachability_prod:
  assumes
    "formula = formula.EX \<phi>"
    "(\<nexists>u l' u'. (\<forall>c\<le>m. u c = 0) \<and> conv_A prod_ta \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> PR_CONST F l')"
  shows "\<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula"
proof -
  let ?check = "\<not> B.Ex_ev (\<lambda>(L, s, _). check_sexp \<phi> L (the \<circ> s)) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0)"
  have *: "PR_CONST F l \<longleftrightarrow> (\<lambda>((L, s), _). check_sexp \<phi> L (the o s)) (l, u)"
    for l and u :: "nat \<Rightarrow> real"
    unfolding assms(1) by auto
  have "conv.all_prop L\<^sub>0 (map_of s\<^sub>0)"
    using all_prop_start unfolding conv_all_prop .
  then have
    "?check \<longleftrightarrow> \<not> reach.Ex_ev (\<lambda> ((L, s), _). check_sexp \<phi> L (the o s)) (l\<^sub>0, u\<^sub>0)"
    by (auto intro!: Ex_ev_iff[symmetric, unfolded A_B.equiv'_def])
  also from assms(2) have "\<dots>"
    apply -
    apply standard
    apply (drule reach.Ex_ev_reaches)
    unfolding impl.reaches_steps'[symmetric]
    apply (subst (asm) *)
    apply force
    done
  finally show ?thesis
    using assms unfolding models_def by simp
qed

theorem unreachability_checker_hnr:
  assumes "\<And>li. P_loc li \<Longrightarrow> states'_memi li"
    and "list_all (\<lambda>x. P_loc x \<and> states'_memi x) L_list"
    and "fst ` set M_list \<subseteq> set L_list"
    and "formula = formula.EX \<phi>"
  shows "(
  uncurry0 (unreachability_checker L_list M_list),
  uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
    \<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula)))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  supply [sep_heap_rules] =
    unreachability_checker_hnr'[OF assms(1-3), to_hnr, unfolded hn_refine_def, rule_format]
  using unreachability_prod[OF assms(4)] by sepref_to_hoare (sep_auto simp: pure_def)

end (* Simple_Network_Impl_nat_ceiling_start_state *)

concrete_definition unreachability_checker uses
  Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker_def

definition
  "certificate_checker
    broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula M_list \<equiv>
  let
    check1 = Simple_Network_Impl_nat_ceiling_start_state
      broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    L_list = map fst M_list;
    check2 = list_all (Simple_Network_Impl_nat_defs.states'_memi broadcast bounds' automata) L_list;
    check3 = (case formula of formula.EX _ \<Rightarrow> True | _ \<Rightarrow> False)
  in if check1 \<and> check2 \<and> check3 then
  do {
    r \<leftarrow> unreachability_checker
      broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 formula L_list M_list;
    return (Some r)
  } else return None"

theorem certificate_check:
  "<emp> certificate_checker
    broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula M_list
   <\<lambda> Some r \<Rightarrow> \<up>(r \<longrightarrow> \<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula)
    | None \<Rightarrow> true>\<^sub>t"
proof -
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  { fix \<phi> assume A: "formula = formula.EX \<phi>"
    note
      Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker_hnr[
        of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
           "Simple_Network_Impl_nat_defs.states'_memi broadcast bounds automata"
           "map fst M_list" M_list,
        folded A_def check_def has_deadlock_def,
        to_hnr, unfolded hn_refine_def, rule_format,
        OF _ _ _ _ A, unfolded A]
  } note *[sep_heap_rules] = this
  show ?thesis
    unfolding A_def[symmetric] check_def[symmetric]
    unfolding certificate_checker_def
    by (sep_auto simp: unreachability_checker.refine[symmetric] pure_def split: formula.split_asm)
qed

end