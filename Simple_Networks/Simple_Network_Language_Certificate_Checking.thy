theory Simple_Network_Language_Certificate_Checking
  imports
    "../Normalized_Zone_Semantics_Certification_Impl"
    Simple_Network_Language_Export_Code
    "../library/Trace_Timing"
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

lemma state_impl_abstract':
  assumes "states'_memi li"
  shows "\<exists>l. (li, l) \<in> loc_rel"
proof -
  obtain Li si where "li = (Li, si)"
    by force
  with state_impl_abstract[of Li si] show ?thesis
    using assms unfolding states'_memi_def states_def by auto
qed

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
  uncurry0 (impl.unreachability_checker L_list M_list),
  uncurry0 (SPEC (\<lambda>r. r \<longrightarrow>
    \<not> Simple_Network_Language.conv A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_. 0) \<Turnstile> formula)))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  define checker where "checker \<equiv> impl.unreachability_checker L_list M_list"
  note [sep_heap_rules] =
    impl.unreachability_checker_hnr[
      OF state_impl_abstract', OF assms(1-3),
      to_hnr, unfolded hn_refine_def, rule_format, folded checker_def
    ]
  show ?thesis
    unfolding checker_def[symmetric] using unreachability_prod[OF assms(4)]
    by sepref_to_hoare (sep_auto simp: pure_def)
qed

schematic_goal succs_impl_alt_def:
  "impl.succs_precise'_impl \<equiv> ?impl"
  unfolding impl.succs_precise'_impl_def impl.succs_precise_inner_impl_def
  apply (abstract_let impl.E_precise_op'_impl E_op_impl)
  unfolding impl.E_precise_op'_impl_def fw_impl'_int
  apply (abstract_let trans_impl trans_impl)
  unfolding trans_impl_def
  apply (abstract_let int_trans_impl int_trans_impl)
  apply (abstract_let bin_trans_from_impl bin_trans_impl)
  apply (abstract_let broad_trans_from_impl broad_trans_impl)
  unfolding int_trans_impl_def bin_trans_from_impl_def broad_trans_from_impl_def
  apply (abstract_let trans_in_broad_grouped trans_in_broad_grouped)
  apply (abstract_let trans_out_broad_grouped trans_out_broad_grouped)
  apply (abstract_let trans_in_map trans_in_map)
  apply (abstract_let trans_out_map trans_out_map)
  apply (abstract_let int_trans_from_all_impl int_trans_from_all_impl)
  unfolding int_trans_from_all_impl_def
  apply (abstract_let int_trans_from_vec_impl int_trans_from_vec_impl)
  unfolding int_trans_from_vec_impl_def
  apply (abstract_let int_trans_from_loc_impl int_trans_from_loc_impl)
  unfolding int_trans_from_loc_impl_def
  apply (abstract_let trans_i_map trans_i_map)
  unfolding trans_out_broad_grouped_def trans_out_broad_map_def
  unfolding trans_in_broad_grouped_def trans_in_broad_map_def
  unfolding trans_in_map_def trans_out_map_def
  unfolding trans_i_map_def
  apply (abstract_let trans_map trans_map)
  apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> _" inv_fun)
  unfolding inv_fun_alt_def
  apply (abstract_let invs2 invs)
  unfolding invs2_def
  apply (abstract_let n_ps n_ps)
  by (rule Pure.reflexive)

context
  fixes L_list and M_list :: "((nat list \<times> int list) \<times> int DBMEntry list list) list"
  assumes assms:
    "list_all states'_memi L_list"
    "fst ` set M_list \<subseteq> set L_list"
begin

private lemma A:
  "list_all (\<lambda>x. states'_memi x \<and> states'_memi x) L_list"
  using assms by simp

lemma unreachability_checker_def:
  "impl.unreachability_checker L_list M_list \<equiv>
   let Fi = impl.F_impl'; Pi = impl.P_impl; copyi = amtx_copy; Lei = dbm_subset_impl m;
       l\<^sub>0i = Heap_Monad.return l\<^sub>0i; s\<^sub>0i = impl.init_dbm_impl; succsi = impl.succs_precise'_impl;
       _ = start_timer ();
       M_table = impl.M_table M_list;
       _ = save_time STR ''Time for loading certificate''
   in do {
    let _ = start_timer ();
    r \<leftarrow> certify_unreachable_impl Fi Pi copyi Lei l\<^sub>0i s\<^sub>0i succsi L_list M_table;
    let _ = save_time STR ''Time for main part of certificate checking'';
    Heap_Monad.return r
  }"
  by (subst impl.unreachability_checker_def[OF state_impl_abstract', OF _ A assms(2)]; simp)

schematic_goal unreachability_checker_alt_def:
  "impl.unreachability_checker L_list M_list \<equiv> ?x"
  apply (subst unreachability_checker_def)
  apply (subst impl.M_table_def[OF state_impl_abstract', of states'_memi, OF _ A assms(2)])
   apply assumption
  unfolding impl.F_impl'_def impl.P_impl_def
  apply (abstract_let states'_memi check_states)
  unfolding states'_memi_def states_mem_compute'
  apply (abstract_let "map states_i [0..<n_ps]" states_i)
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

end (* Anonymous context *)

end (* Simple_Network_Impl_nat_ceiling_start_state *)

concrete_definition unreachability_checker uses
  Simple_Network_Impl_nat_ceiling_start_state.unreachability_checker_alt_def

lemma states'_memi_alt_def:
  "Simple_Network_Impl_nat_defs.states'_memi broadcast bounds' automata = (
     \<lambda>(L, s).
    let
      n_ps = length automata;
      n_vs = Simple_Network_Impl.n_vs bounds';
      states_i = map (Simple_Network_Impl_nat_defs.states_i automata) [0..<n_ps]
    in
      length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> states_i ! i) \<and>
      length s = n_vs \<and> Simple_Network_Impl_nat_defs.check_boundedi bounds' s
    )
    "
  unfolding Simple_Network_Impl_nat_defs.states'_memi_def
  unfolding Simple_Network_Impl_nat_defs.states_mem_compute'
  unfolding Prod_TA_Defs.n_ps_def list_all_iff
  by (intro ext) simp

definition
  "certificate_checker
    M_list broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula \<equiv>
  let
    _ = start_timer ();
    check1 = Simple_Network_Impl_nat_ceiling_start_state
      broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula;
    _ = save_time STR ''Time to check ceiling'';
    L_list = map fst M_list;
    n_ps = length automata;
    n_vs = Simple_Network_Impl.n_vs bounds';
    states_i = map (Simple_Network_Impl_nat_defs.states_i automata) [0..<n_ps];
    _ = start_timer ();
    check2 = list_all (\<lambda>(L, s). length L = n_ps \<and> (\<forall>i<n_ps. L ! i \<in> states_i ! i) \<and>
      length s = n_vs \<and> Simple_Network_Impl_nat_defs.check_boundedi bounds' s
    ) L_list;
    _ = save_time STR ''Time to check states'';
    check3 = (case formula of formula.EX _ \<Rightarrow> True | _ \<Rightarrow> False)
  in if check1 \<and> check2 \<and> check3 then
  do {
    r \<leftarrow> unreachability_checker
      broadcast bounds' automata m num_states num_actions L\<^sub>0 s\<^sub>0 formula L_list M_list;
    Heap_Monad.return (Some r)
  } else Heap_Monad.return None"

theorem certificate_check:
  "<emp> certificate_checker
    M_list broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
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
  } note *[sep_heap_rules] = this[simplified, unfolded hd_of_formulai.simps[abs_def]]
  show ?thesis
    unfolding A_def[symmetric] check_def[symmetric]
    unfolding certificate_checker_def
    unfolding Let_def
    unfolding states'_memi_alt_def[unfolded Let_def, symmetric, of automata bounds broadcast]
    by (sep_auto simp: unreachability_checker.refine[symmetric] pure_def split: formula.split_asm)
qed

definition rename_check where
  "rename_check dc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
    state_space
\<equiv>
do {
  r \<leftarrow> do_rename_mc (
      \<lambda>(show_clock :: (nat \<Rightarrow> string)) (show_state :: (nat list \<times> int list \<Rightarrow> char list)).
      certificate_checker state_space)
    dc broadcast bounds' automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks; *)
    (\<lambda>_ _. '' '') (\<lambda>_. '' '') (\<lambda>_. '' '');
  case r of Some r \<Rightarrow>
    case r of
      None \<Rightarrow> Heap_Monad.return Preconds_Unsat
    | Some False \<Rightarrow> Heap_Monad.return Unsat
    | Some True \<Rightarrow> Heap_Monad.return Sat
  | None \<Rightarrow> Heap_Monad.return Renaming_Failed}
"

theorem certificate_check_rename:
  "<emp> rename_check False broadcast bounds automata k L\<^sub>0 s\<^sub>0 formula
    m num_states num_actions renum_acts renum_vars renum_clocks renum_states
    (* inv_renum_states inv_renum_vars inv_renum_clocks *)
    state_space
    <\<lambda> Sat \<Rightarrow> \<up>(
        (\<not> N broadcast automata bounds,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula))
     | Renaming_Failed \<Rightarrow> \<up>(\<not> Simple_Network_Rename_Formula
        broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0)
     | Unsat \<Rightarrow> true
     | Preconds_Unsat \<Rightarrow> true
    >\<^sub>t"
proof -
  have *: "
    Simple_Network_Rename_Formula_String
        broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0
  = Simple_Network_Rename_Formula
        broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0
  "
    unfolding
      Simple_Network_Rename_Formula_String_def Simple_Network_Rename_Formula_def
      Simple_Network_Rename_def Simple_Network_Rename_Formula_axioms_def
    using infinite_literal by auto
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> formula"
  define A' where "A' \<equiv> N
    (map renum_acts broadcast)
    (map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata)
    (map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds)"
  define check' where "check' \<equiv>
    A',(map_index renum_states L\<^sub>0, map_of (map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0), \<lambda>_ . 0) \<Turnstile>
    map_formula renum_states renum_vars id formula"
  define renaming_valid where "renaming_valid \<equiv>
    Simple_Network_Rename_Formula
      broadcast bounds renum_vars renum_clocks renum_states automata formula s\<^sub>0 L\<^sub>0
  "
  have [simp]: "check \<longleftrightarrow> check'" 
    if renaming_valid
    using that unfolding check_def check'_def A_def A'_def renaming_valid_def
    by (rule Simple_Network_Rename_Formula.models_iff'[symmetric])
  note [sep_heap_rules] =
    certificate_check[
    of state_space
    "map renum_acts broadcast" "map (\<lambda>(a,b,c). (renum_vars a, b, c)) bounds"
    "map_index (renum_automaton renum_acts renum_vars renum_clocks renum_states) automata"
    m num_states num_actions k "map_index renum_states L\<^sub>0" "map (\<lambda>(x, v). (renum_vars x, v)) s\<^sub>0"
    "map_formula renum_states renum_vars id formula",
    folded A'_def check'_def renaming_valid_def,
    simplified
    ]
  show ?thesis
    unfolding rename_check_def do_rename_mc_def rename_network_def
    unfolding if_False
    unfolding Simple_Network_Rename_Formula_String_Defs.check_renaming[symmetric] * Let_def
    unfolding
      A_def[symmetric] check_def[symmetric] renaming_valid_def[symmetric]
    by (sep_auto simp: split: bool.splits)
qed

lemmas [code] = Simple_Network_Impl_nat_defs.states_i_def

export_code rename_check in SML module_name Test

end