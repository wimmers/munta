theory Deadlock_Checking
  imports Deadlock_Impl UPPAAL_Model_Checking
begin

context UPPAAL_Reachability_Problem_precompiled'
begin

text \<open>
  \<^item> @{term equiv.defs.states'}
  \<^item> @{term EA} is @{term equiv.state_ta},
    the state automaton constructed from UPPAAL network (\<open>equiv\<close>/\<open>N\<close>)
  \<^item> @{term A} is @{term equiv.defs.prod_ta},
    the product automaton constructed from UPPAAL network (\<open>equiv\<close>/\<open>N\<close>)
\<close>

context
  fixes \<phi>
  assumes formula_is_false: "formula = formula.EX (and \<phi> (not \<phi>))"
begin

lemma F_is_FalseI:
  shows "PR_CONST (\<lambda>(x, y). F x y) = (\<lambda>_. False)"
  unfolding F_def by (subst formula_is_false) auto

lemma final_fun_is_False:
  "final_fun a = False"
  unfolding final_fun_def by (subst formula_is_false) auto

lemmas deadlock_checker_hoare = impl.deadlock_checker_hoare[
    OF final_fun_is_False F_is_FalseI, folded deadlock_start_iff has_deadlock_def]

end

schematic_goal deadlock_checker_alt_def:
  "impl.deadlock_checker \<equiv> ?impl"
  unfolding impl.deadlock_checker_def impl.succs_impl_def
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def unbounded_dbm_def
  unfolding k_impl_alt_def
  unfolding impl.check_deadlock_neg_impl_def impl.check_deadlock_impl_def
  unfolding impl.is_start_in_states_impl_def
  apply (tactic \<open>pull_tac @{term k_i} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>) (* XXX This is not pulling anything *)
  apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

schematic_goal deadlock_checker_alt_def_refined:
  "impl.deadlock_checker \<equiv> ?impl"
  unfolding deadlock_checker_alt_def
  unfolding fw_impl'_int
  unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def
  unfolding trans_i_from_impl
  unfolding runf_impl runt_impl check_g_impl pairs_by_action_impl check_pred_impl
  apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray bounds"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PF} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PT} @{context}\<close>)
  unfolding PF_alt_def PT_alt_def
  apply (tactic \<open>pull_tac @{term PROG'} @{context}\<close>)
  unfolding PROG'_def
  apply (tactic \<open>pull_tac @{term "length prog"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stripf) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stript) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray prog"} @{context}\<close>)
  unfolding all_actions_by_state_impl
  apply (tactic \<open>pull_tac @{term "[0..<p]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<na]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "{0..<p}"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<m+1]"} @{context}\<close>)
  by (rule Pure.reflexive)

end

concrete_definition deadlock_checker uses
  UPPAAL_Reachability_Problem_precompiled'.deadlock_checker_alt_def_refined

definition
  "precond_dc
    num_processes num_clocks clock_ceiling max_steps I T prog bounds program s\<^sub>0 num_actions
  \<equiv>
    if UPPAAL_Reachability_Problem_precompiled'
      num_processes num_clocks max_steps I T prog bounds program s\<^sub>0 num_actions clock_ceiling
    then
      deadlock_checker
        num_processes num_clocks max_steps I T prog bounds program s\<^sub>0 num_actions clock_ceiling
      \<bind> (\<lambda>x. return (Some x))
    else return None"

theorem deadlock_check:
  "<emp>
      precond_dc p m k max_steps I T prog bounds P s\<^sub>0 na
   <\<lambda> Some r \<Rightarrow> \<up>(
       UPPAAL_Reachability_Problem_precompiled' p m max_steps I T prog bounds P s\<^sub>0 na k \<and>
       r = has_deadlock (conv (N p I P T prog bounds)) max_steps (repeat 0 p, s\<^sub>0, \<lambda>_ . 0))
    | None \<Rightarrow> \<up>(\<not> UPPAAL_Reachability_Problem_precompiled' p m max_steps I T prog bounds P s\<^sub>0 na k)
   >\<^sub>t"
proof -
  define A where "A \<equiv> conv (N p I P T prog bounds)"
  note [sep_heap_rules] = UPPAAL_Reachability_Problem_precompiled'.deadlock_checker_hoare[
      OF _ HOL.refl,
      of p m max_steps I T prog bounds P s\<^sub>0 na k,
      unfolded UPPAAL_Reachability_Problem_precompiled_defs.init_def,
      folded A_def
      ]
  show ?thesis
    unfolding A_def[symmetric] precond_dc_def
    by (sep_auto simp:
        deadlock_checker.refine[symmetric] UPPAAL_Reachability_Problem_precompiled_defs.init_def 
        mod_star_conv)
qed

export_code precond_dc checking SML

end