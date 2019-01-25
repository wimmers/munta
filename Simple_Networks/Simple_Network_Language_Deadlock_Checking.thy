theory Simple_Network_Language_Deadlock_Checking
  imports Simple_Network_Language_Model_Checking "../Deadlock_Checking"
begin

context Simple_Network_Impl_nat_ceiling_start_state
begin

context
  fixes \<phi>
  assumes formula_is_false: "formula = formula.EX (not sexp.true)"
begin

lemma F_is_FalseI:
  shows "PR_CONST F = (\<lambda>_. False)"
  by (subst formula_is_false) auto

lemma final_fun_is_False:
  "Fi a = False"
  by (subst formula_is_false) auto

lemmas deadlock_checker_hoare = impl.deadlock_checker_hoare[
    OF final_fun_is_False F_is_FalseI, folded deadlock_start_iff has_deadlock_def]

end

thm impl.is_start_in_states_impl_def
schematic_goal deadlock_checker_alt_def:
  "impl.deadlock_checker \<equiv> ?impl"
  unfolding impl.deadlock_checker_def
  unfolding impl.succs_impl_def
  unfolding impl.check_deadlock_neg_impl_def impl.check_deadlock_impl_def
  apply (abstract_let impl.is_start_in_states_impl is_start)
  unfolding impl.is_start_in_states_impl_def
  apply (abstract_let impl.E_op''_impl E_op''_impl)
  unfolding impl.E_op''_impl_def fw_impl'_int
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
  unfolding k_impl_alt_def
  apply (abstract_let k_i k_i) (* Could be killed *)
  apply (abstract_let n_ps n_ps)
  (* These would need to be moved to a defs locale *)
  unfolding k_i_def impl.state_copy_impl_def impl.a\<^sub>0_impl_def impl.abstr_repair_impl_def
    impl.subsumes_impl_def impl.emptiness_check_impl_def impl.abstra_repair_impl_def
    impl.init_dbm_impl_def
  by (rule Pure.reflexive)

end

concrete_definition deadlock_checker uses
  Simple_Network_Impl_nat_ceiling_start_state.deadlock_checker_alt_def

definition precond_dc where
  "precond_dc
    show_clock show_state broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula \<equiv>
    if Simple_Network_Impl_nat_ceiling_start_state
      broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 formula
    then
      deadlock_checker
        broadcast bounds' automata m num_states num_actions k L\<^sub>0 s\<^sub>0 show_clock show_state
      \<bind> (\<lambda> x. return (Some x))
    else return None"

theorem deadlock_check:
  "<emp> precond_dc
    show_clock show_state broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0
      (formula.EX (not sexp.true))
    <\<lambda> Some r \<Rightarrow> \<up>(
        Simple_Network_Impl_nat_ceiling_start_state
          broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 (formula.EX (not sexp.true)) \<and>
          r = has_deadlock (N broadcast automata bounds) (L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0)
        )
     | None \<Rightarrow> \<up>(\<not> Simple_Network_Impl_nat_ceiling_start_state
        broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 (formula.EX (not sexp.true)))
    >\<^sub>t"
proof -
  define A where "A \<equiv> N broadcast automata bounds"
  define check where "check \<equiv> A,(L\<^sub>0, map_of s\<^sub>0, \<lambda>_ . 0) \<Turnstile> (formula.EX (not sexp.true))"
  note [sep_heap_rules] = Simple_Network_Impl_nat_ceiling_start_state.deadlock_checker_hoare[
      OF _ HOL.refl,
      of broadcast bounds automata m num_states num_actions k L\<^sub>0 s\<^sub>0 _,
      unfolded UPPAAL_Reachability_Problem_precompiled_defs.init_def,
      folded A_def
      ]
  show ?thesis
    unfolding A_def[symmetric] precond_dc_def
    by (sep_auto simp: deadlock_checker.refine[symmetric] pure_def has_deadlock_def)
qed

end