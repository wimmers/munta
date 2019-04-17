theory Deadlock_Checking
  imports Deadlock_Impl TA_Byte_Code.UPPAAL_Model_Checking
begin

paragraph \<open>Standard Deadlock Checker Implementation\<close>
context Reachability_Problem_Impl
begin

definition deadlock_checker where
  "deadlock_checker \<equiv>
    let
      key = return \<circ> fst;
      sub = subsumes_impl;
      copy = state_copy_impl;
      start = a\<^sub>0_impl;
      final = (\<lambda>_. return False);
      succs = succs_impl;
      empty = emptiness_check_impl;
      P = check_deadlock_neg_impl;
      trace = tracei
    in do {
      r1 \<leftarrow> is_start_in_states_impl;
      if r1 then do {
        r2 \<leftarrow> check_passed_impl succs start final sub empty key copy trace P;
        return r2
      }
      else return True
    }
    "

interpretation ta_bisim: Bisimulation_Invariant
  "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(l, u) (l', u'). l' = l \<and> (\<forall> c. c \<in> clk_set (conv_A A) \<longrightarrow> u c = u' c))"
  "(\<lambda>_. True)" "(\<lambda>_. True)"
  by (rule ta_bisimulation[of "conv_A A"])

lemma deadlock_zero_clock_val_iff:
  "(\<exists>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<and> deadlock (l\<^sub>0, u\<^sub>0)) \<longleftrightarrow> deadlock (l\<^sub>0, \<lambda>_. 0)"
  apply safe
  subgoal for u
    using clocks_I[of "\<lambda>_. 0" u] by (subst ta_bisim.deadlock_iff; simp)
  by auto

context
  assumes F_fun_False: "\<And>x. F_fun x = False" and F_False: "F = (\<lambda>_. False)"
begin
lemma F_impl_is_False:
  "F_impl = (\<lambda>_. return False)"
  unfolding F_impl_def F_fun_False by simp

lemma deadlock_checker_correct:
  "(uncurry0 deadlock_checker, uncurry0 (Refine_Basic.RETURN (deadlock (l\<^sub>0, \<lambda>_. 0))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  unfolding
    deadlock_checker_def Let_def F_impl_is_False[symmetric]
    check_passed_impl_start_def[symmetric] deadlock_zero_clock_val_iff[symmetric]
  using check_passed_impl_start_hnr[OF F_False] .

lemmas deadlock_checker_hoare = deadlock_checker_correct[to_hnr, unfolded hn_refine_def, simplified]

end

end


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
  apply (abstract_let k_i ceiling)
  apply (abstract_let "inv_fun :: (_ \<times> int list \<Rightarrow> _)" inv)
  apply (abstract_let "trans_fun" trans)
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
  apply (abstract_let "IArray (map IArray inv)" inv_array)
  apply (abstract_let "IArray (map IArray trans_out_map)" trans_out)
  apply (abstract_let "IArray (map IArray trans_in_map)" trans_in)
  apply (abstract_let "IArray (map IArray trans_i_map)" trans_internal)
  apply (abstract_let "IArray bounds" bounds_array)
  apply (abstract_let PF PF)
  apply (abstract_let PT PT)
  unfolding PF_alt_def PT_alt_def
  apply (abstract_let PROG' PROG')
  unfolding PROG'_def
  apply (abstract_let "length prog" len_prog)
  apply (abstract_let "IArray (map (map_option stripf) prog)" prog_f)
  apply (abstract_let "IArray (map (map_option stript) prog)" prog_t)
  apply (abstract_let "IArray prog" prog_array)
  unfolding all_actions_by_state_impl
  apply (abstract_let "[0..<p]" p_ran)
  apply (abstract_let "[0..<na]" num_actions_ran)
  apply (abstract_let "{0..<p}" num_processes_ran)
  apply (abstract_let "[0..<m+1]" num_clocks_ran)
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
        mod_star_conv has_deadlock_def)
qed

export_code precond_dc checking SML

end