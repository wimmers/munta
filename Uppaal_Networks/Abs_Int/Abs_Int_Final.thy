theory Abs_Int_Final
  imports
    Abs_Int_Refine
    State_Smart
    Stack_Window
    Abs_Word_Strided_Interval
    Abs_Int_C
begin

type_synonym si_state = "(strided_interval toption option, strided_interval toption option stack_window) smart"

definition[simp]: "\<gamma>_word \<equiv> \<gamma>_option (\<gamma>_toption \<gamma>_strided_interval)"

global_interpretation Abs_Int_Final: Smart_Base
  where \<gamma>_word = "\<gamma>_word"
    and contains = "option_contains (toption_contains strided_interval_contains)"
    and make = "Some \<circ> Minor \<circ> strided_interval_make"
    and concretize = "option_concretize (toption_concretize (strided_interval_concretize concretize_max))"
    and aplus = "option_aplus (toption_aplus strided_interval_aplus)"
    and lt = "option_lift_bool (toption_lift_bool strided_interval_lt)"
    and le = "option_lift_bool (toption_lift_bool strided_interval_le)"
    and eq = "option_lift_bool (toption_lift_bool strided_interval_eq)"
    and \<gamma>_stack = "\<gamma>_stack_window window_size \<gamma>_word"
    and push = "push_stack_window window_size"
    and pop = "pop_stack_window window_size"
  for window_size :: nat
  and concretize_max :: nat
  defines "final_step_base" = "Abs_Int_Final.step_smart_base"
    and "final_step" = "Abs_Int_Final.step_smart"
    and "final_astore_singleton" = "Abs_Int_Final.astore_singleton"
    and "final_astore_multi" = "Abs_Int_Final.astore_multi"
    and "final_astore" = "Abs_Int_Final.astore"
    and "final_load" = "Abs_Int_Final.load"
    and "final_cmp_op" = "Abs_Int_Final.cmp_op"
    and "final_pop2" = "Abs_Int_Final.pop2"
    and "final_pop2_push" = "Abs_Int_Final.pop2_push"
    and "final_word_of" = "Abs_Int_Final.word_of"
    and "final_\<gamma>" = "Abs_Int_Final.\<gamma>_smart"
    and "final_\<gamma>_regs" = "Abs_Int_Final.\<gamma>_regs"
    and "final_loopc'" = "Abs_Int_Final.Smart_C.ai_loopc"
proof(standard, goal_cases)
  case (1 a b) then show ?case by (simp add: Word_Strided_Interval.mono_gamma) next
  case (3 a x) then show ?case by (simp add: Word_Strided_Interval.contains_correct) next
  case (5 a vs) then show ?case by (simp add: Word_Strided_Interval.concretize_correct) next
  case (6 a vs) then show ?case by (rule Word_Strided_Interval.concretize_finite) next
  case (7 x a y b) then show ?case by (simp add: Word_Strided_Interval.plus_correct) next
  case (8 a b) then show ?case using Word_Strided_Interval.lt_correct \<gamma>_word_def by presburger next
  case (9 a b) then show ?case using Word_Strided_Interval.le_correct \<gamma>_word_def by presburger next
  case (10 a b) then show ?case using Word_Strided_Interval.eq_correct \<gamma>_word_def by presburger next
  case (11 a b) then show ?case by (simp add: window_mono_gamma_stack Word_Strided_Interval.mono_gamma) next
  case (13 c b cx x) then show ?case by (simp add: Word_Strided_Interval.mono_gamma window_push_correct) next
  case (14 cx c b) then show ?case by (simp add: Word_Strided_Interval.mono_gamma window_pop_correct(1)) next
  case (15 cx c b) then show ?case by (simp add: Word_Strided_Interval.mono_gamma window_pop_correct(2))
qed auto

definition[simp]: "final_loop window_size concretize_max \<equiv> finite_loop (final_step window_size concretize_max)"
theorem ai_loop_correct: "collect_loop prog n (Abs_Int_Final.Smart.\<gamma>_map window_size entry)
  \<le> Abs_Int_Final.Smart.\<gamma>_map window_size (final_loop window_size concretize_max prog n entry)"
  using Abs_Int_Final.Smart.ai_loop_correct by simp

definition[simp]: "final_loop_fp window_size concretize_max \<equiv> finite_loop_fp (final_step window_size concretize_max)"
theorem ai_loop_fp_correct: "collect_loop prog m (Abs_Int_Final.Smart.\<gamma>_map window_size entry)
  \<le> Abs_Int_Final.Smart.\<gamma>_map window_size (final_loop_fp window_size concretize_max prog n entry)"
  using Abs_Int_Final.Smart.ai_loop_fp_correct by simp

definition[simp]: "final_loopc window_size concretize_max cprog \<equiv>
      finite_loop (astep_liftc (final_step window_size concretize_max) smart_kill_flag cprog) (extract_prog cprog)"
theorem final_loop_stepsc:
  assumes
    "stepsc cprog (Suc n) u (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> final_\<gamma> window_size entry"
  shows "(st', s', f', rs') \<in> final_\<gamma> window_size (lookup (final_loopc window_size concretize_max cprog n (single pc entry)) pc')"
  using assms by (metis Abs_Int_Final.Smart_C.ai_loopc_def Abs_Int_Final.Smart_C.ai_stepsc_single final_loopc_def)

theorem final_loop_stepsc_pc:
  assumes
    "stepsc cprog (Suc n) u (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> final_\<gamma> window_size entry"
  shows "pc' \<in> domain (final_loopc window_size concretize_max cprog n (single pc entry))"
  using assms
  by (metis Abs_Int_Final.Smart_C.ai_loopc_def Abs_Int_Final.Smart_C.ai_stepsc_pc UPPAAL_Asm_Map.single_lookup final_loopc_def)

lemmas final_loop_steps_pc = Abs_Int_Final.Smart.ai_steps_pc

definition "final_top_equivalent window_size =
  Some (Smart (stack_window_top_equivalent window_size) \<top> \<top>)"

lemma final_top_equivalent:
  "final_\<gamma> n (final_top_equivalent n) = \<top>"
proof -
  have "final_\<gamma> n (final_top_equivalent n) =
    {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack_window n \<gamma>_word (stack_window_top_equivalent n) \<and> rstate \<in> final_\<gamma>_regs \<top> \<and> flag \<in> \<gamma>_power_bool \<top>}"
    unfolding final_top_equivalent_def by simp
  also have "\<dots> = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack_window n \<gamma>_word (stack_window_top_equivalent n)}" by simp
  also have "\<dots> = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack_window n \<gamma>_word \<top>}" by (simp add: stack_window_top_equivalent)
  finally show ?thesis by auto
qed

definition "final_reg_bounded_top_equivalent window_size reg_bound =
  Some (Smart (stack_window_top_equivalent window_size) (regs_bounded_top reg_bound) \<top>)"

lemma final_reg_bounded_top_equivalent:
  "final_\<gamma> n (final_reg_bounded_top_equivalent n reg_bound) = {(stack, rstate, flag, nl). length rstate \<le> reg_bound}"
proof -
  have "final_\<gamma> n (final_reg_bounded_top_equivalent n reg_bound) =
    {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack_window n \<gamma>_word (stack_window_top_equivalent n)
      \<and> rstate \<in> final_\<gamma>_regs (regs_bounded_top reg_bound)
      \<and> flag \<in> \<gamma>_power_bool \<top>}"
    unfolding final_reg_bounded_top_equivalent_def by simp
  also have "\<dots> = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack_window n \<gamma>_word (stack_window_top_equivalent n)
      \<and> rstate \<in> final_\<gamma>_regs (regs_bounded_top reg_bound)}" by simp
  also have "\<dots> = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack_window n \<gamma>_word \<top>
    \<and> rstate \<in> final_\<gamma>_regs (regs_bounded_top reg_bound)}" by (simp add: stack_window_top_equivalent)
  also have "\<dots> = {(stack, rstate, flag, nl). rstate \<in> final_\<gamma>_regs (regs_bounded_top reg_bound)}" by simp
  also have "\<dots> = {(stack, rstate, flag, nl). length rstate \<le> reg_bound}"
  proof -
    have "length rstate \<le> reg_bound \<Longrightarrow> rstate \<in> final_\<gamma>_regs (regs_bounded_top reg_bound)"
      for rstate by (simp add: regs_bounded_top)
    moreover have "rstate \<in> final_\<gamma>_regs (regs_bounded_top reg_bound) \<Longrightarrow> length rstate \<le> reg_bound"
      for rstate by (simp add: regs_bounded_top_bounded)
    ultimately show ?thesis by blast
  qed
  finally show ?thesis by auto
qed


export_code final_loop_fp in SML module_name AbsInt_Final

end