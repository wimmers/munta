theory AbsInt_Final
  imports
    AbsInt_Refine
    State_Smart
    Stack_Window
    Word_StridedInterval
begin

definition "n \<equiv> 16"

definition[simp]: "\<gamma>_word \<equiv> \<gamma>_option (\<gamma>_toption \<gamma>_strided_interval)"

global_interpretation Abs_Int_Final: Smart_Base
  where \<gamma>_word = "\<gamma>_word"
    and contains = "option_contains (toption_contains strided_interval_contains)"
    and make = "Some \<circ> Minor \<circ> strided_interval_make"
    and concretize = "option_concretize (toption_concretize strided_interval_concretize)"
    and aplus = "option_aplus (toption_aplus strided_interval_aplus)"
    and lt = "option_lift_bool (toption_lift_bool strided_interval_lt)"
    and le = "option_lift_bool (toption_lift_bool strided_interval_le)"
    and eq = "option_lift_bool (toption_lift_bool strided_interval_eq)"
    and \<gamma>_stack = "\<gamma>_stack_window n \<gamma>_word"
    and push = "push_stack_window n"
    and pop = "pop_stack_window n"
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

definition[simp]: "final_loop_fp \<equiv> finite_loop_fp final_step"
theorem ai_loop_fp_correct: "collect_loop prog m (Abs_Int_Final.Smart.\<gamma>_map entry) \<le> Abs_Int_Final.Smart.\<gamma>_map (final_loop_fp prog n entry)"
  using Abs_Int_Final.Smart.ai_loop_fp_correct by simp

export_code final_loop_fp in SML module_name AbsInt_Final

end