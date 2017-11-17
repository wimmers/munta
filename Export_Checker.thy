theory Export_Checker
  imports UPPAAL_Model_Checking UPPAAL_State_Networks_Impl_Refine_Calc
begin

(* XXX Add this fix to IArray theory *)
code_printing
  constant IArray.sub' \<rightharpoonup> (SML) "(Vector.sub o (fn (a, b) => (a, IntInf.toInt b)))"

(* For debugging purposes only *)
definition
  "bounded_int bounds (s :: int list) \<equiv>
   length s = length bounds \<and> (\<forall> i < length s. fst (bounds ! i) < s ! i \<and> s ! i < snd (bounds ! i))"

export_code
  precond_mc Pure.type init_pred_check time_indep_check1 time_indep_check2 conjunction_check2
  LT LE EQ GE GT integer_of_nat nat_of_integer int_of_integer integer_of_int
  In INSTR loc
  UPPAAL_Reachability_Problem_precompiled_defs.check_pre
  map_option
  UPPAAL_Reachability_Problem_precompiled_start_state
  UPPAAL_Reachability_Problem_precompiled
  UPPAAL_Reachability_Problem_precompiled_start_state_axioms
  UPPAAL_Reachability_Problem_precompiled_defs.check_ceiling
  bounded_int
  nat
  REACHABLE UNREACHABLE INIT_INV_ERR
  UPPAAL_Reachability_Problem_precompiled_defs.k
  formula.EX
  in SML module_name Model_Checker
  file "ML/UPPAAL_Model_Checker.sml"

ML_file_debug "ML/UPPAAL_Model_Checker.sml"

ML \<open>
  open Model_Checker;;
\<close>

end (* End of Theory *)