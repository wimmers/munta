theory Export_Checker
  imports UPPAAL_State_Networks_Impl_Refine UPPAAL_State_Networks_Impl_Refine_Calc
begin

code_printing constant Array.new' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/
(IntInf.toInt _,/ (_)))"
code_printing constant Array.make' \<rightharpoonup> (SML) "(fn/ ()/ =>/
Array.tabulate/ (IntInf.toInt _,/ _ o IntInf.fromInt))"
code_printing constant Array.len' \<rightharpoonup> (SML) "(fn/ ()/ =>/ IntInf.fromInt
(Array.length/ _))"
code_printing constant Array.nth' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/
((_),/ IntInf.toInt _))"
code_printing constant Array.upd' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/
((_),/ IntInf.toInt _,/ (_)))"


code_printing
  type_constructor array \<rightharpoonup> (SML) "_/ FArray.IsabelleMapping.ArrayType"
| constant Array \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_of'_list"
| constant new_array' \<rightharpoonup> (SML) "(fn a => FArray.IsabelleMapping.new'_array a o IntInf.toInt)"
| constant array_length' \<rightharpoonup> (SML) "IntInf.fromInt o FArray.IsabelleMapping.array'_length"
| constant array_get' \<rightharpoonup> (SML) "(fn a => FArray.IsabelleMapping.array'_get a o IntInf.toInt)"
| constant array_set' \<rightharpoonup> (SML) "(fn a => FArray.IsabelleMapping.array'_set a o IntInf.toInt)"
| constant array_grow' \<rightharpoonup> (SML) "(fn a => FArray.IsabelleMapping.array'_grow a o IntInf.toInt)"
| constant array_shrink' \<rightharpoonup> (SML) "(fn a => FArray.IsabelleMapping.array'_shrink a o IntInf.toInt)"
| constant array_of_list \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_of'_list"
| constant array_get_oo' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_get'_oo"
| constant array_set_oo' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_set'_oo"

(* XXX Add this fix to IArray theory *)
code_printing
  constant IArray.sub' \<rightharpoonup> (SML) "(Vector.sub o (fn (a, b) => (a, IntInf.toInt b)))"

code_printing code_module "array_blit" \<rightharpoonup> (SML)
\<open>
fun array_blit src si dst di len = (
    src=dst andalso raise Fail ("array_blit: Same arrays");
    ArraySlice.copy {
      di = IntInf.toInt di,
      src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
      dst = dst})

  fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
  fun array_upd_oo f i x a () =
    (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()
\<close>

(*
code_printing
  constant List.gen_length \<rightharpoonup> (SML) "(fn n => fn xs => nat_of_integer (length xs + integer_of_nat n))"
*)

thm UPPAAL_Reachability_Problem_precompiled_def

(* For debugging purposes only *)
definition
  "bounded_int bounds (s :: int list) \<equiv>
   length s = length bounds \<and> (\<forall> i < length s. fst (bounds ! i) < s ! i \<and> s ! i < snd (bounds ! i))"

export_code
  check_and_verify init_pred_check time_indep_check1 time_indep_check2 conjunction_check2
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
  in SML_imp module_name Reachability_Checker
  file "ML/UPPAAL_Reachability_Checker.ml"

ML_file_debug "ML/UPPAAL_Reachability_Checker.ml"

ML \<open>
  open Reachability_Checker;;
\<close>

end (* End of Theory *)