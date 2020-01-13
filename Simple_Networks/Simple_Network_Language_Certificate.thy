theory Simple_Network_Language_Certificate
  imports "../Extract_Certificate" TA_Code.Simple_Network_Language_Model_Checking
begin

context Simple_Network_Impl_nat_ceiling_start_state
begin

definition
  "state_space \<equiv>
  let
    succsi = impl.succs_impl;
    a\<^sub>0i = impl.a\<^sub>0_impl;
    Fi = impl.F_impl;
    Lei = impl.subsumes_impl;
    emptyi = impl.emptiness_check_impl;
    keyi = return o fst;
    copyi = impl.state_copy_impl;
    trace = impl.tracei
  in extract_certificate_impl succsi a\<^sub>0i Fi Lei emptyi keyi copyi trace"

schematic_goal state_space_alt_def:
  "state_space \<equiv> ?impl"
  unfolding state_space_def
  unfolding succs_impl_alt_def
  unfolding k_impl_alt_def k_i_def
  (* The following are just to unfold things that should have been defined in a defs locale *)
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

end (* Simple_Network_Impl_nat_ceiling_start_state *)

concrete_definition state_space
  uses Simple_Network_Impl_nat_ceiling_start_state.state_space_alt_def

end