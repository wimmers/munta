theory AbsInt_Test
  imports
    "HOL.String"
    Uppaal_Networks.UPPAAL_Asm_Show
    AbsInt_Final
begin

instantiation toption :: ("show") "show"
begin
fun show_toption :: "'a toption \<Rightarrow> string" where
  "show_toption Top = ''Top''" |
  "show_toption (Minor x) = ''Minor '' @ show x"
instance ..
end

instantiation dumb_base :: "show"
begin
fun show_dumb_base :: "dumb_base \<Rightarrow> string" where
  "show_dumb_base Any = ''Any''"
instance ..
end

instantiation power_bool :: "show"
begin
fun show_power_bool :: "power_bool \<Rightarrow> string" where
  "show_power_bool BTrue = ''BTrue''" |
  "show_power_bool BFalse = ''BFalse''" |
  "show_power_bool BBoth = ''BBoth''"
instance ..
end

instantiation smart_base :: ("show", "show") "show"
begin
fun show_smart_base :: "('a, 'b) smart_base \<Rightarrow> string" where
  "show_smart_base (Smart stack regs flag) = ''Smart '' @ show stack @ '' '' @ show regs @ '' '' @ show flag"
instance ..
end

(* Ugly hack for visualizing sets: *)
fun to_list :: "'a set \<Rightarrow> 'a list" where
  "to_list _ = undefined"
lemma[code]: "to_list (set as) = as" sorry
instantiation set :: ("show") "show"
begin
fun show_set :: "'a set \<Rightarrow> string" where
  "show_set s =
    (let stuff = map show (fold (#) [] (to_list s)) in
    intercalate ''; '' stuff)"
instance proof qed
end

instantiation strided_interval :: "show"
begin
fun show_strided_interval :: "strided_interval \<Rightarrow> string" where
  "show_strided_interval i = show (stride i) @ ''['' @ show (lower i) @ ''-'' @ show (upper i) @ '']''"
instance ..
end

definition "myprog_listing \<equiv> [
PUSH 42,
PUSH 3,
instr.LT,
JMPZ 7,
HALT,
PUSH 13,
PUSH 37,
PUSH 123,
HALT
]"

definition "myprog \<equiv> assemble myprog_listing"

definition "dumb_entry \<equiv> merge_single (\<bottom>::dumb state_map) 0 (Some Any)"
definition "dumb_stepped \<equiv>
  finite_step_map step_dumb (fetch_op myprog) dumb_entry"
value "lookup (dump_stepped::dumb state_map) 0"
definition "dumb_advanced \<equiv>
  finite_advance step_dumb (fetch_op myprog) dumb_entry"
definition "dumb_result \<equiv>
  dumb_loop (fetch_op myprog) 100 dumb_entry"
definition "abs_res_str \<equiv> String.implode (show (DisplayCtx myprog dumb_result))"
(*ML \<open>val _ = writeln (@{code abs_res_str})\<close>*)

type_synonym si_state = "(strided_interval toption option, strided_interval toption option stack_window) smart state_map"

definition "set_entry \<equiv> (merge_single \<bottom> 0 (Some (Smart \<bottom> \<bottom> BFalse)))::si_state"
definition "set_result \<equiv> final_loop_fp (fetch_op myprog) 100 set_entry"
definition "set_res_str \<equiv> String.implode (show (DisplayCtx myprog set_result))"
ML \<open>val _ = writeln (@{code set_res_str})\<close>



(*definition "empty_state \<equiv> ([], [], False, [])"
definition "empty_state1 \<equiv> ([], [], True, [])"
definition "(collect_result::collect_state set state_map) \<equiv>
  let prog = fetch_op myprog;
      entry = deepen {(0::addr, empty_state), (0, empty_state1)} in
  collect_loop prog 4 entry"
definition "my_string \<equiv> String.implode (show (DisplayCtx mysprog collect_result))"
ML \<open>val _ = writeln (@{code my_string})\<close>*)
end