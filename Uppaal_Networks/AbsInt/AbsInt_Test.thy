theory AbsInt_Test
  imports
    "HOL.String"
    AbsInt_Refine
    Uppaal_Networks.UPPAAL_Asm_Show
    Word_Set
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

instantiation smart_base :: ("show", "show") "show"
begin
fun show_smart_base :: "('a, 'b) smart_base \<Rightarrow> string" where
  "show_smart_base (Smart stack regs flag) = undefined"
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

instantiation int_set_base :: "show"
begin
fun show_int_set_base :: "int_set_base \<Rightarrow> string" where
  "show_int_set_base (IntSet s) = show s"
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

definition "set_entry \<equiv> merge_single \<bottom> 0 (Some (Smart \<bottom> \<bottom> BFalse))"
definition "set_result \<equiv> word_set_loop (fetch_op myprog) 3 set_entry"
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