theory AbsInt_Test
  imports AbsInt_Refine "HOL-IMP.AExp" "HOL.String"
begin

definition myprog :: "instr list" where "myprog \<equiv> [
PUSH 42,
PUSH 3,
instr.LT,
HALT
]"

fun assemble :: "instr list \<Rightarrow> spaced_program" where
  "assemble listing = SpacedProgram
    (set (upt 0 (length listing)))
    (\<lambda>pc. if pc < length listing then Some (listing ! pc) else None)"

class "show" =
  fixes "show" :: "'a \<Rightarrow> string"

fun hexlit :: "nat \<Rightarrow> nat \<Rightarrow> string" where
  "hexlit 0 0 = ''0x''" |
  "hexlit len v =
    (let c = v mod 16 in
    hexlit (len-1) (v div 16) @ [char_of (if c < 10 then 48 + c else 97 + (c - 10))])"

fun hexliti :: "nat \<Rightarrow> int \<Rightarrow> string" where
  "hexliti len v = hexlit len (if v < 0 then nat (-v) else nat v)"

instantiation nat :: "show"
begin
fun show_nat :: "nat \<Rightarrow> string" where
  "show_nat n = hexlit 4 n"
instance proof qed
end

instantiation int :: "show"
begin
fun show_int :: "int \<Rightarrow> string" where
  "show_int n = hexliti 1 n"
instance proof qed
end

instantiation bool :: "show"
begin
fun show_bool :: "bool \<Rightarrow> string" where
  "show_bool True = ''True''" |
  "show_bool False = ''False''"
instance proof qed
end

instantiation instr :: "show"
begin
fun show_instr :: "instr \<Rightarrow> string" where
  "show_instr (JMPZ a) = ''JMPZ '' @ (show a)" |
  "show_instr ADD = ''ADD''" |
  "show_instr NOT = ''NOT''" |
  "show_instr AND = ''AND''" |
  "show_instr instr.LT = ''LT''" |
  "show_instr instr.LE = ''LE''" |
  "show_instr instr.EQ = ''EQ''" |
  "show_instr (PUSH imm) = ''PUSH '' @ (show imm)" |
  "show_instr POP = ''POP''" |
  "show_instr (LID r) = ''LID '' @ (show r)"|
  "show_instr STORE = ''STORE''" |
  "show_instr (STOREI r imm) = ''STOREI '' @ (show r) @ '' '' @ (show imm)"|
  "show_instr COPY = ''COPY''" |
  "show_instr CALL = ''CALL''" |
  "show_instr RETURN = ''RETURN''" |
  "show_instr HALT = ''HALT''" |
  "show_instr (STOREC n i) = ''STOREC '' @ (show n) @ '' '' @ (show i)" |
  "show_instr (SETF b) = ''SETF '' @ (show b)"
instance ..
end

instantiation prod :: ("show", "show") "show"
begin
fun show_prod :: "('a * 'b) \<Rightarrow> string" where
  "show_prod (a, b) = CHR ''('' # show a @ '', '' @ show b @ '')''"
instance ..
end

instantiation list :: ("show") "show"
begin
fun show_list_rest :: "'a list \<Rightarrow> string" where
  "show_list_rest [] = '']''" |
  "show_list_rest (x # xs) = show x @ '', '' @ show_list_rest xs"

fun show_list :: "'a list \<Rightarrow> string" where
  "show_list [] = ''[]''" |
  "show_list xs = show_list_rest xs"
instance ..
end

instantiation option :: ("show") "show"
begin
fun show_option :: "'a option \<Rightarrow> string" where
  "show_option None = ''None''" |
  "show_option (Some x) = ''Some '' @ show x"
instance ..
end

instantiation dumb_base :: "show"
begin
fun show_dumb_base :: "dumb_base \<Rightarrow> string" where
  "show_dumb_base Any = ''Any''"
instance ..
end

abbreviation init where "init \<equiv> (0, [], [], False, [])"
value "case assemble myprog of (SpacedProgram space prog) \<Rightarrow> step (the (prog (state_pc init))) init"

instantiation spaced_program :: "show"
begin
fun show_spaced_program :: "spaced_program \<Rightarrow> string" where
  "show_spaced_program (SpacedProgram space prog) =
    concat (map (\<lambda>pc. (show pc) @ '' '' @ (show (the (prog pc))) @ [char_of (10::nat)]) (sorted_list_of_set space))"
instance proof qed
end

definition "asm_width \<equiv> 20"
datatype 'a dispctx = DisplayCtx spaced_program "'a state_map"

definition "emoji \<equiv> map char_of ([240,159,164,183] :: nat list)"

fun intercalate:: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "intercalate _ [] = []" |
  "intercalate _ [x] = x" |
  "intercalate sep (x # xs) = x @ sep @ intercalate sep xs"

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

fun format_ctx_line :: "nat \<Rightarrow> addr \<Rightarrow> program \<Rightarrow> ('a::show) state_map \<Rightarrow> string" where
  "format_ctx_line len pc prog ctx =
      (let asm = (show pc) @ '' '' @ (show (the (prog pc)));
           padding = replicate ((asm_width - 1) - length asm + 1) CHR '' '';
           states = show (lookup ctx pc) in
      asm @ padding @ states @ ''\<newline>'')"

instantiation dispctx :: ("show") "show"
begin
fun show_dispctx :: "'a dispctx \<Rightarrow> string" where
  "show_dispctx (DisplayCtx (SpacedProgram space prog) st) =
    concat (map (\<lambda>pc. format_ctx_line asm_width pc prog st) (sorted_list_of_set space))"
instance proof qed
end

definition "mysprog \<equiv> assemble myprog"

fun spprog :: "spaced_program \<Rightarrow> program" where
  "spprog (SpacedProgram _ prog) = prog"

definition "empty_state \<equiv> ([], [], False, [])"
definition "empty_state1 \<equiv> ([], [], True, [])"

definition "(collect_result::collect_state set state_map) \<equiv>
  let prog = spprog mysprog;
      entry = deepen {(0::addr, empty_state), (0, empty_state1)} in
  collect_loop prog 4 entry"

definition "my_string \<equiv> String.implode (show (DisplayCtx mysprog collect_result))"
ML \<open>val _ = writeln (@{code my_string})\<close>

definition "dumb_entry \<equiv> merge_single (\<bottom>::dumb state_map) 0 (Some Any)"

definition "dumb_stepped \<equiv>
  step_map dumb_step (spprog mysprog) dumb_entry"

definition "dumb_advanced \<equiv>
  advance dumb_step (spprog mysprog) dumb_entry"

definition "dumb_result \<equiv>
  Dumb.ai_loop (spprog mysprog) 2 dumb_entry"

value "sorted_list_of_set (domain dumb_entry)"

value "dumb_result"
definition "abs_res_str \<equiv> String.implode (show (DisplayCtx mysprog dumb_result))"
ML \<open>val _ = writeln (@{code abs_res_str})\<close>


end