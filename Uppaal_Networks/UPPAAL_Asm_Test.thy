theory UPPAAL_Asm_Test
  imports UPPAAL_Asm_AbsInt "HOL-IMP.AExp" "HOL.String"
begin

definition myprog :: "instr list" where "myprog \<equiv> [
PUSH 42,
PUSH 3,
instr.LT,
HALT
]"

find_consts "('a \<Rightarrow> bool) \<Rightarrow> 'a set"

find_consts "nat \<Rightarrow> nat list"

fun assemble :: "instr list \<Rightarrow> spaced_program" where
  "assemble listing = SpacedProgram
    (set (upt 0 (length listing)))
    (\<lambda>pc. if pc < length listing then Some (listing ! pc) else None)"

class display =
  fixes display :: "'a \<Rightarrow> string"

fun hexlit :: "nat \<Rightarrow> nat \<Rightarrow> string" where
  "hexlit 0 0 = ''0x''" |
  "hexlit len v =
    (let c = v mod 16 in
    hexlit (len-1) (v div 16) @ [char_of (if c < 10 then 48 + c else 97 + (c - 10))])"

fun hexliti :: "nat \<Rightarrow> int \<Rightarrow> string" where
  "hexliti len v = hexlit len (if v < 0 then nat (-v) else nat v)"

instantiation nat :: display
begin
fun display_nat :: "nat \<Rightarrow> string" where
  "display_nat n = hexlit 4 n"
instance proof qed
end

instantiation int :: display
begin
fun display_int :: "int \<Rightarrow> string" where
  "display_int n = hexliti 1 n"
instance proof qed
end

instantiation bool :: display
begin
fun display_bool :: "bool \<Rightarrow> string" where
  "display_bool True = ''True''" |
  "display_bool False = ''False''"
instance proof qed
end

instantiation instr :: display
begin
fun display_instr :: "instr \<Rightarrow> string" where
  "display_instr (JMPZ a) = ''JMPZ '' @ (display a)" |
  "display_instr ADD = ''ADD''" |
  "display_instr NOT = ''NOT''" |
  "display_instr AND = ''AND''" |
  "display_instr instr.LT = ''LT''" |
  "display_instr instr.LE = ''LE''" |
  "display_instr instr.EQ = ''EQ''" |
  "display_instr (PUSH imm) = ''PUSH '' @ (display imm)" |
  "display_instr POP = ''POP''" |
  "display_instr (LID r) = ''LID '' @ (display r)"|
  "display_instr STORE = ''STORE''" |
  "display_instr (STOREI r imm) = ''STOREI '' @ (display r) @ '' '' @ (display imm)"|
  "display_instr COPY = ''COPY''" |
  "display_instr CALL = ''CALL''" |
  "display_instr RETURN = ''RETURN''" |
  "display_instr HALT = ''HALT''" |
  "display_instr (STOREC n i) = ''STOREC '' @ (display n) @ '' '' @ (display i)" |
  "display_instr (SETF b) = ''SETF '' @ (display b)"
instance proof qed
end

abbreviation init where "init \<equiv> (0, [], [], False, [])"
value "case assemble myprog of (SpacedProgram space prog) \<Rightarrow> step (the (prog (state_pc init))) init"

instantiation spaced_program :: display
begin
fun display_spaced_program :: "spaced_program \<Rightarrow> string" where
  "display_spaced_program (SpacedProgram space prog) =
    concat (map (\<lambda>pc. (display pc) @ '' '' @ (display (the (prog pc))) @ [char_of (10::nat)]) (sorted_list_of_set space))"
instance proof qed
end

definition "asm_width \<equiv> 20"
datatype dispcollect = DisplayCollect spaced_program "cstate option"

definition "emoji \<equiv> map char_of ([240,159,164,183] :: nat list)"

fun intercalate:: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "intercalate _ [] = []" |
  "intercalate _ [x] = x" |
  "intercalate sep (x # xs) = x @ sep @ intercalate sep xs"

fun format_cpstate :: "cpstate \<Rightarrow> string" where
  "format_cpstate (stk, rst, flg, clk) =
    ''f='' @ display flg"

definition folds :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "folds f z A = (THE y. fold_graph f z A y)"

fun to_list :: "'a set \<Rightarrow> 'a list" where
  "to_list _ = undefined"

lemma[code]: "to_list (set as) = as" sorry

fun format_cpstates :: "cpstate set option \<Rightarrow> string" where
  "format_cpstates None = ''--''" |
  "format_cpstates (Some states) =
    (let stuff = map format_cpstate (fold (#) [] (to_list states)) in
    intercalate ''; '' stuff)"

ML \<open>@{code format_cpstates}\<close>

fun format_collect_line :: "nat \<Rightarrow> addr \<Rightarrow> program \<Rightarrow> cstate \<Rightarrow> string" where
  "format_collect_line len pc prog st =
      (let asm = (display pc) @ '' '' @ (display (the (prog pc)));
           padding = replicate ((asm_width - 1) - length asm + 1) CHR '' '';
           states = format_cpstates (lookup st pc) in
      asm @ padding @ states @ ''\<newline>'')"

instantiation dispcollect :: display
begin
fun display_dispcollect :: "dispcollect \<Rightarrow> string" where
  "display_dispcollect (DisplayCollect _ None) = ''fail''" |
  "display_dispcollect (DisplayCollect (SpacedProgram space prog) (Some st)) =
    concat (map (\<lambda>pc. format_collect_line asm_width pc prog st) (sorted_list_of_set space))"
instance proof qed
end

definition "collect_sprog \<equiv> assemble myprog"

fun spprog :: "spaced_program \<Rightarrow> program" where
  "spprog (SpacedProgram _ prog) = prog"

definition "empty_state \<equiv> ([], [], False, [])"
definition "empty_state1 \<equiv> ([], [], True, [])"

definition "collect_result \<equiv>
  let prog = spprog collect_sprog;
      entry = (\<lambda>pc. if pc = 0 then Some {empty_state, empty_state1} else None) in
  collect_loop prog 4 (entry, {0})"

definition "my_string \<equiv> String.implode (display (DisplayCollect collect_sprog collect_result))"
ML \<open>val _ = writeln (@{code my_string})\<close>

end