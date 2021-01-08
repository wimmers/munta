theory UPPAAL_Asm_Show
  imports
    UPPAAL_Asm_Map
    UPPAAL_Asm_Assemble
begin

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
instance ..
end

instantiation int :: "show"
begin
fun show_int :: "int \<Rightarrow> string" where
  "show_int n = hexliti 1 n"
instance ..
end

instantiation bool :: "show"
begin
fun show_bool :: "bool \<Rightarrow> string" where
  "show_bool True = ''True''" |
  "show_bool False = ''False''"
instance ..
end

instantiation instr :: "show"
begin
fun show_instr :: "instr \<Rightarrow> string" where
  "show_instr NOP = ''NOP''" |
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
  "show_list_rest [x] = show x @ '']''" |
  "show_list_rest (x # xs) = show x @ '', '' @ show_list_rest xs"

fun show_list :: "'a list \<Rightarrow> string" where
  "show_list [] = ''[]''" |
  "show_list xs = CHR ''['' # show_list_rest xs"
instance ..
end

instantiation option :: ("show") "show"
begin
fun show_option :: "'a option \<Rightarrow> string" where
  "show_option None = ''None''" |
  "show_option (Some x) = ''Some '' @ show x"
instance ..
end

abbreviation init where "init \<equiv> (0, [], [], False, [])"

instantiation concrete_program :: "show"
begin
fun show_concrete_program :: "concrete_program \<Rightarrow> string" where
  "show_concrete_program p =
    (let space = prog_domain p in
    concat (map (\<lambda>pc. (show pc) @ '' '' @ (show (the (fetch_op p pc))) @ [char_of (10::nat)]) (sorted_list_of_set space)))"
instance ..
end

definition "asm_width \<equiv> 20"
datatype 'a dispctx = DisplayCtx concrete_program "'a state_map"

definition "emoji \<equiv> map char_of ([240,159,164,183] :: nat list)"

fun intercalate:: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "intercalate _ [] = []" |
  "intercalate _ [x] = x" |
  "intercalate sep (x # xs) = x @ sep @ intercalate sep xs"

fun format_ctx_line :: "nat \<Rightarrow> addr \<Rightarrow> program \<Rightarrow> 'a::show \<Rightarrow> string" where
  "format_ctx_line len pc prog v =
      (let asm = (show pc) @ '' '' @ (case prog pc of Some op \<Rightarrow> show op | None \<Rightarrow> ''--'');
           padding = replicate ((asm_width - 1) - length asm + 1) CHR '' '';
           states = show v in
      asm @ padding @ states @ ''\<newline>'')"

instantiation dispctx :: ("{show, bot}") "show"
begin
fun show_dispctx :: "'a dispctx \<Rightarrow> string" where
  "show_dispctx (DisplayCtx p st) =
    concat (map (\<lambda>pc. format_ctx_line asm_width pc (fetch_op p) (lookup st pc)) (sorted_list_of_set (prog_domain p \<union> domain st)))"
instance ..
end

end