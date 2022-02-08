(* Author: Simon Wimmer *)
section \<open>JSON Parsing\<close>
theory JSON_Parsing
  imports Lexer
begin

definition [consuming]:
  "brace_open \<equiv> lx_ws *-- exactly ''{''"

definition [consuming]:
 "brace_close \<equiv> lx_ws *-- exactly ''}''"

definition [consuming]:
  "bracket_open \<equiv> lx_ws *-- exactly ''[''"

definition [consuming]:
  "bracket_close \<equiv> lx_ws *-- exactly '']''"

definition [consuming]:
  "colon \<equiv> lx_ws *-- exactly '':''"

definition [consuming]:
  "comma \<equiv> lx_ws *-- exactly '',''"

definition json_character :: "(char,char) parser" where [consuming]:
  \<comment>\<open>This is both, too permissive and too strict compared to JSON\<close>
  "json_character \<equiv> do {
    x\<leftarrow>get;
    if x \<notin> set [CHR ''\"'', CHR 0x92, CHR ''\<newline>'']
    then return x
    else err_expecting (shows_string ''JSON string character'') }"

definition [consuming]:
  "json_string = exactly ''\"'' *-- repeat json_character --* exactly ''\"''"
  \<comment>\<open>Less permissive than JSON strings\<close>

definition [consuming]:
  "identifier = exactly ''\"'' *-- repeat1 json_character --* exactly ''\"''"

fun nats_to_nat :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "nats_to_nat x [] = x" |
  "nats_to_nat x (n # ns) = nats_to_nat (10 * x + n) ns"

(* definition [consuming]:
  "lx_rat_fract \<equiv> repeat1 lx_digit'
    with (\<lambda>ns. Fract (int (nats_to_nat 0 ns)) (int (10 ^ length ns)))"

definition lx_rat[consuming]:
  "lx_rat \<equiv> lx_int -- exactly ''.'' *-- lx_rat_fract
    with (\<lambda> (a, b). if a \<ge> 0 then of_int a + b else of_int a - b)" *)

datatype fract = Rat bool int int

definition lx_rat[consuming]:
  "lx_rat \<equiv> lx_int -- exactly ''.'' *-- (repeat1 lx_digit' with int o nats_to_nat 0)
    with (\<lambda> (a, b). if a \<ge> 0 then Rat True a b else Rat False a b)"


definition
  "parse_list a \<equiv> chainL1 (a with (\<lambda>a. [a])) (do {comma; return (@)})"

abbreviation
  "parse_list' a \<equiv> parse_list a \<parallel> lx_ws with (\<lambda>_. [])"

lemma parse_list_cong[fundef_cong]:
  assumes "\<And>l2. ll_fuel l2 \<le> ll_fuel l' \<Longrightarrow> A l2 = A' l2"
  assumes "l=l'"
  shows "parse_list A l = parse_list A' l'"
  unfolding parse_list_def chainL1_def
  apply (intro bind_cong repeat_cong assms order_refl)
  by auto

datatype JSON =
  is_obj: Object "(string \<times> JSON) list"
| is_array: Array "JSON list"
| is_string: String string \<comment>\<open>An Isabelle string rather than a JSON string\<close>
| is_int: Int int \<comment>\<open>The number type is split into natural Isabelle/HOL types\<close>
| is_nat: Nat nat
| is_rat: Rat fract
| is_boolean: Boolean bool \<comment>\<open>True and False are contracted to one constructor\<close>
| is_null: Null

definition [consuming]:
  "atom \<equiv> lx_ws *-- (
     json_string       with String
   \<parallel> lx_rat            with JSON.Rat
   \<parallel> lx_nat            with Nat
   \<parallel> lx_int            with JSON.Int
   \<parallel> exactly ''true''  with (\<lambda>_. Boolean True)
   \<parallel> exactly ''false'' with (\<lambda>_. Boolean False)
   \<parallel> exactly ''null''  with (\<lambda>_. Null)
)"

fun json and dict and seq where
  "json ::= atom \<parallel> seq \<parallel> dict" |
  "dict ::=
    brace_open *--
      parse_list' (lx_ws *-- identifier -- colon *-- json)
    --* brace_close with Object" |
  "seq  ::=
    bracket_open *--
      parse_list' json
    --* bracket_close with Array"


paragraph \<open>Test Cases\<close>

definition test where "test \<equiv> STR
''
{
 \"a\": [\"b\", {\"a\":\"a\",\"b\":[\"b\" ,\"d\"]}] ,

 \"c\" : \"c\",

 \"ab\" : 1,
 \"abcd1\" : -11,

 \"abc\" : 11.1,
\"_abc-\" : true,
\"ab_c\" : false,
\"a-bc\":null
}''
"

value [code]
  "parse_all lx_ws json test"

definition test2 where "test2 \<equiv>
 STR ''{
    \"info\": \"Derived from the Uppaal benchmarks found at https://www.it.uu.se/research/group/darts/uppaal/benchmarks/\",
    \"automata\": [
        {
            \"name\": \"ST2\",
            \"initial\": 9,
            \"nodes\": [
                {
                    \"id\": 14,
                    \"name\": \"y_idle\",
                    \"x\": 458.2894592285156,
                    \"y\": 442.4790954589844,
                    \"invariant\": \"\"
                }
            ],
            \"edges\": [
                {
                    \"source\": 9,
                    \"target\": 12,
                    \"guard\": \"\",
                    \"label\": \"tt1?\",
                    \"update\": \"y2 := 0, x2 := 0\"
                }
            ]
        }
    ],
    \"clocks\": \"x0, x1, y1, z1, x2, y2, z2\",
    \"vars\": \"id[-1:2]\",
    \"formula\": \"E<> ((ST1.z_sync || ST1.z_async)  && (ST2.z_sync || ST2.z_async)  )\"
}''"

value [code] "parse_all lx_ws json test2"

end