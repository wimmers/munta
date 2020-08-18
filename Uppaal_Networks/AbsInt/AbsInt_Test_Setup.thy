theory AbsInt_Test_Setup
  imports
    "HOL.Code_Numeral"
    "HOL-Library.Code_Target_Int"
    "HOL-Library.Code_Target_Nat"
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
PUSH 123
]"

definition "myprog \<equiv> assemble (map Some myprog_listing)"

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

type_synonym si_state =   "(strided_interval toption option, strided_interval toption option stack_window) smart"
definition show_display_ctx :: "si_state dispctx \<Rightarrow> string" where
  "show_display_ctx = show"

definition "set_entry \<equiv> (merge_single \<bottom> 0 (Some (Smart \<bottom> \<bottom> BFalse)))::si_state state_map"
definition "set_result \<equiv> final_loop_fp 16 16 (fetch_op myprog) 100 set_entry"
definition "set_res_str \<equiv> String.implode (show_display_ctx (DisplayCtx myprog set_result))"

definition "entry_default \<equiv> (merge_single \<bottom> 0 (Some (Smart \<bottom> \<bottom> BFalse)))::si_state state_map"
definition "entry_later \<equiv> (merge_single \<bottom> 5 (Some (Smart \<bottom> \<bottom> BFalse)))::si_state state_map"

ML_file "../../ML/Scan_More.ML";
ML\<open>
(*** Utilities for parsing
 * Should be removed at some point
***)

datatype ('a, 'b) instr' = JMPZ' of 'a | ADD' | NOT' | AND' | LT' | LE' | EQ' | PUSH' of 'b | POP' |
    LID' of 'a | STOREI' of 'a * 'b | COPY' | CALL' | RETURN' | HALT' |
    STOREC' of 'a * 'b | SETF' of bool

datatype ('a, 'b) acconstraint = LTa of 'a * 'b | LEa of 'a * 'b |
  EQa of 'a * 'b | GT of 'a * 'b | GE of 'a * 'b;

datatype 'a act = In of 'a | Out of 'a | Sil of 'a;

datatype ('a, 'b, 'c) instrc' = INSTR' of ('a, 'b) instr' | CEXP' of ('a, 'c) acconstraint

datatype ('a, 'b) bexp' =
  Not' of ('a, 'b) bexp' |
  And' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Or' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Imply' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Loc' of 'a * 'a | Eq' of 'a * 'b | Lea' of 'a * 'b |
  Lta' of 'a * 'b | Ge' of 'a * 'b | Gt' of 'a * 'b

datatype ('a, 'b) formula' =
  EX' of ('a, 'b) bexp' |
  EG' of ('a, 'b) bexp' |
  AX' of ('a, 'b) bexp' |
  AG' of ('a, 'b) bexp' |
  Leadsto' of ('a, 'b) bexp' * ('a, 'b) bexp' |
  Has_Deadlock

infix 9 Lea' Lta' Ge' Gt' Eq'
infix 8 And'
infix 7 Or' Imply'

fun map_acconstraint f g = fn
  LTa (a, b) => LTa (f a, g b) |
  LEa (a, b) => LEa (f a, g b) |
  EQa (a, b) => EQa (f a, g b) |
  GE (a, b) => GE (f a, g b) |
  GT (a, b) => GT (f a, g b)

fun map_act f = fn
  In a => In (f a) |
  Out a => Out (f a) |
  Sil a => Sil (f a)

fun map_instr f_nat f_int = fn
  JMPZ' n => @{code JMPZ} (f_nat n) |
  PUSH' i => @{code PUSH} (f_int i) |
  LID' n => @{code LID} (f_nat n) |
  STOREI' (n, i) => @{code STOREI} (f_nat n, f_int i) |
  STOREC' (n, i) => @{code STOREC} (f_nat n, f_int i) |
  ADD' => @{code ADD} | NOT' => @{code NOT} | AND' => @{code AND} | LT' => @{code LT} | LE' => @{code LE} | EQ' => @{code EQ} |
  POP' => @{code POP} | COPY' => @{code COPY} | CALL' => @{code CALL} | RETURN' => @{code RETURN} | HALT' => @{code HALT} |
  SETF' b => @{code SETF} b

fun map_option _ NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun map_instrc f_nat f_int _ = fn
  SOME (INSTR' instr) => SOME (map_instr f_nat f_int instr) |
  SOME (CEXP' _) => NONE |
  NONE => NONE

fun nat_of_integer k = @{code nat} k;

val to_int = @{code int_of_integer}
val to_nat = @{code nat} o @{code int_of_integer}

(*** Parsing ***)
open Scan_More;

fun scan_pairc_int x = scan_pairc [scan_int, scan_int] x
val scan_acconstraint_lt = scan_pairc_int "LTa" (op LTa)
val scan_acconstraint_le = scan_pairc_int "LEa" (op LEa)
val scan_acconstraint_eq = scan_pairc_int "EQa" (op EQa)
val scan_acconstraint_ge = scan_pairc_int "GE" (op GE)
val scan_acconstraint_gt = scan_pairc_int "GT" (op GT)
val scan_acconstraint = Scan.first [
  scan_acconstraint_lt,
  scan_acconstraint_le,
  scan_acconstraint_eq,
  scan_acconstraint_ge,
  scan_acconstraint_gt
  ]

fun scan_infix_pairc_int x = scan_infix_pairc scan_int scan_int x;

fun scan_parens lparen rparen inner =
  op $$ lparen |-- scan_whitespace |-- inner --| scan_whitespace --| op $$ rparen

val scan_bexp_elem = Scan.first [
  scan_pairc_int "Loc'"  (op Loc'),
  scan_pairc_int "Lea''" (op Lea'),
  scan_pairc_int "Eq'"   (op Eq'),
  scan_pairc_int "Lta'"  (op Lta'),
  scan_pairc_int "Ge'"   (op Ge'),
  scan_pairc_int "Gt'"   (op Gt')
]
fun scan_bexp xs =
  let
    val scan_parens = scan_parens "(" ")"
    fun scan_7 xs =
      xs |>
      (
        scan_infix_pairc scan_6 scan_7 "Imply'" op Imply' ||
        scan_infix_pairc scan_6 scan_7 "Or'" op Or' ||
        scan_6
      )
    and scan_6 xs =
      xs |> (scan_infix_pairc scan_0 scan_6 "And'" op And' || scan_0)
    and scan_inner_bexp xs = xs |> scan_parens scan_7
    and scan_prefix sep constr =
      Scan.this_string sep -- scan_whitespace |-- scan_inner_bexp >> constr
    and scan_0 xs =
      xs |>
      (
        scan_prefix "Not'" op Not' ||
        scan_bexp_elem ||
        scan_inner_bexp
      )
  in
    scan_7 xs
  end

val scan_formula = scan_parens "(" ")" (Scan.first [
  scan_nullary "has_deadlock" op Has_Deadlock,
  scan_singlec scan_bexp "EX" op EX',
  scan_singlec scan_bexp "EG" op EG',
  scan_singlec scan_bexp "AX" op AX',
  scan_singlec scan_bexp "AG" op AG',
  scan_infix_pairc scan_bexp scan_bexp "Leadsto" op Leadsto',
  scan_infix_pairc scan_bexp scan_bexp "-->"     op Leadsto'
  ])

val scan_singlec_int = scan_singlec scan_int

val scan_act = Scan.first [
  scan_singlec_int "In" op In,
  scan_singlec_int "Out" op Out,
  scan_singlec_int "Sil" op Sil
  ]

val scan_bool =
  Scan.this_string "true" >> K true || Scan.this_string "false" >> K false

val instr_nullaries = [
  ("ADD'", op ADD'),
  ("NOT'", op NOT'),
  ("AND'", op AND'),
  ("LT'", op LT'),
  ("LE'", op LE'),
  ("EQ'", op EQ'),
  ("COPY'", op COPY'),
  ("CALL'", op CALL'),
  ("RETURN'", op RETURN'),
  ("HALT'", op HALT'),
  ("POP'", op POP')
  ]
val scan_nullary_instr = Scan.first (map (uncurry scan_nullary) instr_nullaries)
val scan_instr = scan_nullary_instr ||
  Scan.first [
  scan_pairc_int "STOREI'" op STOREI',
  scan_pairc_int "STOREC'" op STOREC',
  scan_singlec scan_int "JMPZ'" op JMPZ',
  scan_singlec scan_int "LID'" op LID',
  scan_singlec scan_int "PUSH'" op PUSH',
  scan_singlec scan_bool "SETF'" op SETF'
  ]
val scan_instrc =
  scan_singlec scan_nullary_instr "INSTR'" op INSTR' ||
  scan_singlec (scan_parens "(" ")" scan_instr) "INSTR'" op INSTR' ||
  scan_singlec (scan_parens "(" ")" scan_acconstraint) "CEXP'" op CEXP'

fun scan_option p = scan_nullary "NONE" NONE || scan_singlec p "SOME" SOME

fun scan_quadruple' (p1, p2, p3, p4) =
  scan_parens "(" ")" (
    (p1 --| op $$ "," --| scan_whitespace) --
    (p2 --| op $$ "," --| scan_whitespace) --
    (p3 --| op $$ "," --| scan_whitespace) --
    p4 >> (fn (((a, b), c), d) => (a, b, c, d))
  )
val scan_invariant = scan_list (scan_list (scan_list scan_acconstraint))
val scan_trans =
  scan_quadruple' (scan_int, scan_act, scan_int, scan_int) |>
  scan_list |>
  scan_list |>
  scan_list
val scan_prog = scan_parens "(" ")" scan_instrc |> scan_option |> scan_list
(* XXX Why do we need this renewed fixity declaration? *)
val scan_all =
  scan_int --- (* p *)
  scan_int --- (* m *)
  scan_list scan_int --- (* k *)
  scan_int --- (* max_steps *)
  scan_invariant --- (* inv *)
  scan_trans --- (* trans *)
  scan_prog --- (* prog *)
  scan_formula --- (* query *)
  scan_list (scan_pair [scan_int, scan_int]) --- (* bounds *)
  (scan_int |> scan_list |> scan_list) --- (* pred *)
  scan_list scan_int --- (* s *)
  scan_int (* na *)
  (* XXX Can we end with EOF or EOS here? *)

(*** Printing utilites ***)
fun println s = writeln s (*print (s ^ "\n")*)

fun list_to_string f = (fn x => "[" ^ x ^ "]") o String.concatWith ", " o map f;

fun print_result NONE = println("Invalid input\n")
    | print_result (SOME true) = println("Property is satisfied\n")
    | print_result (SOME false) = println("Property is not satisfied\n")

fun read_lines stream =
  let
    val input = TextIO.inputLine stream
      handle Size => (println "Input line too long!"; raise Size)
  in
    case input of
      NONE => ""
    | SOME input => input ^ read_lines stream
  end

fun show_result prog = fn
  @{code RSM} sm => @{code DisplayCtx} (prog, @{code RSM} sm) |> @{code show_display_ctx} |> @{code String.implode} |
  @{code RSMS} _ => "Top"

fun program_file file =
  let
    val f = TextIO.openIn file
    val input = read_lines f
    val (((((((_, prog'), _), _), _), _), _), _) = scan_all (explode_string (input ^ " "))
    val prog = map (map_instrc to_nat to_int to_int) prog'
  in
    @{code assemble} prog
  end;

fun absint_run prog entry window_size concretize_max steps =
  let
    val result = @{code final_loop_fp} (to_nat window_size) (to_nat concretize_max) (@{code fetch_op} prog) (to_nat steps) entry
  in
    show_result prog result |> writeln
  end;

val absint_benchmark = absint_run o program_file

val entry_default = @{code entry_default}
val entry_later = @{code entry_later}
val myprog = @{code myprog}
\<close>

(*definition "empty_state \<equiv> ([], [], False, [])"
definition "empty_state1 \<equiv> ([], [], True, [])"
definition "(collect_result::collect_state set state_map) \<equiv>
  let prog = fetch_op myprog;
      entry = deepen {(0::addr, empty_state), (0, empty_state1)} in
  collect_loop prog 4 entry"
definition "my_string \<equiv> String.implode (show (DisplayCtx mysprog collect_result))"
ML \<open>val _ = writeln (@{code my_string})\<close>*)
end