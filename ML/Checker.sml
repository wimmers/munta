open Model_Checker;

(*** Utilities for parsing
 * Should be removed at some point
***)
datatype ('a, 'b) instr' = JMPZ' of 'a | ADD' | NOT' | AND' | LT' | LE' | EQ' | PUSH' of 'b | POP' |
    LID' of 'a | STOREI' of 'a * 'b | COPY' | CALL' | RETURN' | HALT' |
    STOREC' of 'a * 'b | SETF' of bool

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
  Leadsto' of ('a, 'b) bexp' * ('a, 'b) bexp'


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
  JMPZ' n => JMPZ (f_nat n) |
  PUSH' i => PUSH (f_int i) |
  LID' n => LID (f_nat n) |
  STOREI' (n, i) => STOREI (f_nat n, f_int i) |
  STOREC' (n, i) => STOREC (f_nat n, f_int i) |
  ADD' => ADD | NOT' => NOT | AND' => AND | LT' => LT | LE' => LE | EQ' => EQ |
  POP' => POP | COPY' => COPY | CALL' => CALL | RETURN' => RETURN | HALT' => HALT |
  SETF' b => SETF b

fun map_instrc f_nat f_int f_time = fn
  INSTR' instr => INSTR (map_instr f_nat f_int instr) |
  CEXP' ac => CEXP (map_acconstraint f_nat f_time ac)

fun map_bexp f_nat f_int = fn
  Not' a => Not (map_bexp f_nat f_int a) |
  a And' b => And (map_bexp f_nat f_int a, map_bexp f_nat f_int b) |
  a Or' b => Or (map_bexp f_nat f_int a, map_bexp f_nat f_int b) |
  a Imply' b => Imply (map_bexp f_nat f_int a, map_bexp f_nat f_int b) |
  Loc' (p, l) => Loc (f_nat p, f_nat l) |
  v Lta' x => Lta (f_nat v, f_int x) |
  v Lea' x => Lea (f_nat v, f_int x) |
  v Eq' x => Eq (f_nat v, f_int x) |
  v Ge' x => Ge (f_nat v, f_int x) |
  v Gt' x => Gt (f_nat v, f_int x)

fun map_formula f_nat f_int =
  let
    val f = map_bexp f_nat f_int
  in
    fn
      EX' a => EX (f a) |
      EG' a => EG (f a) |
      AX' a => AX (f a) |
      AG' a => AG (f a) |
      Leadsto' (a, b) => Leadsto (f a, f b)
  end


val to_int = Int_of_integer o IntInf.fromInt
val to_nat = nat_of_integer o IntInf.fromInt
val nat_of_int = nat_of_integer o integer_of_int


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
fun println s = print (s ^ "\n")

fun list_to_string f = (fn x => "[" ^ x ^ "]") o String.concatWith ", " o map f;

fun print_result NONE = println("Invalid input\n")
    | print_result (SOME true) = println("Property is satisfied\n")
    | print_result (SOME false) = println("Property is not satisfied\n")


(*** Wrapping up the checker ***)
fun check_and_verify2 p m ignore_k max_steps inv trans prog query bounds pred s na () =
  let
    val debug_level: Int32.int Unsynchronized.ref = ref 0
    val _ = debug_level := 1

    val map_constraint = map (map_acconstraint to_nat to_int);
    val inv = map (map map_constraint) inv;
    val trans =
      map (map (map (fn (g, a, r, l) => (to_nat g, (map_act to_nat a, (to_nat r, to_nat l)))))) trans;
    val prog = map (map_option (map_instrc to_nat to_int to_int)) prog
    val query = map_formula to_nat to_int query
    val bounds = map (fn (a, b) => (to_int a, to_int b)) bounds
    val pred = map (map to_nat) pred
    val s = map to_int s
    val p = to_nat p
    val m = to_nat m
    val max_steps = to_nat max_steps
    val na = to_nat na;
    val _ = if !debug_level >= 3 then println("Now calculating ceiling") else ();
    val k = k p m max_steps inv trans prog;
    val k = map (map (map nat_of_int)) k;
    val _ = if !debug_level >= 3 then println("Finished calculating ceiling") else ();
    val _ =
      if !debug_level >= 3 then
        println (
          "\n"
          ^ list_to_string (list_to_string (list_to_string (IntInf.toString o integer_of_nat))) k
          ^ "\n"
        )
      else ()

    fun print_precondition_check name test =
      let
        val s = "Precondition check " ^ name ^ ": " ^ (if test then "Passed" else "Failed")
      in println s end;

    val _ = if !debug_level >= 2 then
      let
        val test1 = uPPAAL_Reachability_Problem_precompiled_start_state
            p m max_steps inv trans prog bounds pred s
        val test1a = uPPAAL_Reachability_Problem_precompiled p m inv pred trans prog
        val test1aa = check_pre p m inv pred trans prog
        val test1ab = check_ceiling p m max_steps inv trans prog k;
        val test1b =
          uPPAAL_Reachability_Problem_precompiled_start_state_axioms p max_steps trans
              prog bounds pred s;
        val init_pred_check = init_pred_check p prog max_steps pred s;
        val bounded_check = bounded_int bounds s
        val indep_1 = time_indep_check1 pred prog max_steps
        val indep_2 = time_indep_check2 trans prog max_steps
        val d = conjunction_check2 trans prog max_steps
        val tests =
          [
            ("1", test1),
            ("1a", test1a),
            ("1aa", test1aa),
            ("1ab", test1ab),
            ("1b", test1b),
            ("initial_predicate", init_pred_check),
            ("boundedness", bounded_check),
            ("time_independence_1", indep_1),
            ("time_independence_2", indep_2),
            ("conjunctiveness", d)
          ]
        val _ = map (uncurry print_precondition_check) tests;
      in println "" end else ();
    val t = Time.now ()
    val result = Model_Checker.precond_mc p m k max_steps inv trans prog query bounds pred s na ()
    val t = Time.- (Time.now (), t)
    val _ = println("Internal time for precondition check + actual checking: " ^ Time.toString t)
    val _ = println("")
    val _ = if !debug_level >= 1 then
      let
        val _ = println("# explored states: " ^ Int.toString(Tracing.get_count ()))
        val _ = println("")
      in () end else ();
    (*val _ = if !debug_level >= 1 then
      let
        val _ = println("# additions on DBM entries:" ^ Int.toString (!cnt))
        val _ = println("# explored states:" ^ Int.toString (!cnt2))
        val _ = println("")
      in () end else ();
     *)
  in
    print_result result
  end;

fun check_and_verify_parse input =
  let
    val (result, _) = scan_all input
      handle x => (println "Parse error"; raise x)
    val (result, na) = result
    val (result, s) = result
    val (result, pred) = result
    val (result, bounds) = result
    val (result, query) = result
    val (result, prog) = result
    val (result, trans) = result
    val (result, inv) = result
    val (result, max_steps) = result
    val (result, ignore_k) = result
    val (result, m) = result
    val p = result
  in
    check_and_verify2 p m ignore_k max_steps inv trans prog query bounds pred s na
  end;

fun read_lines stream =
  let
    val input = TextIO.inputLine stream
      handle Size => (println "Input line too long!"; raise Size)
  in
    case input of
      NONE => ""
    | SOME input => input ^ read_lines stream
  end

fun check_and_verify_from_stream stream =
  let
    val input = read_lines stream
  in
    if input = ""
    then (println "Failed to read line from input!"; fn () => ())
      (* We append a space to terminate the input for the parser *)
    else input ^ " " |> explode_string |> check_and_verify_parse
  end;
