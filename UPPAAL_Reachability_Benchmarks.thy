theory UPPAAL_Reachability_Benchmarks
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

term Array.nth' ML \<open>Array.sub\<close>
term array_get' term "\<lambda> a. array_get' a o integer_of_int" term array_grow' term array_length'

term integer_of_nat

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

thm UPPAAL_Reachability_Problem_precompiled_def

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
  nat
  REACHABLE UNREACHABLE INIT_INV_ERR
  UPPAAL_Reachability_Problem_precompiled_defs.k
  in SML_imp module_name Reachability_Checker
  file "UPPAAL_Reachability_Checker.ml"

ML_file "UPPAAL_Reachability_Checker.ml"

ML \<open>
  open Reachability_Checker;;
\<close>

ML \<open>REACHABLE\<close>
ML_val \<open>app\<close>

ML \<open>integer_of_nat\<close>
ML \<open>IntInf.toInt\<close>
ML \<open>nat_of_integer o IntInf.fromInt\<close>
ML \<open>Int_of_integer\<close>
ML \<open>nat_of_integer o integer_of_int\<close>
ML \<open>integer_of_nat\<close>
ML \<open>Vector.sub\<close>

ML \<open>Array.sub\<close>

ML \<open>
  fun map_acconstraint f g = fn
    LTa (a, b) => LTa (f a, g b) |
    LEa (a, b) => LEa (f a, g b) |
    EQa (a, b) => EQa (f a, g b) |
    GE (a, b) => GE (f a, g b) |
    GT (a, b) => GT (f a, g b)
\<close>

ML \<open>
  fun map_act f = fn
    In a => In (f a) |
    Out a => Out (f a) |
    Sil a => Sil (f a)
\<close>

ML \<open>
datatype ('a, 'b) instr' = JMPZ' of 'a | ADD' | NOT' | AND' | LT' | LE' | EQ' | PUSH' of 'b | POP' |
    LID' of 'a | STORE' of 'a * 'b | COPY' | CALL' | RETURN' | HALT' |
    STOREC' of 'a * 'b | SETF' of bool
\<close>

ML \<open>
  fun map_instr f_nat f_int = fn
    JMPZ' n => JMPZ (f_nat n) |
    PUSH' i => PUSH (f_int i) |
    LID' n => LID (f_nat n) |
    STORE' (n, i) => STORE (f_nat n, f_int i) |
    STOREC' (n, i) => STOREC (f_nat n, f_int i) |
    ADD' => ADD | NOT' => NOT | AND' => AND | LT' => LT | LE' => LE | EQ' => EQ |
    POP' => POP | COPY' => COPY | CALL' => CALL | RETURN' => RETURN | HALT' => HALT |
    SETF' b => SETF b
\<close>

ML \<open>
  datatype ('a, 'b, 'c) instrc' = INSTR' of ('a, 'b) instr' | CEXP' of ('a, 'c) acconstraint

  fun map_instrc f_nat f_int f_time = fn
    INSTR' instr => INSTR (map_instr f_nat f_int instr) |
    CEXP' ac => CEXP (map_acconstraint f_nat f_time ac)
\<close>

ML \<open>time_indep_check1\<close>

ML \<open>ML_Syntax.print_term\<close>

ML \<open>ML_Syntax.print_list (IntInf.toString o integer_of_nat)\<close>

  ML \<open>IntInf.toString\<close>

ML \<open>
  datatype ('a, 'b) bexp' =
    Not' of ('a, 'b) bexp' |
    And' of ('a, 'b) bexp' * ('a, 'b) bexp' |
    Or' of ('a, 'b) bexp' * ('a, 'b) bexp' |
    Imply' of ('a, 'b) bexp' * ('a, 'b) bexp' |
    Loc' of 'a * 'a | Eq' of 'a * 'b | Lea' of 'a * 'b |
    Lta' of 'a * 'b | Ge' of 'a * 'b | Gt' of 'a * 'b
\<close>

ML \<open>infix 9 Lea' Lta' Ge' Gt' Eq'\<close>
ML \<open>infix 8 And'\<close>
ML \<open>infix 7 Or' Imply'\<close>

ML \<open>
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
\<close>

ML \<open>integer_of_int\<close>

ML \<open>
\<close>

ML \<open>

  fun check_and_verify p m k max_steps inv trans prog query bounds pred s na =
    let
      val k = map nat_of_integer k;
      val map_constraint = map (map_acconstraint Nat Int_of_integer);
      val inv = map (map map_constraint) inv;
      val trans =
        map (map (map (fn (g, a, r, l) => (Nat g, (map_act Nat a, (Nat r, Nat l)))))) trans;
      val prog = map (map_option (map_instrc Nat Int_of_integer Int_of_integer)) prog
      val query = map_bexp Nat Int_of_integer query
      val bounds = map (fn (a, b) => (Int_of_integer a, Int_of_integer b)) bounds
      val pred = map (map Nat) pred
      val s = map Int_of_integer s
      val p = Nat p
      val m = Nat m
      val max_steps = Nat max_steps
      val na = Nat na

      (*
      val test1 = uPPAAL_Reachability_Problem_precompiled_start_state
          p m k max_steps inv trans prog bounds pred s
      val _ = writeln ("Test 1: " ^ (if test1 then "Passed" else "Failed"))
      val test1a = uPPAAL_Reachability_Problem_precompiled p m k inv pred trans prog
      val _ = writeln ("Test 1a: " ^ (if test1a then "Passed" else "Failed"))
      *)
      val test1aa = check_pre p m k inv pred trans prog
      val _ = writeln ("Test 1aa: " ^ (if test1aa then "Passed" else "Failed"))
      val b = equal_nata (size_list inv) p andalso equal_nata (size_list pred) p andalso
              equal_nata (size_list trans) p
      val c = (all_interval_nat
           (fn i =>
             equal_nata (size_list (nth pred i))
               (size_list (nth trans i)) andalso
               equal_nata (size_list (nth inv i)) (size_list (nth trans i))) zero_nat p)
      val d = list_all
             (fn t =>
               list_all
                 (list_all (fn (_, (_, (_, l))) => less_nat l (size_list t))) t)
             trans
      val e = equal_nata (size_list k) (plus_nat m one_nat) andalso
              less_nat zero_nat p andalso less_nat zero_nat m
      val f = all_interval_nat (fn i => not (null (nth trans i))) zero_nat p
      val g = all_interval_nat
                       (fn q => not (null (nth (nth trans q) zero_nat)))
                       zero_nat p
      val h = equal_nata (nth k zero_nat) zero_nat
      val i = ball (clkp_set inv prog) (fn (_, a) => less_eq_int zero_inta a)
      val clks = clk_set inv prog
      val Set clk_list = clks
      val _ = writeln ("Clock set:" ^ ML_Syntax.print_list (IntInf.toString o integer_of_nat) clk_list)
      val j = eq_set (card_UNIV_nat, equal_nat) (clk_set inv prog) (Set (upt one_nat (suc m)))
      val test1aa1 = check_resets prog andalso b andalso c andalso d andalso e andalso f andalso g
        andalso h andalso i andalso j
      val _ = writeln ("Test 1aa1: " ^ (if test1aa1 then "Passed" else "Failed"))
      val test1ab = check_ceiling k inv prog;
      val _ = writeln ("Test 1ab: " ^ (if test1ab then "Passed" else "Failed"))
      (*
      val test1b =
        uPPAAL_Reachability_Problem_precompiled_start_state_axioms p max_steps trans
            prog bounds pred s;
      val _ = writeln ("Test 1b: " ^ (if test1b then "Passed" else "Failed"))
      *)
      val init_pred_check = init_pred_check p prog max_steps pred s;
      val _ = writeln ("Init pred: " ^ (if init_pred_check then "Passed" else "Failed"))
      val bounded_check = bounded ord_int bounds s
      val _ = writeln ("Bounded check: " ^ (if bounded_check then "Passed" else "Failed"))
      val indep_1 = time_indep_check1 pred prog max_steps
      val _ = writeln ("Time independence check 1: " ^ (if indep_1 then "Passed" else "Failed"))
      val indep_2 = time_indep_check2 trans prog max_steps
      val _ = writeln ("Time independence check 2: " ^ (if indep_1 then "Passed" else "Failed"))
      val d = conjunction_check2 trans prog max_steps
      val _ = writeln ("Conjunction check: " ^ (if d then "Passed" else "Failed"))
      (*
      val bounded_check = (bounded ord_int bounds s andalso
        (time_indep_check1 pred prog max_steps andalso
          (time_indep_check2 trans prog max_steps andalso
            conjunction_check2 trans prog max_steps)))
      val _ = writeln ("Bounded check: " ^ (if bounded_check then "Passed" else "Failed"))
      *)
      (*
      val test2 = uPPAAL_Reachability_Problem_precompiled_axioms trans na
      val _ = writeln ("Test 2: " ^ (if test2 then "Passed" else "Failed"))
      *)
    in
      Reachability_Checker.check_and_verify p m k max_steps inv trans prog query bounds pred s na
    end;
\<close>

ML \<open>
  val triv_example =
  check_and_verify 1 1 [0, 2] 3 [[[]]] [[[(0, Sil 0, 2, 0)]]] [SOME (CEXP' (LTa (1, 2))), SOME (INSTR' HALT'), SOME (INSTR' HALT')] (Loc' (0, 0)) [] [[2]] [] 1
\<close>

ML_val \<open>triv_example ()\<close>

(*
ML_file "~/UPPAAL/test_ta/test_state.ml"

ML_val \<open>test_state ()\<close>

ML_file "~/UPPAAL/test_ta/Test1.ml"

ML_val \<open>Test1 () = SOME true\<close>

ML_file "~/UPPAAL/test_ta/Test11.ml"

ML_val \<open>Test11 () = SOME true\<close>

ML_file "~/UPPAAL/test_ta_new/Test1a.ml"

ML_val \<open>Test1a () = SOME true\<close>

ML_file "~/UPPAAL/test_ta_new/PM_Test_1.ml"

ML_val \<open>PM_Test_1 ()\<close>

*)

ML_file "~/UPPAAL/test_ta/PM_Test_1_const.ml"

(* ML_val \<open>PM_Test_1_const ()\<close> *)

ML_file "~/UPPAAL/test_ta_new/fischer.ml"

ML_val \<open>fischer ()\<close>

ML_file "~/UPPAAL/test_ta_new/hddi.ml"

ML_val \<open>hddi ()\<close>

ML_file "~/UPPAAL/test_ta_new/hddi_input_02.ml"

ML_val \<open>hddi_input_02 ()\<close>

ML_file "~/UPPAAL/test_ta_new/hddi_input_02_sanity.ml"

ML_val \<open>hddi_input_02 ()\<close>

ML_file "~/UPPAAL/test_ta_new/csma_input_02.ml"

ML_val \<open>csma_input_02 ()\<close>

ML_file "~/UPPAAL/gen/csma_input_04.ml"

ML_val \<open>csma_input_04 ()\<close>

ML_file "~/UPPAAL/gen/csma_02.ml"

ML_val \<open>csma_02 ()\<close>

ML_file "~/UPPAAL/gen/csma_03.ml"

ML_val \<open>csma_03 ()\<close>

ML_file "~/UPPAAL/gen/csma_04.ml"

ML_val \<open>csma_04 ()\<close>

ML_file "~/UPPAAL/test_ta/Test11.ml"

ML_file "~/UPPAAL/test_ta/Test1b.ml"

ML_file "~/UPPAAL/test_ta/Tutorial_1.ml"
ML_file "~/UPPAAL/test_ta/Tutorial_11.ml"

ML_file "~/UPPAAL/test_ta/Tutorial_2.ml"

ML_file "~/UPPAAL/test_ta/Tutorial_3a.ml"

ML_file "~/UPPAAL/test_ta/Tutorial_3b.ml"

ML_file "~/UPPAAL/test_ta/Tutorial_4a.ml"
ML_file "~/UPPAAL/test_ta/Tutorial_4b.ml"
ML_file "~/UPPAAL/test_ta/Tutorial_2x2a.ml"
ML_file "~/UPPAAL/test_ta/Tutorial_2x2b.ml"
ML_file "~/UPPAAL/test_ta/broadcast_test.ml"
ML_file "~/UPPAAL/test_ta/broadcast_test2.ml"
ML_file "~/UPPAAL/test_ta/PM_Test_1.ml"
ML_file "~/UPPAAL/test_ta/PM_Test_2.ml"
ML_file "~/UPPAAL/test_ta/PM_Test_3.ml"
ML_file "~/UPPAAL/test_ta/PM_Test_4.ml"

ML_val \<open>Test1a () = SOME true\<close>
ML_val \<open>Test11 () = SOME true\<close>
ML_val \<open>Test1b () = SOME true\<close>
ML_val \<open>Tutorial_1 () = SOME true\<close>
ML_val \<open>Tutorial_11 () = SOME true\<close>
text \<open>Final location: fail\<close>
ML_val \<open>Tutorial_2 () = SOME false\<close>
text \<open>Final location: end\<close>
ML_val \<open>Tutorial_3a () = SOME true\<close>
text \<open>Final location: fail\<close>
ML_val \<open>Tutorial_3b () = SOME false\<close>
text \<open>Final location: bright\<close>
ML_val \<open>Tutorial_4a () = SOME true\<close>
text \<open>Final location: fail\<close>
ML_val \<open>Tutorial_4b () = SOME false\<close>
ML_val \<open>Tutorial_2x2a () = SOME true\<close>
ML_val \<open>Tutorial_2x2b () = SOME true\<close>
ML_val \<open>broadcast_test () = SOME true\<close>
ML_val \<open>broadcast_test2 () = SOME false\<close>
text \<open>E<> PURI_test.interval\<close>
ML_val \<open>PM_Test_1 () = SOME true\<close>
text \<open>E<> PURI_test.URI_fail\<close>
ML_val \<open>PM_Test_2 () = SOME false\<close>
text \<open>E<> Pvv.two_a\<close>
ML_val \<open>PM_Test_3 () = SOME true\<close>
text \<open>E<> Pvv.LRI_fail\<close>
ML_val \<open>PM_Test_4 () = SOME false\<close>

end