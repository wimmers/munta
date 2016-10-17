theory Reachability_Benchmarks
  imports Normalized_Zone_Semantics_Impl_Refine
begin

definition
  "test \<equiv>
  check_and_verify 1 1 [0,2] [[EQ 1 2]] [[([], [], 0)]] [0]"

definition
  "test2 \<equiv>
  check_and_verify 3 2 [0, 2, 10] [[LE 2 10], [], []]
    [[([], [1], 1), ([GT 2 5], [], 2)], [([LE 1 2], [], 0)], []] [2]"

ML_val \<open>@{code test} ()\<close>

ML_val \<open>@{code test2} ()\<close>

export_code open check_and_verify in SML_imp module_name Reachability_Checker
  file "Reachability_Checker.ml"

ML_file "Reachability_Checker.ml"

ML \<open>
  open Reachability_Checker;;
\<close>

ML \<open>
  fun map_acconstraint f g = fn
    LT (a, b) => LT (f a, g b) |
    LE (a, b) => LE (f a, g b) |
    EQ (a, b) => EQ (f a, g b) |
    GE (a, b) => GE (f a, g b) |
    GT (a, b) => GT (f a, g b)
\<close>

ML \<open>
  fun check_and_verify n m k inv trans final =
    let
      val k = map Nat k;
      val map_constraint = map (map_acconstraint Nat Int_of_integer);
      val inv = map map_constraint inv;
      val trans = map (map (fn (g, (r, l)) => (map_constraint g, (map Nat r, Nat l)))) trans;
      val final = map Nat final;
    in
      Reachability_Checker.check_and_verify (Nat n) (Nat m) k inv trans final
    end;
    
\<close>

ML_val \<open>
  check_and_verify 3 2 [0, 2, 10] [[LE (2, 10)], [], []]
    [[([], ([1], 1)), ([GT (2, 5)], ([], 2))], [([LE (1, 2)], ([], 0))], []] [2]
  ()\<close>

ML_file "~/UPPAAL/test_ta/Test1a.ml"

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