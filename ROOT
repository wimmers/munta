(*
session "Timed_Automata" = "HOL" +
  options [document = pdf, document_output = "output"]
  theories [document = false]
    Main
  theories
    Timed_Automata Misc Closure Floyd_Warshall Paths_Cycles DBM_Operations Normalized_Zone_Semantics
  document_files
    "root.tex"
    "root.bib"
*)

session "TA" = "Refine_Imperative_HOL" +
  theories [document = false]
    Normalized_Zone_Semantics

session "TA_Impl" = "TA" +
  theories [document = false]
    Normalized_Zone_Semantics_Impl_Refine

session "TA_Impl_Calc_Prereq" = "TA_Impl" +
  theories [document = false]
    "$AFP/Gabow_SCC/Gabow_SCC_Code"

session "TA_Impl_Refine_Calc_Prereq" = "TA_Impl" +
  theories [document = false]
    "$AFP/Gabow_SCC/Gabow_SCC_Code"
    UPPAAL_State_Networks_Impl

session "TA_All" = "TA_Impl" +
  theories [document = false]
    UPPAAL_State_Networks_Impl_Refine

session "TA_Code" = "TA_Impl_Refine_Calc_Prereq" +
  theories [document = false]
    UPPAAL_Reachability_Benchmarks

