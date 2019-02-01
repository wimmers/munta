session "TA_Library" = "Refine_Imperative_HOL" +
  theories
    "library/More_Methods"
    "library/Abstract_Term"
    "library/Instantiate_Existentials"
    "library/Tracing"
    "library/Printing"
    "library/Error_List_Monad"


(* Use this to get document output for the abstract formalization of Reachability Checking *)
session "TA" = "TA_Library" +
(*
  options
    [document = pdf, document_output = "output",
     document_variants = "abstract_reachability_proofs:abstract_reachability=/proof,/ML"]
*)
  theories [document = false]
    Main HOL.Real Floyd_Warshall FW_Code
  theories
    Normalized_Zone_Semantics
(*
  document_files
    "root.bib" "wasysym.sty"
  document_files (in "document/abstract_reachability")
    "root.tex"
*)

session "TA_Impl" = "TA" +
  sessions
    Show
  theories [document = false]
    Refine_Imperative_HOL.IICF
    "HOL-Library.IArray"
  theories
    Normalized_Zone_Semantics_Impl_Refine

(*
session "TA_Impl_Calc_Prereq" = "TA_Impl" +
  sessions
    Gabow_SCC
  theories [document = false]
    "Gabow_SCC.Gabow_SCC_Code"

session "TA_Impl_Refine_Calc_Prereq" = "TA_Impl" +
  theories
    UPPAAL_State_Networks_Impl

session "TA_All_Pre" = "TA_Impl_Refine_Calc_Prereq" +
  theories [document = false]
    "library/ML_Util"
  theories
    "Uppaal_Networks/UPPAAL_State_Networks_Impl_Refine"
*)

session "TA_Byte_Code" = "TA_Impl" +
  theories UPPAAL_Model_Checking

(* Use this to get document output for the implementation of Reachability Checking *)
session "TA_All" = "TA_Impl" +
  options
    [document = pdf, document_output = "output",
     document_variants = "model_checking_proofs:model_checking=/proof,/ML"]
  theories [document = false]
    Refine_Imperative_HOL.IICF
    TA.Instantiate_Existentials
    TA.Sequence
    TA.Stream_More
    "HOL-Library.IArray"
  theories
    "Uppaal_Networks/UPPAAL_State_Networks_Impl_Refine"
    TA.Simulation_Graphs
    TA_More
    Infinite_TA_Runs
    "Worklist_Algorithms/Worklist_Subsumption_Impl1"
    "Worklist_Algorithms/Worklist_Subsumption_Multiset"
    (* Worklist_Subsumption_PW_Multiset *)
  document_files (in "document/model_checking")
    "root.tex"

session "TA_Code" = "TA_Byte_Code" +
  sessions
    Gabow_SCC
  theories [document = false]
    Export_Checker
