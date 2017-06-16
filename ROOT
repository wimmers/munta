session "TA" = "Refine_Imperative_HOL" +
  theories [document = false]
    Main Real
  theories
    Normalized_Zone_Semantics

session "TA_Impl" = "TA" +
  theories [document = false]
    IICF
    "~~/src/HOL/Library/IArray"
  theories
    Normalized_Zone_Semantics_Impl_Refine

session "TA_Impl_Calc_Prereq" = "TA_Impl" +
  theories [document = false]
    "$AFP/Gabow_SCC/Gabow_SCC_Code"

session "TA_Impl_Refine_Calc_Prereq" = "TA_Impl" +
  theories
    UPPAAL_State_Networks_Impl

session "TA_All" = "TA_Impl" +
  options [document = pdf, document_output = "output"]
  theories
    UPPAAL_State_Networks_Impl_Refine
    Infinite_TA_Runs
    Simulation_Graphs
    TA_More
    Worklist_Subsumption_Impl1
    Worklist_Subsumption_Multiset
    (* Worklist_Subsumption_PW_Multiset *)
  document_files
    "root.tex"
    "root.bib"

session "TA_Code" = "TA_Impl_Refine_Calc_Prereq" +
  theories [document = false]
    Export_Checker