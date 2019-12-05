session "TA_Library" in "library" = "Refine_Imperative_HOL" +
  sessions
    Transition_Systems_and_Automata
    LTL_Master_Theorem
  theories
    ML_Util
    More_Methods
    Abstract_Term
    Instantiate_Existentials
    Reordering_Quantifiers
    More_List
    Stream_More
    Bijective_Embedding
    Tracing
    Printing
    Trace_Timing
    Error_List_Monad
    Imperative_Loops
    Temporal_Logics
    CTL

(* Use this to get document output for the abstract formalization of reachability checking *)
session "TA" = "TA_Library" +
  options
    [document = pdf, document_output = "output",
     document_variants = "abstract_reachability_proofs:abstract_reachability=/proof,/ML"]
  theories [document = false]
    Main HOL.Real Floyd_Warshall FW_Code
  theories
    Normalized_Zone_Semantics
  document_files
    "root.bib" "wasysym.sty"
  document_files (in "document/abstract_reachability")
    "root.tex"

session "TA_Impl" = "TA" +
  sessions
    Show
  theories [document = false]
    Refine_Imperative_HOL.IICF
    "HOL-Library.IArray"
  theories
    Normalized_Zone_Semantics_Impl_Refine

session "TA_Byte_Code" = "TA_Impl" +
  theories UPPAAL_Model_Checking

(* Use this to get document output for the implementation of reachability checking with byte code *)
session "TA_All" = "TA_Impl" +
  options
    [document = pdf, document_output = "output",
     document_variants = "model_checking_proofs:model_checking=/proof,/ML"]
  sessions
    TA_Byte_Code
  theories [document = false]
    Refine_Imperative_HOL.IICF
    TA_Library.Instantiate_Existentials
    TA_Library.Stream_More
    "HOL-Library.IArray"
  theories
    TA_Byte_Code.UPPAAL_State_Networks_Impl_Refine
    TA.Simulation_Graphs
    TA_More
    Infinite_TA_Runs
    "Worklist_Algorithms/Worklist_Subsumption_Impl1"
    "Worklist_Algorithms/Worklist_Subsumption_Multiset"
  document_files (in "document/model_checking")
    "root.tex"

session "TA_Code" = "TA_Byte_Code" +
  sessions
    Certification_Monads
    FinFun
    Gabow_SCC
  theories
    "Simple_Networks/Simple_Network_Language_Export_Code"

session TA_Certificates = "TA_Code" +
  options
    [quick_and_dirty]
  theories
    "Simple_Networks/Simple_Network_Language_Certificate_Code"
