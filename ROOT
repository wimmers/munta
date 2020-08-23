session "TA_Library" in "library" = "Refine_Imperative_HOL" +
  sessions
    Transition_Systems_and_Automata
    LTL_Master_Theorem
  theories
    Syntax_Bundles
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
    Subsumption_Graphs

session DBM in DBM = TA_Library +
  theories
    Floyd_Warshall
    FW_Code
    DBM_Operations
    DBM_Normalization
    DBM_Constraint_Systems
    DBM_Operations_Impl_Refine
    FW_More

session TA in TA = DBM +
  options
    [document = pdf, document_output = "output",
     document_variants = "abstract_reachability_proofs:abstract_reachability=/proof,/ML"]
  theories [document = false]
    Main HOL.Real
  theories
    Normalized_Zone_Semantics
  theories [document = false]
    TA_More
  document_files
    "root.bib" "wasysym.sty"
  document_files (in "document/abstract_reachability")
    "root.tex"

session Worklist_Algorithms in Worklist_Algorithms = TA_Library +
  theories
    Worklist_Subsumption_Impl1
    Unified_PW_Impl
    Liveness_Subsumption_Impl
    Leadsto_Impl
    Worklist_Subsumption_Multiset

session TA_Impl in TA_Impl = TA +
  sessions
    Show
    Worklist_Algorithms
  theories [document = false]
    Refine_Imperative_HOL.IICF
    "HOL-Library.IArray"
  theories
    Normalized_Zone_Semantics_Impl_Refine
    Normalized_Zone_Semantics_Impl_Extra

session Certification in Certification = TA_Impl +
  options
    [quick_and_dirty]
  sessions
    Graph_Theory
  theories
    Lasso_Freeness_Certificates_Complete
    Unreachability_Certification
    Unreachability_Certification2
    Simulation_Graphs2
    TA_Simulation
    Normalized_Zone_Semantics_Certification_Impl
    Normalized_Zone_Semantics_Certification_Impl2

session Networks in Networks = TA_Impl +
  theories
    State_Networks

session Uppaal_Networks in Uppaal_Networks = Networks +
  directories
    AbsInt
  theories
    UPPAAL_Model_Checking

session Simple_Networks in Simple_Networks = Uppaal_Networks +
  sessions
    FinFun
  theories
    Simple_Network_Language_Model_Checking

session Deadlock in Deadlock = Uppaal_Networks +
  theories
    Deadlock_Checking

session Parsing in Parsing = Certification_Monads +
  sessions
    "HOL-Library"
    Show
  theories
    JSON_Parsing

session TA_Code in Model_Checking = Simple_Networks +
  sessions
    Certification_Monads
    FinFun
    Gabow_SCC
    Deadlock
    Parsing
  theories
    Simple_Network_Language_Export_Code
    Shortest_SCC_Paths

session TA_Certificates in Certificate_Checking = TA_Code +
  options
    [quick_and_dirty]
  theories
    Simple_Network_Language_Certificate_Code