theory AbsInt_Test
  imports AbsInt_Test_Setup
begin

ML\<open>
val _ = absint_benchmark "benchmarks/critical_01.munta" entry_default 100
\<close>

end