theory Word
  imports AbsInt PowerBool
begin

section \<open>Abstraction of Machine Words\<close>
text \<open>More specifically, abstraction for @{type val}, @{type reg} and @{type addr}\<close>

class absword = bounded_semilattice_sup_bot + order_top

locale AbsWord =
fixes \<gamma>_word :: "('a::absword) \<Rightarrow> int set"
  and aplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and contains :: "'a \<Rightarrow> int \<Rightarrow> bool"
assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma>_word a \<le> \<gamma>_word b"
  and gamma_Top[simp]: "\<gamma>_word \<top> = UNIV"
  and plus_correct: "x \<in> \<gamma>_word a \<Longrightarrow> y \<in> \<gamma>_word b \<Longrightarrow> (x + y) \<in> \<gamma>_word (aplus a b)"
  and contains_correct: "contains a x \<longleftrightarrow> x \<in> \<gamma>_word a"

end