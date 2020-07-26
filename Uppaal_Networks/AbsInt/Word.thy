theory Word
  imports AbsInt
begin

section \<open>Abstraction of Machine Words\<close>
text \<open>More specifically, abstraction for @{type val}, @{type reg} and @{type addr}\<close>

class absword = complete_lattice

locale AbsWord =
fixes \<gamma>_word :: "('a::absword) \<Rightarrow> int set"
  assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma>_word a \<le> \<gamma>_word b"
  and gamma_Top[simp]: "\<gamma>_word \<top> = UNIV"

end