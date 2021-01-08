theory Abs_Word
  imports Abs_Int Abs_Bool Toption
begin

section \<open>Abstraction of Machine Words\<close>
text \<open>More specifically, abstraction for @{type val}, @{type reg} and @{type addr}\<close>

class absword = semilattice_sup + order_bot + order_top

fun word_of_gen :: "(int \<Rightarrow> 'a::absword) \<Rightarrow> power_bool \<Rightarrow> 'a" where
  "word_of_gen make BTrue = make 1" |
  "word_of_gen make BFalse = make 0" |
  "word_of_gen make BBoth = make 0 \<squnion> make 1"

locale Abs_Word =
fixes \<gamma>_word :: "('a::absword) \<Rightarrow> int set"
  and contains :: "'a \<Rightarrow> int \<Rightarrow> bool"
  and make :: "int \<Rightarrow> 'a"
  and concretize :: "'a \<Rightarrow> int set toption" \<comment> \<open>Finite overapproximation of \<gamma>_word if existing\<close>
  and aplus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and lt :: "'a \<Rightarrow> 'a \<Rightarrow> power_bool"
  and le :: "'a \<Rightarrow> 'a \<Rightarrow> power_bool"
  and eq :: "'a \<Rightarrow> 'a \<Rightarrow> power_bool"
assumes mono_gamma: "a \<le> b \<Longrightarrow> \<gamma>_word a \<le> \<gamma>_word b"
  and gamma_Top[simp]: "\<gamma>_word \<top> = \<top>"
  and contains_correct: "contains a x \<longleftrightarrow> x \<in> \<gamma>_word a"
  and make_correct: "v \<in> \<gamma>_word (make v)"
  and concretize_correct: "concretize a = Minor vs \<Longrightarrow> \<gamma>_word a \<subseteq> vs"
  and concretize_finite: "concretize a = Minor vs \<Longrightarrow> finite vs"
  and plus_correct: "x \<in> \<gamma>_word a \<Longrightarrow> y \<in> \<gamma>_word b \<Longrightarrow> (x + y) \<in> \<gamma>_word (aplus a b)"
  and lt_correct: "(if \<forall>x y. x \<in> \<gamma>_word a \<longrightarrow> y \<in> \<gamma>_word b \<longrightarrow> x < y then BTrue
                    else if \<exists>x y. x \<in> \<gamma>_word a \<and> y \<in> \<gamma>_word b \<and> x < y then BBoth
                    else BFalse) \<le> lt a b"
  and le_correct: "(if \<forall>x y. x \<in> \<gamma>_word a \<longrightarrow> y \<in> \<gamma>_word b \<longrightarrow> x \<le> y then BTrue
                    else if \<exists>x y. x \<in> \<gamma>_word a \<and> y \<in> \<gamma>_word b \<and> x \<le> y then BBoth
                    else BFalse) \<le> le a b"
  and eq_correct: "(if \<forall>x y. x \<in> \<gamma>_word a \<longrightarrow> y \<in> \<gamma>_word b \<longrightarrow> x = y then BTrue
                    else if \<exists>x y. x \<in> \<gamma>_word a \<and> y \<in> \<gamma>_word b \<and> x = y then BBoth
                    else BFalse) \<le> eq a b"
begin

definition[simp]: "word_of \<equiv> word_of_gen make"

lemma word_of:
  assumes "x \<in> \<gamma>_power_bool b"
  shows "int_of x \<in> \<gamma>_word (word_of b)"
proof (cases b)
  case BTrue
  then show ?thesis using assms int_of_def by (simp add: make_correct)
next
  case BFalse
  then show ?thesis using assms int_of_def by (simp add: make_correct)
next
  case BBoth
  then show ?thesis
  proof (cases x)
    case True then show ?thesis by (simp; metis BBoth in_mono int_of_def make_correct mono_gamma sup_ge2 word_of_gen.simps(3))
  next
    case False then show ?thesis by (simp; metis BBoth in_mono int_of_def make_correct mono_gamma sup.cobounded1 word_of_gen.simps(3))
  qed
qed

end

type_synonym 'a abs_word_args = "
  ('a \<Rightarrow> int set) *
  ('a \<Rightarrow> int \<Rightarrow> bool) *
  (int \<Rightarrow> 'a) *
  ('a \<Rightarrow> int set toption) *
  ('a \<Rightarrow> 'a \<Rightarrow> 'a) *
  ('a \<Rightarrow> 'a \<Rightarrow> power_bool) *
  ('a \<Rightarrow> 'a \<Rightarrow> power_bool) *
  ('a \<Rightarrow> 'a \<Rightarrow> power_bool)"

end