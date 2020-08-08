theory Word_StridedInterval
  imports Word OptionLattice
begin

subsection\<open>Strided Intervals\<close>

text\<open>
Intermediate-representation recovery from low-level code
Reps, Thomas and Balakrishnan, Gogul and Lim, Junghee
\<close>

text\<open>
Strided intervals defined as stride-1, lower/stride, (upper-lower)/stride.
- stride-1 to avoid modulo by 0
- upper-lower to avoid upper < lower
- /stride for uniqueness
\<close>
datatype strided_interval = StridedInterval nat int nat

fun stride :: "strided_interval \<Rightarrow> nat" where
  "stride (StridedInterval s _ _) = Suc s"

fun lower :: "strided_interval \<Rightarrow> int" where
  "lower (StridedInterval s l _) = l * int (Suc s)"

fun upper :: "strided_interval \<Rightarrow> int" where
  "upper (StridedInterval s l e) = (l + int e) * int (Suc s)"

lemma upper_lower: "lower i \<le> upper i"
proof -
  obtain s l e where split: "i = StridedInterval s l e" using strided_interval.exhaust by blast
  have "l * int s \<le> (l + int e) * int s" by (simp add: mult_right_mono)
  thus ?thesis using split by simp
qed

lemma stride_pos: "stride i > 0"
proof -
  obtain s l e where "i = StridedInterval s l e" using strided_interval.exhaust by blast
  thus ?thesis by simp
qed

lemma strided_interval_eqI: "stride a = stride b \<Longrightarrow> lower a = lower b \<Longrightarrow> upper a = upper b \<Longrightarrow> a = b"
proof -
  assume "stride a = stride b" "lower a = lower b" "upper a = upper b"
  moreover obtain as al ae bs bl be where split: "a = StridedInterval as al ae" "b = StridedInterval bs bl be"
    using strided_interval.exhaust by meson
  ultimately show "a = b" by simp
qed

fun \<gamma>_strided_interval :: "strided_interval \<Rightarrow> int set" where
  "\<gamma>_strided_interval i = {x. lower i \<le> x \<and> x \<le> upper i \<and> int (stride i) dvd x}"

fun strided_interval_contains :: "strided_interval \<Rightarrow> int \<Rightarrow> bool" where
  "strided_interval_contains i x \<longleftrightarrow> lower i \<le> x \<and> x \<le> upper i \<and> x mod int (stride i) = 0"

fun strided_interval_make :: "int \<Rightarrow> strided_interval" where
  "strided_interval_make v =
    (if v = 0
     then StridedInterval 1 0 0
     else StridedInterval (nat (abs v) - 1) (if v < 0 then -1 else 1) 0)"

definition "strided_interval_concretize_max \<equiv> 16" \<comment> \<open>Hardcoded, could be made nicer\<close>
fun strided_interval_concretize :: "strided_interval \<Rightarrow> int set toption" where
  "strided_interval_concretize i = Top" (* TODO *)

fun strided_interval_aplus :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> strided_interval" where
  "strided_interval_aplus a b = undefined"

fun strided_interval_lt :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> power_bool" where
  "strided_interval_lt a b = undefined"

fun strided_interval_le :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> power_bool" where
  "strided_interval_le a b = undefined"

fun strided_interval_eq :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> power_bool" where
  "strided_interval_eq a b = undefined"

lemma strided_interval_make_exact: "\<gamma>_strided_interval (strided_interval_make v) = {v}"
  by (intro Set.equalityI Set.subsetI; cases "v = 0"; auto)

instantiation strided_interval :: semilattice_sup
begin
  fun less_eq_strided_interval :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> bool" where
    "less_eq_strided_interval a b \<longleftrightarrow>
      stride a mod stride b = 0 \<and> lower b \<le> lower a \<and> upper a \<le> upper b"

  fun less_strided_interval :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> bool" where
    "less_strided_interval a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

  fun sup_strided_interval :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> strided_interval" where
    "sup_strided_interval a b =
      (let l = (min (lower a) (lower b));
           u = (max (upper a) (upper b));
           s = gcd (stride a) (stride b) in
       StridedInterval (s - 1) (l div (int s)) ((nat (u - l)) div s))"

  lemma sup_stride: "stride (a \<squnion> b) = gcd (stride a) (stride b)"
    by (simp; unfold Let_def; simp add: stride_pos)

  lemma dvd_lower_ab: "(int (gcd (stride a) (stride b))) dvd (min (lower a) (lower b))"
  proof -
    let ?s = "gcd (stride a) (stride b)"
    let ?l = "min (lower a) (lower b)"
    show ?thesis
    proof (cases "lower a < lower b")
      case True
      hence "?l = lower a" by simp
      hence "int (stride a) dvd ?l" by (metis dvd_def lower.simps mult.commute stride.elims)
      then show ?thesis by auto
    next
      case False
      hence "?l = lower b" by simp
      hence "int (stride b) dvd ?l" by (metis dvd_def lower.simps mult.commute stride.elims)
      then show ?thesis by auto
    qed
  qed

  lemma sup_lower: "lower (a \<squnion> b) = min (lower a) (lower b)"
  proof -
    let ?s = "gcd (stride a) (stride b)"
    let ?l = "min (lower a) (lower b)"
    have "lower (a \<squnion> b) = (?l div (int ?s)) * (int ?s)"
      using int_ops(6) by (simp; unfold Let_def; simp)
    moreover have "(int ?s) dvd ?l" by (rule dvd_lower_ab)
    ultimately show ?thesis by auto
  qed

  lemma sup_upper: "upper (a \<squnion> b) = max (upper a) (upper b)"
  proof -
    let ?s = "gcd (stride a) (stride b)"
    let ?u = "max (upper a) (upper b)"
    have udiv: "(int ?s) dvd ?u"
    proof (cases "upper a < upper b")
      case True
      hence "?u = upper b" by simp
      hence "int (stride b) dvd ?u" by (metis dvd_def upper.simps mult.commute stride.elims)
      then show ?thesis by auto
    next
      case False
      hence "?u = upper a" by simp
      hence "int (stride a) dvd ?u" by (metis dvd_def upper.simps mult.commute stride.elims)
      then show ?thesis by auto
    qed
    moreover have "upper (a \<squnion> b) = (?u div (int ?s)) * (int ?s)"
    proof -
      let ?l = "min (lower a) (lower b)"
      have ldiv: "(int ?s) dvd ?l" by (rule dvd_lower_ab)
      obtain s l e where split: "a \<squnion> b = StridedInterval s l e" using strided_interval.exhaust by blast
      have lower_l: "lower (a \<squnion> b) = ?l" using sup_lower split by blast
      have lower_suc: "lower (a \<squnion> b) = l * int (Suc s)" using split by simp
      have "stride (a \<squnion> b) = Suc s" using split by simp
      hence "Suc s = ?s" using sup_stride by metis
      hence lower_complete: "lower (a \<squnion> b) = l * int ?s" using lower_suc by simp
      from split have "e = ((nat (?u - ?l)) div ?s)" by (simp; unfold Let_def; simp)
      hence "upper (a \<squnion> b) = (l + int ((nat (?u - ?l)) div ?s)) * int (?s)" using split sup_stride by (metis stride.simps upper.simps)
      hence "upper (a \<squnion> b) = l * int ?s + (int ((nat (?u - ?l)) div ?s)) * int ?s" using distrib_right by auto
      hence "upper (a \<squnion> b) = l * int ?s + ((?u - ?l) div int ?s) * int ?s" by (smt nat_0_le upper_lower zdiv_int)
      hence "upper (a \<squnion> b) = l * int ?s + (?u div int ?s - ?l div int ?s) * int ?s" by (simp add: dvd_lower_ab udiv)
      hence "upper (a \<squnion> b) = l * int ?s + (?u div int ?s) * int ?s - (?l div int ?s) * int ?s" using int_distrib(3) by auto
      hence "upper (a \<squnion> b) = l * int ?s + (?u div int ?s) * int ?s - ?l" using ldiv by auto
      hence "upper (a \<squnion> b) = ?l + (?u div int ?s) * int ?s - ?l" using lower_l lower_complete by simp
      thus ?thesis by (simp add: udiv)
    qed
    ultimately show ?thesis by auto
  qed

instance proof (standard, goal_cases)
  case (1 x y)
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y z)
  then show ?case by auto
next
  case (4 x y)
  from 4 have "stride x = stride y" by auto
  moreover from 4 have "lower x = lower y" by simp
  moreover from 4 have "upper x = upper y" by simp
  ultimately show ?case by (rule strided_interval_eqI)
next
  case (5 x y)
  show ?case using sup_stride sup_lower sup_upper by simp
next
  case (6 y x)
  show ?case using sup_stride sup_lower sup_upper by simp
next
  case (7 y x z)
  from 7 have "stride (y \<squnion> z) mod stride x = 0" using sup_stride by auto
  moreover from 7 have lower: "lower x \<le> lower (y \<squnion> z)" using sup_lower by simp
  moreover from 7 have "upper (y \<squnion> z) \<le> upper x" using sup_upper by simp
  ultimately show ?case by simp
qed
end

lemma \<gamma>_strided_interval_mono: assumes "x \<le> y" shows "\<gamma>_strided_interval x \<le> \<gamma>_strided_interval y"
proof (intro Set.subsetI, goal_cases)
  case (1 v)
  hence p: "lower x \<le> v \<and> v \<le> upper x \<and> v mod int (stride x) = 0" by simp
  from assms have "int (stride x) mod int (stride y) = 0" by auto
  from p this have "v mod int (stride y) = 0" by auto
  from p this show ?case using assms by auto
qed

type_synonym strided_interval_word = "strided_interval toption option"

global_interpretation WordStridedInterval: AbsWord
  where \<gamma>_word = "\<gamma>_option (\<gamma>_toption \<gamma>_strided_interval)"
    and contains = "option_contains (toption_contains strided_interval_contains)"
    and make = "Some \<circ> Minor \<circ> strided_interval_make"
    and concretize = "option_concretize (toption_concretize strided_interval_concretize)"
    and aplus = "option_aplus (toption_aplus strided_interval_aplus)"
    and lt = "option_lt (toption_lt strided_interval_lt)"
    and le = "option_le (toption_le strided_interval_le)"
    and eq = "option_eq (toption_eq strided_interval_eq)"
proof (standard, goal_cases)
  case (1 a b)
  then show ?case using \<gamma>_option_mono \<gamma>_toption_mono mono_def \<gamma>_strided_interval_mono 1 by blast
next
  case 2
  then show ?case by simp
next
  case (3 a x)
  then show ?case
  proof (cases a)
    case (Some aa)
    then show ?thesis by (cases aa; auto)
  qed simp
next
  case (4 v)
  then show ?case by simp
next
  case (5 a vs)
  from 5 obtain aa where "a = Some (Minor aa)" by (metis option.exhaust option_concretize.simps toption.distinct(1) toption_bind.elims toption_concretize_def)
  then show ?case using 5 by auto
next
  case (6 a vs)
  then show ?case by (metis option_concretize.elims strided_interval_concretize.simps toption.distinct(1) toption_bind.elims toption_concretize_def)
next
  case (7 x a y b)
  then show ?case sorry
next
  case (8 a b)
  then show ?case sorry
next
  case (9 a b)
  then show ?case sorry
next
  case (10 a b)
  then show ?case sorry
qed

end