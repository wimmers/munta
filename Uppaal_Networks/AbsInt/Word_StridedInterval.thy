theory Word_StridedInterval
  imports Word OptionLattice
begin

subsection\<open>Strided Intervals\<close>

text\<open>
Intermediate-representation recovery from low-level code
Reps, Thomas and Balakrishnan, Gogul and Lim, Junghee
\<close>

text\<open>
Strided intervals defined as stride-1, lower, upper-lower.
- stride-1 to avoid modulo by 0
- upper-lower to avoid upper < lower
\<close>
datatype strided_interval = StridedInterval nat int nat

fun stride :: "strided_interval \<Rightarrow> nat" where
  "stride (StridedInterval s _ _) = Suc s"

fun lower :: "strided_interval \<Rightarrow> int" where
  "lower (StridedInterval s l _) = l"

fun upper :: "strided_interval \<Rightarrow> int" where
  "upper (StridedInterval s l e) = l + int e"

lemma upper_lower: "lower a \<le> upper a"
  by (metis lower.simps upper.elims zle_iff_zadd)

lemma strided_interval_eqI: "stride a = stride b \<Longrightarrow> lower a = lower b \<Longrightarrow> upper a = upper b \<Longrightarrow> a = b"
proof -
  assume "stride a = stride b" "lower a = lower b" "upper a = upper b"
  moreover from this obtain as al ae bs bl be where "a = StridedInterval as al ae" "b = StridedInterval bs bl be"
    using strided_interval.exhaust by meson
  ultimately show "a = b" by simp
qed

fun \<gamma>_strided_interval :: "strided_interval \<Rightarrow> int set" where
  "\<gamma>_strided_interval i = {x. lower i \<le> x \<and> x \<le> upper i \<and> x mod int (stride i) = 0}"

fun round_up :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "round_up s v = (let m = v mod (int (Suc s)) in if m = 0 then v else v + int (Suc s) - m)"

lemma round_up:
  assumes
    "x mod (int (Suc s)) = 0"
    "x \<ge> v"
  shows
    "x \<ge> round_up s v"
proof (cases "v mod (int (Suc s)) = 0")
  case True
  then show ?thesis using assms by simp
next
  case False
  from False have round: "round_up s v = v + int (Suc s) - (v mod (int (Suc s)))" by simp
  from False have greater: "x > v" by (smt assms(1) assms(2))
  hence "x - 1 \<ge> v" using zle_diff1_eq by blast
  have "(x - 1) mod (int (Suc s)) = int s" sorry
(*  hence "int (Suc s) - (v mod (int (Suc s))) \<le> x - v"*)
  then show ?thesis using assms round by linarith
qed

fun strided_interval_pack :: "strided_interval \<Rightarrow> strided_interval" where
  "strided_interval_pack (StridedInterval s l e) =
    (let lmod = l mod (int s);
         nl = if lmod = 0 then l else l + int s - lmod;
         u = l + (int e);
         nu = u - (u mod (int s));
         ne = nat (nu - nl)
     in StridedInterval s nl ne)"

lemma strided_interval_pack_preserve: "\<gamma>_strided_interval (strided_interval_pack a) = \<gamma>_strided_interval a"
proof -
  obtain s l e where split: "a = StridedInterval s l e" using strided_interval.exhaust by blast
  let ?packed = "strided_interval_pack (StridedInterval s l e)"
  obtain ps pl pe where psplit: "?packed = StridedInterval ps pl pe" using strided_interval.exhaust by blast
  have s: "ps = s" using psplit by (metis stride.simps strided_interval_pack.simps)
  let ?lmod = "l mod (int s)"
  have l: "pl = (if ?lmod = 0 then l else l + int s - ?lmod)" using psplit by (simp; unfold Let_def; auto)
  let ?u = "l + (int e)"
  let ?pu = "?u - (?u mod (int s))"
  have e: "pe = nat (?pu - pl)" using psplit by (simp; unfold Let_def; auto)
  have "\<gamma>_strided_interval (?packed) = \<gamma>_strided_interval (StridedInterval s l e)"
  proof (intro Set.equalityI Set.subsetI, goal_cases)
    case (1 x)
    have "x mod (int s) = 0" using 1 psplit s by force
    have "l \<le> x" using 1 psplit sorry
    moreover have "x \<le> ?u" sorry
    ultimately show ?case using 1 psplit s by auto
  next
    case (2 x)
    then show ?case sorry
  qed
  from this split show ?thesis by simp
qed

fun strided_interval_contains :: "strided_interval \<Rightarrow> int \<Rightarrow> bool" where
  "strided_interval_contains i x \<longleftrightarrow> lower i \<le> x \<and> x \<le> upper i \<and> x mod int (stride i) = 0"

fun strided_interval_make :: "int \<Rightarrow> strided_interval" where
  "strided_interval_make v = StridedInterval (nat (abs v)) v 0"

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
  by (intro Set.equalityI Set.subsetI; simp)

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
           u = (max (upper a) (upper b)) in
       StridedInterval (gcd (stride a) (stride b)) l (nat (u - l)))"
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
  show ?case by (simp; unfold Let_def; auto)
next
  case (6 y x)
  show ?case by (simp; unfold Let_def; auto)
next
  case (7 y x z)
  from 7 have "stride (y \<squnion> z) mod stride x = 0" by (simp; unfold Let_def; auto)
  moreover from 7 have lower: "lower x \<le> lower (y \<squnion> z)" by (simp; unfold Let_def; auto)
  moreover from 7 have "upper (y \<squnion> z) \<le> upper x"
  proof -
    let ?l = "min (lower y) (lower z)"
    let ?u = "max (upper y) (upper z)"
    let ?e = "nat (?u - ?l)"
    have "upper (y \<squnion> z) = ?l + int ?e" by (metis sup_strided_interval.simps upper.simps)
    hence "upper (y \<squnion> z) = ?u" using upper_lower by (smt nat_0_le)
    thus ?thesis using 7 7 by auto
  qed
  ultimately show ?case by simp
qed
end

lemma \<gamma>_strided_interval_mono: assumes "x \<le> y" shows "\<gamma>_strided_interval x \<le> \<gamma>_strided_interval y"
proof (intro Set.subsetI, goal_cases)
  case (1 v)
  hence p: "lower x \<le> v \<and> v \<le> upper x \<and> v mod int (stride x) = 0" by simp
  from assms have "int (stride x) mod int (stride y) = 0" by auto
  from p this have "v mod int (stride y) = 0" by auto
  from p this show ?case using assms by simp
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
    then show ?thesis by (cases aa; simp)
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