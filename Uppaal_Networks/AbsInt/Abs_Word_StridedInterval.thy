theory Abs_Word_StridedInterval
  imports Abs_Word OptionLattice
begin

subsection\<open>Strided Intervals\<close>

text\<open>
Intermediate-representation recovery from low-level code
Reps, Thomas and Balakrishnan, Gogul and Lim, Junghee

Strided intervals are commonly denoted as stride[lower, upper]
See @{term \<gamma>_strided_interval} for the semantics.
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

fun is_zero :: "strided_interval \<Rightarrow> bool" where
  "is_zero (StridedInterval s l e) = (l = 0 \<and> e = 0)"

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

lemma lower_inside: "lower i \<in> \<gamma>_strided_interval i"
proof -
  have "int (stride i) dvd lower i" by (metis dvd_def lower.simps mult.commute stride.elims)
  thus ?thesis using upper_lower by simp
qed

lemma upper_inside: "upper i \<in> \<gamma>_strided_interval i"
proof -
  have "int (stride i) dvd upper i" by (metis dvd_def mult.commute stride.simps upper.elims)
  thus ?thesis using upper_lower by simp
qed

lemma is_zero: "is_zero i \<longleftrightarrow> \<gamma>_strided_interval i = {0}"
proof -
  obtain s l e where split: "i = StridedInterval s l e" using strided_interval.exhaust by blast
  show ?thesis
  proof (standard, goal_cases)
    case 1
    have "x \<in> \<gamma>_strided_interval i \<Longrightarrow> x = 0" for x using 1 split by simp
    moreover have "0 \<in> \<gamma>_strided_interval i" using 1 split by simp
    ultimately show ?case by blast
  next
    case 2
    hence "lower i = 0 \<and> upper i = 0" using lower_inside upper_inside by blast
    then show ?case using split by force
  qed
qed

fun strided_interval_make :: "int \<Rightarrow> strided_interval" where
  "strided_interval_make v =
    (if v = 0
     then StridedInterval 0 0 0
     else StridedInterval (nat (abs v) - 1) (if v < 0 then -1 else 1) 0)"

fun strided_interval_concretize :: "nat \<Rightarrow> strided_interval \<Rightarrow> int set toption" where
  "strided_interval_concretize concretize_max (StridedInterval s l e) =
    (if e > concretize_max
     then Top
     else Minor (set (map ((*) (int (Suc s)) \<circ> ((+) l) \<circ> int) [0..<Suc e])))"

fun strided_interval_aplus_nonzero :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> strided_interval" where
  "strided_interval_aplus_nonzero a b =
      (let l = lower a + lower b;
           u = upper a + upper b;
           s = gcd (stride a) (stride b) in
       StridedInterval (s - 1) (l div (int s)) ((nat (u - l)) div s))"

lemma strided_interval_aplus_nonzero:
  assumes
    "x \<in> \<gamma>_strided_interval a"
    "y \<in> \<gamma>_strided_interval b"
  shows
    "x + y \<in> \<gamma>_strided_interval (strided_interval_aplus_nonzero a b)"
proof -
  let ?plused = "strided_interval_aplus_nonzero a b"
  from assms(1) have x: "lower a \<le> x \<and> x \<le> upper a \<and> int (stride a) dvd x" using \<gamma>_strided_interval.simps by blast
  from assms(2) have y: "lower b \<le> y \<and> y \<le> upper b \<and> int (stride b) dvd y" using \<gamma>_strided_interval.simps by blast

  have strideval: "stride ?plused = gcd (stride a) (stride b)" by (simp; unfold Let_def; simp add: stride_pos)

  from strideval have gcd_pos: "gcd (stride a) (stride b) > 0" by (simp add: stride_pos)
  hence gcd_sup: "1 + int (gcd (stride a) (stride b) - Suc 0) = int (gcd (stride a) (stride b))"  by (metis Suc_pred of_nat_Suc)

  have lower_div: "int (gcd (stride a) (stride b)) dvd (lower a + lower b)"
    using dvd_add_left_iff dvd_def gcd_dvdI1 gcd_dvdI2 gcd_int_int_eq lower.simps mult.commute stride.simps strided_interval.exhaust by metis
  hence lowerdiv: "(lower a + lower b) div int (gcd (stride a) (stride b)) * (int (gcd (stride a) (stride b))) = lower a + lower b" by simp
  hence lowerval: "lower ?plused = lower a + lower b" by (simp; unfold Let_def; simp add: gcd_sup)

  have upper_div: "int (gcd (stride a) (stride b)) dvd (upper a + upper b)"
    by (metis dvd_add_left_iff dvd_def gcd_dvdI1 gcd_dvdI2 gcd_int_int_eq mult.commute stride.simps upper.elims)
  have "(lower a + lower b) + (upper a + upper b - (lower a + lower b)) =
    upper a + upper b" by simp
  hence "(lower a + lower b) + (((upper a + upper b - (lower a + lower b)) div (int (gcd (stride a) (stride b))))) * (int (gcd (stride a) (stride b))) =
    upper a + upper b" by (metis dvd_diff dvd_div_mult_self lower_div upper_div)
  hence "(lower a + lower b) + (int (nat (upper a + upper b - (lower a + lower b)) div gcd (stride a) (stride b))) * (int (gcd (stride a) (stride b))) =
    upper a + upper b" using x y zdiv_int by auto
  hence upperval: "upper ?plused = upper a + upper b" by (simp; unfold Let_def; simp add: gcd_sup lowerdiv distrib_right)

  have lower: "lower ?plused \<le> (x + y)" using lowerval x y by linarith
  moreover have upper: "(x + y) \<le> upper ?plused" using upperval x y by linarith
  moreover have stride: "int (stride ?plused) dvd (x + y)" using strideval x y by fastforce
  ultimately show ?thesis by simp
qed

fun strided_interval_aplus :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> strided_interval" where
  "strided_interval_aplus a b =
    (if is_zero a
     then b
     else if is_zero b
     then a
     else strided_interval_aplus_nonzero a b)"

lemma strided_interval_aplus:
  assumes
    "x \<in> \<gamma>_strided_interval a"
    "y \<in> \<gamma>_strided_interval b"
  shows
    "x + y \<in> \<gamma>_strided_interval (strided_interval_aplus a b)"
proof (cases "is_zero a")
  case True
  then show ?thesis using assms is_zero by auto
next
  case False
  then show ?thesis using assms
  proof (cases "is_zero b")
    case True
    then show ?thesis using assms is_zero by auto
  next
    assume bFalse: "\<not> is_zero b"
    then show ?thesis using False assms strided_interval_aplus_nonzero by auto
  qed
qed

fun strided_interval_lt :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> power_bool" where
  "strided_interval_lt a b =
    (if upper a < lower b
     then BTrue
     else if upper b \<le> lower a
     then BFalse
     else BBoth)"

fun strided_interval_le :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> power_bool" where
  "strided_interval_le a b =
    (if upper a \<le> lower b
     then BTrue
     else if upper b < lower a
     then BFalse
     else BBoth)"

fun strided_interval_eq :: "strided_interval \<Rightarrow> strided_interval \<Rightarrow> power_bool" where
  "strided_interval_eq a b =
    (if upper a \<le> lower b \<and> upper b \<le> lower a
     then BTrue
     else if upper a < lower b \<or> upper b < lower a \<comment> \<open>a case like 2[0,2] 1[1,1] will currently be overapproximated by BBoth\<close>
     then BFalse
     else BBoth)"

lemma strided_interval_lt: "strided_interval_lt a b =
                            (if \<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x < y then BTrue
                             else if \<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x < y then BBoth
                             else BFalse)"
proof (cases "\<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x < y")
  case True
  then have "strided_interval_lt a b = BTrue" using lower_inside upper_inside by auto
  then show ?thesis using True by simp
next
  case False
  then show ?thesis
  proof (cases "\<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x < y")
    case True
    thus ?thesis using False by auto
  next
    case False
    thus ?thesis by (smt lower_inside strided_interval_lt.simps upper_inside)
  qed
qed

lemma strided_interval_lt_over: "(if \<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x < y then BTrue
                             else if \<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x < y then BBoth
                             else BFalse) \<le> strided_interval_lt a b" using strided_interval_lt by simp

lemma strided_interval_le: "strided_interval_le a b = (if \<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x \<le> y then BTrue
                             else if \<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x \<le> y then BBoth
                             else BFalse)"
proof (cases "\<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x \<le> y")
  case True
  then have "strided_interval_le a b = BTrue" using lower_inside upper_inside
    using strided_interval_le.simps by presburger
  then show ?thesis using True by presburger
next
  case False
  then show ?thesis
  proof (cases "\<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x \<le> y")
    case True
    thus ?thesis using False by auto
  next
    case False
    thus ?thesis by (smt lower_inside strided_interval_le.simps upper_inside)
  qed
qed

lemma strided_interval_le_over: "(if \<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x \<le> y then BTrue
                             else if \<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x \<le> y then BBoth
                             else BFalse) \<le> strided_interval_le a b" using strided_interval_le by simp

lemma strided_interval_eq: "(if \<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x = y then BTrue
                             else if \<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x = y then BBoth
                             else BFalse) \<le> strided_interval_eq a b"
proof (cases "\<forall>x y. x \<in> \<gamma>_strided_interval a \<longrightarrow> y \<in> \<gamma>_strided_interval b \<longrightarrow> x = y")
  case True
  then have "strided_interval_eq a b = BTrue" using lower_inside upper_inside by fastforce
  then show ?thesis using True by simp
next
  case False
  hence fa: "\<not>(upper a \<le> lower b \<and> upper b \<le> lower a)" by auto
  then show ?thesis
  proof (cases "\<exists>x y. x \<in> \<gamma>_strided_interval a \<and> y \<in> \<gamma>_strided_interval b \<and> x = y")
    case True
    thus ?thesis using False by auto
  next
    case False
    thus ?thesis proof (cases "upper a < lower b \<or> upper b < lower a")
      assume ass: "upper a < lower b \<or> upper b < lower a"
      from fa ass have "strided_interval_eq a b = BFalse" by simp
      then show ?thesis by (smt False less_eq_power_bool.simps(3) lower_inside)
    qed simp
  qed
qed

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

global_interpretation Word_Strided_Interval: Abs_Word
  where \<gamma>_word = "\<gamma>_option (\<gamma>_toption \<gamma>_strided_interval)"
    and contains = "option_contains (toption_contains strided_interval_contains)"
    and make = "Some \<circ> Minor \<circ> strided_interval_make"
    and concretize = "option_concretize (toption_concretize (strided_interval_concretize concretize_max))"
    and aplus = "option_aplus (toption_aplus strided_interval_aplus)"
    and lt = "option_lift_bool (toption_lift_bool strided_interval_lt)"
    and le = "option_lift_bool (toption_lift_bool strided_interval_le)"
    and eq = "option_lift_bool (toption_lift_bool strided_interval_eq)"
  for concretize_max :: nat
proof (standard, goal_cases)
  case (1 a b)
  then show ?case using \<gamma>_option_mono \<gamma>_toption_mono mono_def \<gamma>_strided_interval_mono 1 by blast
next
  case 2
  then show ?case by (simp add: top_option_def)
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
  from 5 obtain aa where aa: "a = Some (Minor aa)" by (metis option.exhaust option_concretize.simps toption.distinct(1) toption_bind.elims toption_concretize_def)
  obtain s l e where split: "aa = StridedInterval s l e" using strided_interval.exhaust by blast
  show ?case
  proof (cases "e > concretize_max")
    case True
    hence "strided_interval_concretize concretize_max aa = Top" using split by simp
    hence "option_concretize (toption_concretize (strided_interval_concretize concretize_max)) a = Top" using aa by simp
    thus ?thesis using 5 by simp
  next
    case False
    hence "strided_interval_concretize concretize_max aa = Minor (set (map ((*) (int (Suc s)) \<circ> ((+) l) \<circ> int) [0..<Suc e]))" using split by simp
    hence vs: "vs = set (map ((*) (int (Suc s)) \<circ> ((+) l) \<circ> int) [0..<Suc e])" using aa 5 by simp
    have "\<gamma>_strided_interval aa \<subseteq> ((*) (int (Suc s)) \<circ> ((+) l) \<circ> int) ` (set [0..<Suc e])"
    proof (standard, goal_cases)
      case (1 x)
      hence prec: "lower aa \<le> x \<and> x \<le> upper aa \<and> int (stride aa) dvd x" by simp
      from this obtain y where y: "x = y * int (Suc s)" using split by auto
      from y prec have l: "l \<le> y" using split by simp
      from y prec have u: "y \<le> l + int e" using split by simp
      hence "nat (y - l) < Suc e" by simp
      hence ins: "nat (y - l) \<in> set [0..<Suc e]" using atLeast_upt by blast
      have "((*) (int (Suc s)) \<circ> ((+) l) \<circ> int) (nat (y - l)) = x" using l y by simp
      from this ins show ?case by fastforce
    qed
    then show ?thesis using vs aa by simp
  qed
next
  case (6 a vs)
  from this obtain aa where aa: "a = Some (Minor aa)" by (metis option.exhaust option_concretize.simps toption.distinct(1) toption_bind.elims toption_concretize_def)
  obtain s l e where split: "aa = StridedInterval s l e" using strided_interval.exhaust by blast
  have "e \<le> concretize_max"
  proof (rule ccontr, goal_cases)
    case 1
    hence "option_concretize (toption_concretize (strided_interval_concretize concretize_max)) a = Top" using aa split by simp
    then show ?case using 6 by simp
  qed
  then show ?case using 6 aa split by fastforce
next
  case (7 x a y b)
  then show ?case using option_aplusI toption_aplusI strided_interval_aplus by metis
next
  case (8 a b)
  then show ?case using option_toption_lift_bool strided_interval_lt_over by blast
next
  case (9 a b)
  then show ?case using option_toption_lift_bool strided_interval_le_over by blast
next
  case (10 a b)
  then show ?case using option_toption_lift_bool strided_interval_eq by blast
qed

end