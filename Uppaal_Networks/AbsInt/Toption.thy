theory Toption
  imports Main "HOL-Library.Lattice_Syntax" PowerBool
begin

text\<open>@{type option}-like type adding a top element.\<close>

datatype 'a toption = Top | Minor 'a

instantiation toption :: (type) top
begin
  definition[simp]: "\<top> = Top"
instance ..
end

instantiation toption :: (order) order_top
begin
  fun less_eq_toption :: "'a toption \<Rightarrow> 'a toption \<Rightarrow> bool" where
    "_ \<le> Top \<longleftrightarrow> True" |
    "Top \<le> x \<longleftrightarrow> False" |
    "Minor x \<le> Minor y \<longleftrightarrow> x \<le> y"

  fun less_toption :: "'a toption \<Rightarrow> 'a toption \<Rightarrow> bool" where
    "Top < _ \<longleftrightarrow> False" |
    "Minor x < Top \<longleftrightarrow> True" |
    "Minor x < Minor y \<longleftrightarrow> x < y"
instance proof (standard, goal_cases)
  case (1 x y)
  then show ?case by (cases x; cases y; auto)
next
  case (2 x)
  then show ?case by (cases x; simp)
next
  case (3 x y z)
  then show ?case by (cases x; cases y; cases z; simp)
next
  case (4 x y)
  then show ?case by (cases x; cases y; simp)
qed simp
end

instantiation toption :: (semilattice_sup) semilattice_sup
begin
  fun sup_toption :: "'a toption \<Rightarrow> 'a toption \<Rightarrow> 'a toption" where
    "Top \<squnion> _ = Top" |
    "_ \<squnion> Top = Top" |
    "Minor x \<squnion> Minor y = Minor (x \<squnion> y)"
instance proof(standard, goal_cases)
  case (1 x y)
  then show ?case by (cases x; cases y; simp)
next
  case (2 y x)
  then show ?case by (cases x; cases y; simp)
next
  case (3 y x z)
  then show ?case by (cases x; cases y; cases z; simp)
qed
end

instantiation toption :: (order_bot) order_bot
begin
definition[simp]: "\<bottom> = Minor \<bottom>"
instance proof (standard, goal_cases)
  case (1 a) then show ?case by (cases a; simp)
qed
end

instantiation toption :: (bounded_semilattice_sup_bot) "bounded_semilattice_sup_bot" begin instance .. end

fun \<gamma>_toption :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a toption \<Rightarrow> 'b set" where
  "\<gamma>_toption \<gamma> Top = \<top>" |
  "\<gamma>_toption \<gamma> (Minor a) = \<gamma> a"

lemma \<gamma>_toption_mono:
  assumes
    "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
    "a \<le> b"
  shows "\<gamma>_toption f a \<le> \<gamma>_toption f b"
  using assms by (cases a; cases b; simp)

fun toption_contains :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a toption \<Rightarrow> 'b \<Rightarrow> bool" where
  "toption_contains _ Top _ = True" |
  "toption_contains contains (Minor a) v = contains a v"

fun toption_bind :: "'a toption \<Rightarrow> ('a \<Rightarrow> 'b toption) \<Rightarrow> 'b toption" where
  "toption_bind Top f = Top" |
  "toption_bind (Minor a) f = f a"

definition[simp]: "toption_concretize f t = toption_bind t f"

fun toption_aplus :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a toption \<Rightarrow> 'a toption \<Rightarrow> 'a toption" where
  "toption_aplus f (Minor a) (Minor b) = Minor (f a b)" |
  "toption_aplus _ Top _ = Top" |
  "toption_aplus _ _ Top = Top"

lemma toption_aplusI:
  assumes "\<And>x y a b. x \<in> \<gamma> a \<Longrightarrow> y \<in> \<gamma> b \<Longrightarrow> (x + y) \<in> \<gamma> (aplus a b)"
  shows "x \<in> \<gamma>_toption \<gamma> a \<Longrightarrow> y \<in> \<gamma>_toption \<gamma> b \<Longrightarrow> (x + y) \<in> \<gamma>_toption \<gamma> (toption_aplus aplus a b)"
  using assms by (cases a; cases b; simp)

fun toption_lift_bool :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> 'a toption \<Rightarrow> 'a toption \<Rightarrow> power_bool" where
  "toption_lift_bool f (Minor a) (Minor b) = f a b" |
  "toption_lift_bool f Top _ = BBoth" |
  "toption_lift_bool f _ Top = BBoth"

lemma toption_lift_bool:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> cop x y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> cop x y then BBoth
                   else BFalse) \<le> f a b"
  shows "(if \<forall>x y. x \<in> (\<gamma>_toption \<gamma>) a \<longrightarrow> y \<in> (\<gamma>_toption \<gamma>) b \<longrightarrow> cop x y then BTrue
          else if \<exists>x y. x \<in> (\<gamma>_toption \<gamma>) a \<and> y \<in> (\<gamma>_toption \<gamma>) b \<and> cop x y then BBoth
          else BFalse) \<le> (toption_lift_bool f) a b"
proof (cases a)
  case (Minor x2)
  then show ?thesis
  proof (cases b)
    fix x1 assume ass: "b = Minor x1"
    hence "\<And>f. \<gamma>_toption f b = (f x1::'b set)" by auto
    moreover have "\<And>f. \<gamma>_toption f a = (f x2::'b set)" by (simp add: Minor)
    moreover have "\<And>f. toption_lift_bool f a b = f x2 x1" by (simp add: Minor ass)
    ultimately show ?thesis using assms by presburger
  qed simp
qed simp

fun toption_le :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> 'a toption \<Rightarrow> 'a toption \<Rightarrow> power_bool" where
  "toption_le f (Minor a) (Minor b) = f a b" |
  "toption_le f Top _ = BBoth" |
  "toption_le f _ Top = BBoth"

lemma toption_le_complete:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> x \<le> y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> x \<le> y then BBoth
                   else BFalse) \<le> le a b"
  shows "(if \<forall>x y. x \<in> (\<gamma>_toption \<gamma>) a \<longrightarrow> y \<in> (\<gamma>_toption \<gamma>) b \<longrightarrow> x \<le> y then BTrue
          else if \<exists>x y. x \<in> (\<gamma>_toption \<gamma>) a \<and> y \<in> (\<gamma>_toption \<gamma>) b \<and> x \<le> y then BBoth
          else BFalse) \<le> (toption_le le) a b"
proof (cases a)
  case (Minor x2)
  then show ?thesis
  proof (cases b)
    fix x1 assume ass: "b = Minor x1"
    then show ?thesis
    proof -
      have "\<And>f. \<gamma>_toption f b = (f x1::'b set)" using ass by auto
      moreover have "\<And>f. \<gamma>_toption f a = (f x2::'b set)" by (simp add: Minor)
      moreover have "\<And>f. toption_le f a b = f x2 x1" by (simp add: Minor ass)
      ultimately show ?thesis using assms by presburger
    qed
  qed simp
qed simp

fun toption_eq :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> 'a toption \<Rightarrow> 'a toption \<Rightarrow> power_bool" where
  "toption_eq f (Minor a) (Minor b) = f a b" |
  "toption_eq f Top _ = BBoth" |
  "toption_eq f _ Top = BBoth"

lemma toption_eq_complete:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> x = y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> x = y then BBoth
                   else BFalse) \<le> eq a b"
  shows "(if \<forall>x y. x \<in> (\<gamma>_toption \<gamma>) a \<longrightarrow> y \<in> (\<gamma>_toption \<gamma>) b \<longrightarrow> x = y then BTrue
          else if \<exists>x y. x \<in> (\<gamma>_toption \<gamma>) a \<and> y \<in> (\<gamma>_toption \<gamma>) b \<and> x = y then BBoth
          else BFalse) \<le> (toption_eq eq) a b"
proof (cases a)
  case (Minor x2)
  then show ?thesis
  proof (cases b)
    fix x1 assume ass: "b = Minor x1"
    then show ?thesis
    proof -
      have "\<And>f. \<gamma>_toption f b = (f x1::'b set)" using ass by auto
      moreover have "\<And>f. \<gamma>_toption f a = (f x2::'b set)" by (simp add: Minor)
      moreover have "\<And>f. toption_eq f a b = f x2 x1" by (simp add: Minor ass)
      ultimately show ?thesis using assms by presburger
    qed
  qed simp
qed simp

end