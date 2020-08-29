theory OptionLattice
imports Abs_Int Abs_Word PowerBool
  "HOL-Library.Option_ord"
begin

instantiation option :: ("{semilattice_sup, order_top}") absstate begin instance .. end
instantiation option :: ("{semilattice_sup, order_top}") absword begin instance .. end

fun \<gamma>_option :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a option \<Rightarrow> 'b set" where
  "\<gamma>_option _ None = {}" |
  "\<gamma>_option \<gamma> (Some a) = \<gamma> a"

lemma \<gamma>_option_mono:
  assumes
    "\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y"
    "a \<le> b"
  shows "\<gamma>_option f a \<le> \<gamma>_option f b"
  using assms by (cases a; cases b; simp)

fun option_contains :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> 'b \<Rightarrow> bool" where
  "option_contains _ None _ = False" |
  "option_contains contains (Some a) v = contains a v"

fun option_concretize :: "('a \<Rightarrow> 'b toption) \<Rightarrow> 'a option \<Rightarrow> 'b toption" where
  "option_concretize f None = Top" |
  "option_concretize f (Some a) = f a"

fun option_aplus :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" where
  "option_aplus f (Some a) (Some b) = Some (f a b)" |
  "option_aplus _ None _ = None" |
  "option_aplus _ _ None = None"

lemma option_aplusI:
  assumes "\<And>x y a b. x \<in> \<gamma> a \<Longrightarrow> y \<in> \<gamma> b \<Longrightarrow> (x + y) \<in> \<gamma> (aplus a b)"
  shows "x \<in> \<gamma>_option \<gamma> a \<Longrightarrow> y \<in> \<gamma>_option \<gamma> b \<Longrightarrow> (x + y) \<in> \<gamma>_option \<gamma> (option_aplus aplus a b)"
  using assms by (cases a; cases b; simp)

fun option_lift_bool :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> power_bool" where
  "option_lift_bool f (Some a) (Some b) = f a b" |
  "option_lift_bool _ None _ = BTrue" |
  "option_lift_bool _ _ None = BTrue"

lemma option_lift_bool:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> cop x y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> cop x y then BBoth
                   else BFalse) \<le> f a b"
  shows "(if \<forall>x y. x \<in> (\<gamma>_option \<gamma>) a \<longrightarrow> y \<in> (\<gamma>_option \<gamma>) b \<longrightarrow> cop x y then BTrue
          else if \<exists>x y. x \<in> (\<gamma>_option \<gamma>) a \<and> y \<in> (\<gamma>_option \<gamma>) b \<and> cop x y then BBoth
          else BFalse) \<le> (option_lift_bool f) a b"
proof (cases a)
  case (Some aa)
  then show ?thesis
  proof (cases b)
    fix bb assume ass: "b = Some bb"
    have "\<And>f. \<gamma>_option f b = (f bb::'b set)" by (simp add: \<open>b = Some bb\<close>)
    moreover have "\<And>f. \<gamma>_option f a = (f aa::'b set)" by (simp add: Some)
    moreover have "\<And>f. option_lift_bool f a b = f aa bb" using Some ass by force
    ultimately show ?thesis using assms by presburger
  qed simp
qed simp

lemma option_toption_lift_bool:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> cop x y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> cop x y then BBoth
                   else BFalse) \<le> f a b"
  shows "(if \<forall>x y. x \<in> \<gamma>_option (\<gamma>_toption \<gamma>) a \<longrightarrow> y \<in> \<gamma>_option (\<gamma>_toption \<gamma>) b \<longrightarrow> cop x y then BTrue
          else if \<exists>x y. x \<in> \<gamma>_option (\<gamma>_toption \<gamma>) a \<and> y \<in> \<gamma>_option (\<gamma>_toption \<gamma>) b \<and> cop x y then BBoth
          else BFalse) \<le> option_lift_bool (toption_lift_bool f) a b"
proof -
  from assms have "(if \<forall>x y. x \<in> \<gamma>_toption \<gamma> a \<longrightarrow> y \<in> \<gamma>_toption \<gamma> b \<longrightarrow> cop x y then BTrue
          else if \<exists>x y. x \<in> \<gamma>_toption \<gamma> a \<and> y \<in> \<gamma>_toption \<gamma> b \<and> cop x y then BBoth
          else BFalse) \<le> toption_lift_bool f a b" for a b by (rule toption_lift_bool)
  thus ?thesis by (rule option_lift_bool)
qed

fun option_le :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> power_bool" where
  "option_le f (Some a) (Some b) = f a b" |
  "option_le _ None _ = BTrue" |
  "option_le _ _ None = BTrue"

lemma option_le_complete:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> x \<le> y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> x \<le> y then BBoth
                   else BFalse) \<le> le a b"
  shows "(if \<forall>x y. x \<in> (\<gamma>_option \<gamma>) a \<longrightarrow> y \<in> (\<gamma>_option \<gamma>) b \<longrightarrow> x \<le> y then BTrue
          else if \<exists>x y. x \<in> (\<gamma>_option \<gamma>) a \<and> y \<in> (\<gamma>_option \<gamma>) b \<and> x \<le> y then BBoth
          else BFalse) \<le> (option_le le) a b"
proof (cases a)
  case (Some aa)
  then show ?thesis
  proof (cases b)
    fix bb assume "b = Some bb"
    then show ?thesis
    proof -
      have "\<And>f. \<gamma>_option f b = (f bb::'b set)" by (simp add: \<open>b = Some bb\<close>)
      moreover have "\<And>f. \<gamma>_option f a = (f aa::'b set)" by (simp add: Some)
      moreover have "\<And>f. option_le f a b = f aa bb" using Some \<open>b = Some bb\<close> by force
      ultimately show ?thesis using assms by presburger
    qed
  qed simp
qed simp

fun option_eq :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> power_bool" where
  "option_eq f (Some a) (Some b) = f a b" |
  "option_eq _ None _ = BTrue" |
  "option_eq _ _ None = BTrue"

lemma option_eq_complete:
  assumes "\<And>a b. (if \<forall>x y. x \<in> \<gamma> a \<longrightarrow> y \<in> \<gamma> b \<longrightarrow> x = y then BTrue
                   else if \<exists>x y. x \<in> \<gamma> a \<and> y \<in> \<gamma> b \<and> x = y then BBoth
                   else BFalse) \<le> le a b"
  shows "(if \<forall>x y. x \<in> (\<gamma>_option \<gamma>) a \<longrightarrow> y \<in> (\<gamma>_option \<gamma>) b \<longrightarrow> x = y then BTrue
          else if \<exists>x y. x \<in> (\<gamma>_option \<gamma>) a \<and> y \<in> (\<gamma>_option \<gamma>) b \<and> x = y then BBoth
          else BFalse) \<le> (option_eq le) a b"
proof (cases a)
  case (Some aa)
  then show ?thesis
  proof (cases b)
    fix bb assume "b = Some bb"
    then show ?thesis
    proof -
      have "\<And>f. \<gamma>_option f b = (f bb::'b set)" by (simp add: \<open>b = Some bb\<close>)
      moreover have "\<And>f. \<gamma>_option f a = (f aa::'b set)" by (simp add: Some)
      moreover have "\<And>f. option_le f a b = f aa bb" using Some \<open>b = Some bb\<close> by force
      moreover have "\<And>f. option_eq f a b = option_le f a b" by (simp add: Some \<open>b = Some bb\<close>)
      ultimately show ?thesis using assms by presburger
    qed
  qed simp
qed simp

end