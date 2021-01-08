theory Abs_Bool
  imports Main
begin

notation
  sup (infixl "\<squnion>" 65) and
  top ("\<top>") and
  Sup ("\<Squnion>")

datatype power_bool = BTrue | BFalse | BBoth

fun not :: "power_bool \<Rightarrow> power_bool" where
  "not BTrue = BFalse" |
  "not BFalse = BTrue" |
  "not BBoth = BBoth"

fun "and" :: "power_bool \<Rightarrow> power_bool \<Rightarrow> power_bool" where
  "and BTrue BTrue = BTrue" |
  "and BFalse _ = BFalse" |
  "and _ BFalse = BFalse" |
  "and _ BBoth = BBoth" |
  "and BBoth BTrue = BBoth"

instantiation power_bool :: top begin definition[simp]: "\<top> = BBoth" instance .. end

instantiation power_bool :: "order"
begin
  fun less_eq_power_bool :: "power_bool \<Rightarrow> power_bool \<Rightarrow> bool" where
    "less_eq_power_bool _ BBoth \<longleftrightarrow> True" |
    "less_eq_power_bool BTrue BTrue \<longleftrightarrow> True" |
    "less_eq_power_bool BFalse BFalse \<longleftrightarrow> True" |
    "less_eq_power_bool _ _ \<longleftrightarrow> False"
  fun less_power_bool :: "power_bool \<Rightarrow> power_bool \<Rightarrow> bool" where
    "less_power_bool BBoth BBoth \<longleftrightarrow> False" |
    "less_power_bool _ BBoth \<longleftrightarrow> True" |
    "less_power_bool _ _ \<longleftrightarrow> False"
instance
proof (standard, goal_cases)
  case (1 x y) then show ?case by (cases x; cases y; simp) next
  case (2 x) then show ?case by (cases x; simp) next
  case (3 x y z) then show ?case by (cases x; cases y; cases z; simp) next
  case (4 x y) then show ?case by (cases x; cases y; simp)
qed
end

instantiation power_bool :: "semilattice_sup"
begin
  fun sup_power_bool :: "power_bool \<Rightarrow> power_bool \<Rightarrow> power_bool" where
    "sup_power_bool _ BBoth = BBoth" |
    "sup_power_bool BBoth _ = BBoth" |
    "sup_power_bool BTrue BFalse = BBoth" |
    "sup_power_bool BFalse BTrue = BBoth" |
    "sup_power_bool a _ = a"
instance
proof (standard, goal_cases)
  case (1 x y) then show ?case by (cases x; cases y; simp) next
  case (2 y x) then show ?case by (cases x; cases y; simp) next
  case (3 y x z) then show ?case by (cases x; cases y; cases z; simp)
qed
end

instantiation power_bool :: "order_top"
begin
instance by (standard, simp)
end

fun \<gamma>_power_bool :: "power_bool \<Rightarrow> bool set" where
  "\<gamma>_power_bool BTrue = {True}" |
  "\<gamma>_power_bool BFalse = {False}" |
  "\<gamma>_power_bool BBoth = \<top>"

lemma mono_gamma_power_bool: "a \<le> b \<Longrightarrow> \<gamma>_power_bool a \<le> \<gamma>_power_bool b" by (cases a; cases b; simp)
lemma gamma_power_boolTop[simp]: "\<gamma>_power_bool \<top> = UNIV" by simp

lemma power_bool_not: "x \<in> \<gamma>_power_bool a \<Longrightarrow> (\<not>x) \<in> \<gamma>_power_bool (not a)" by (cases x; cases a; simp)
lemma power_bool_and: "x \<in> \<gamma>_power_bool a \<Longrightarrow> y \<in> \<gamma>_power_bool b \<Longrightarrow> (x \<and> y) \<in> \<gamma>_power_bool (and a b)" by (cases x; cases y; cases a; cases b; simp)

fun powerup :: "bool \<Rightarrow> power_bool" where
  "powerup True = BTrue" |
  "powerup False = BFalse"

lemma powerup_correct: "b \<in> \<gamma>_power_bool (powerup b)"
  by (cases b; simp)

end