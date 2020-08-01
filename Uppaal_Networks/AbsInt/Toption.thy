theory Toption
  imports Main Uppaal_Networks.Notation
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

end