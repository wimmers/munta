theory PowerBool
  imports Main
begin

notation
  sup (infixl "\<squnion>" 65) and
  top ("\<top>") and
  Sup ("\<Squnion>")

datatype power_bool = BTrue | BFalse | BBoth

instantiation power_bool :: top begin definition "\<top> = BBoth" instance .. end

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

instantiation power_bool :: "Sup"
begin
  fun Sup_power_bool :: "power_bool set \<Rightarrow> power_bool" where
    "Sup_power_bool s = (
      if BBoth \<in> s \<or> s = {BFalse, BTrue} then BBoth
      else if s = {BTrue} then BTrue
      else if s = {BFalse} then BFalse
      else undefined)"
instance ..
end

end