theory State_Stackless
  imports AbsInt Word State_Option Uppaal_Networks.UPPAAL_Asm_Map
begin

type_synonym 'a arstate = "'a state_map"

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

datatype 'a stackless = Stackless "'a arstate" power_bool | StacklessNone

instantiation stackless :: (absword) absstate
begin
  definition "\<top> \<equiv> Stackless \<top> \<top>"
  definition "\<bottom> \<equiv> StacklessNone"

  fun less_eq_stackless :: "'a stackless \<Rightarrow> 'a stackless \<Rightarrow> bool" where
    "less_eq_stackless StacklessNone _ \<longleftrightarrow> True" |
    "less_eq_stackless _ StacklessNone \<longleftrightarrow> False" |
    "less_eq_stackless (Stackless aregs aflag) (Stackless bregs bflag) \<longleftrightarrow> aregs \<le> bregs \<and> aflag \<le> bflag"

  fun less_stackless :: "'a stackless \<Rightarrow> 'a stackless \<Rightarrow> bool" where "less_stackless a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

  fun sup_stackless :: "'a stackless \<Rightarrow> 'a stackless \<Rightarrow> 'a stackless" where
    "sup_stackless StacklessNone b = b" |
    "sup_stackless a StacklessNone = a" |
    "sup_stackless (Stackless aregs aflag) (Stackless bregs bflag) = Stackless (aregs \<squnion> bregs) (aflag \<squnion> bflag)"

  fun inf_stackless :: "'a stackless \<Rightarrow> 'a stackless \<Rightarrow> 'a stackless" where "inf_stackless _ _  = undefined"
  fun Sup_stackless :: "'a stackless set \<Rightarrow> 'a stackless" where "Sup_stackless _ = undefined"
  fun Inf_stackless :: "'a stackless set \<Rightarrow> 'a stackless" where "Inf_stackless _ = undefined"

instance sorry
end

fun \<gamma>_stackless :: "('a \<Rightarrow> int set) \<Rightarrow> 'a stackless \<Rightarrow> collect_state set" where
  "\<gamma>_stackless v  = undefined"

fun step_stackless :: "('a::absword) stackless astep" where
  "step_stackless _ _ StacklessNone = \<bottom>" |
  "step_stackless _ _ _             = undefined"

sublocale AbsWord \<subseteq> AbsInt
  where \<gamma> = "\<gamma>_stackless \<gamma>_word" (* TODO: make this \<gamma>_word not blue *)
    and ai_step = step_stackless
  sorry

end