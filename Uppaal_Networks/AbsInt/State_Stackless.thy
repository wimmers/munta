theory State_Stackless
  imports AbsInt Word State_Option PowerBool Uppaal_Networks.UPPAAL_Asm_Map
begin

type_synonym 'a arstate = "'a state_map"

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

  fun Sup_stackless :: "'a stackless set \<Rightarrow> 'a stackless" where
    "Sup_stackless s = (
      if s = {} then \<bottom>
      else if s = {\<bottom>} then \<bottom>
      else Stackless
        (\<Squnion>{regs. \<exists>flag. Stackless regs flag \<in> s})
        (\<Squnion>{flag. \<exists>regs. Stackless regs flag \<in> s}))"

  fun inf_stackless :: "'a stackless \<Rightarrow> 'a stackless \<Rightarrow> 'a stackless" where "inf_stackless _ _  = undefined"
  fun Inf_stackless :: "'a stackless set \<Rightarrow> 'a stackless" where "Inf_stackless s = \<Squnion>(\<top> - s)"

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