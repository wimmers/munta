theory State_Stackless
  imports AbsInt Word State_Option PowerBool Uppaal_Networks.UPPAAL_Asm_Map
begin

type_synonym 'a arstate = "'a state_map"

datatype 'a stackless_base = Stackless "'a arstate" power_bool
type_synonym 'a stackless = "'a stackless_base option"

instantiation stackless_base :: (absword) order_top
begin
  definition[simp]: "\<top> \<equiv> Stackless \<top> \<top>"

  fun less_eq_stackless_base :: "'a stackless_base \<Rightarrow> 'a stackless_base \<Rightarrow> bool" where
    "less_eq_stackless_base (Stackless aregs aflag) (Stackless bregs bflag) \<longleftrightarrow> aregs \<le> bregs \<and> aflag \<le> bflag"

  fun less_stackless_base :: "'a stackless_base \<Rightarrow> 'a stackless_base \<Rightarrow> bool" where
    "less_stackless_base a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
instance
proof (standard, goal_cases)
  case (2 x)
  then show ?case using State_Stackless.less_eq_stackless_base.elims(3) by fastforce
next
  case (3 x y z) then show ?case by (cases x; cases y; cases z; auto)
next
  case (4 x y) then show ?case by (cases x; cases y; auto)
next
  case (5 a) show ?case by (cases a; simp)
qed simp
end

instantiation stackless_base :: (absword) semilattice_sup
begin
  fun sup_stackless_base :: "'a stackless_base \<Rightarrow> 'a stackless_base \<Rightarrow> 'a stackless_base" where
    "sup_stackless_base (Stackless aregs aflag) (Stackless bregs bflag) =
      Stackless (aregs \<squnion> bregs) (aflag \<squnion> bflag)"
instance
proof (standard, goal_cases)
  case (1 x y) show ?case by (cases x; cases y; simp)
next
  case (2 y x) show ?case by (cases x; cases y; simp)
next
  case (3 y x z) then show ?case by (cases x; cases y; cases z; simp)
qed
end

fun \<gamma>_stackless :: "('a \<Rightarrow> int set) \<Rightarrow> 'a stackless \<Rightarrow> collect_state set" where
  "\<gamma>_stackless v  = undefined"

fun step_stackless :: "('a::absword) stackless astep" where
  "step_stackless _ _ None = \<bottom>" |
  "step_stackless _ _ _    = undefined"

sublocale AbsWord \<subseteq> AbsInt
  where \<gamma> = "\<gamma>_stackless \<gamma>_word"
    and ai_step = step_stackless
  sorry

end