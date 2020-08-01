theory State_Stackless
  imports AbsInt ListLattice Toption Word State_Option PowerBool Uppaal_Networks.UPPAAL_Asm_Map
begin

type_synonym 'a arstate = "'a list toption"

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

context AbsWord
begin

fun \<gamma>_regs_list :: "'a list \<Rightarrow> rstate set" where
  "\<gamma>_regs_list [] = {[]}" |
  "\<gamma>_regs_list (a # as) = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_regs_list as} \<union> \<gamma>_regs_list as"

lemma mono_gamma_regs_list: "a \<le> b \<Longrightarrow> \<gamma>_regs_list a \<le> \<gamma>_regs_list b"
proof (induction a arbitrary: b)
  case Nil
  then show ?case by (induction b; simp)
next
  case (Cons ax as)
  from Cons.prems obtain bx bs where "b = bx # bs" using less_eq_list.elims(2) by blast
  from this Cons show ?case using mono_gamma by fastforce
qed

fun \<gamma>_regs :: "'a arstate \<Rightarrow> rstate set" where
  "\<gamma>_regs Top = \<top>" |
  "\<gamma>_regs (Minor l) = \<gamma>_regs_list l"

lemma mono_gamma_regs: "a \<le> b \<Longrightarrow> \<gamma>_regs a \<le> \<gamma>_regs b"
proof -
  assume ass: "a \<le> b"
  show "\<gamma>_regs a \<le> \<gamma>_regs b"
  proof (cases a)
    case Top from this ass show ?thesis using less_eq_toption.elims(2) by force
  next
    fix ax assume ax: "a = Minor ax"
    then show ?thesis
    proof (cases b)
      case Top then show ?thesis by simp
    next
      case (Minor bx)
      from this ax show ?thesis using ass mono_gamma_regs_list by simp
    qed
  qed
qed

lemma mono_gamma_power_bool: "a \<le> b \<Longrightarrow> \<gamma>_power_bool a \<le> \<gamma>_power_bool b" by (cases a; cases b; simp)

fun \<gamma>_stackless :: "'a stackless \<Rightarrow> collect_state set" where
  "\<gamma>_stackless None = \<bottom>" |
  "\<gamma>_stackless (Some (Stackless aregs aflag)) = {(stack, rstate, flag, nl). rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag}"

fun step_stackless :: "('a::absword) stackless astep" where
  "step_stackless _ _ None = \<bottom>" |
  "step_stackless _ _ _    = undefined"

end

sublocale AbsWord \<subseteq> AbsInt
  where \<gamma> = "\<gamma>_stackless"
    and ai_step = step_stackless
proof (standard, goal_cases)
  case (1 a b)
  then show ?case
  proof (intro Set.subsetI)
    fix x assume ass: "x \<in> \<gamma>_stackless a"
    from ass obtain aregs aflag where asplit: "a = Some (Stackless aregs aflag)" by (metis \<gamma>_stackless.elims empty_iff)
    from this 1 obtain bregs bflag where bsplit: "b = Some (Stackless bregs bflag)" by (metis \<gamma>_stackless.cases less_eq_option.simps(2))
    from ass obtain stack rstate flag nl where xsplit: "x = (stack, rstate, flag, nl)" using prod_cases4 by blast 
    from 1 asplit bsplit have fine_le: "aregs \<le> bregs" "aflag \<le> bflag" by auto
    from asplit xsplit ass have "rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag" by simp
    from this fine_le have "rstate \<in> \<gamma>_regs bregs" "flag \<in> \<gamma>_power_bool bflag" using mono_gamma_power_bool mono_gamma_regs by (blast, blast)
    from this bsplit xsplit show "x \<in> \<gamma>_stackless b" by simp
  qed
next
  case 2
  have "rstate \<in> \<gamma>_regs \<top>" "flag \<in> \<gamma>_power_bool \<top>" for rstate flag by auto
  then show ?case by auto
next
  case (3 op ipc a pc)
  then show ?case sorry
next
  case (4 op ipc pc)
  then show ?case sorry
qed

end