theory State_Dumb
imports AbsInt State_Option
begin

datatype dumb_base = Any

lemma dumb_base_is_dumb: "(x::dumb_base) = y" for x y by (cases x; cases y) blast

instantiation dumb_base :: absstate
begin
  definition "\<top> \<equiv> Any"
  definition "\<bottom> \<equiv> Any"
  fun less_eq_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> bool" where "less_eq_dumb_base _ _ \<longleftrightarrow> True"
  fun less_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> bool" where "less_dumb_base _ _ \<longleftrightarrow> False"
  fun sup_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> dumb_base" where "sup_dumb_base _ _  = Any"
  fun inf_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> dumb_base" where "inf_dumb_base _ _  = Any"
  fun Sup_dumb_base :: "dumb_base set \<Rightarrow> dumb_base" where "Sup_dumb_base _ = Any"
  fun Inf_dumb_base :: "dumb_base set \<Rightarrow> dumb_base" where "Inf_dumb_base _ = Any"
instance by standard (auto simp: dumb_base_is_dumb)
end

type_synonym dumb = "dumb_base option"

fun \<gamma>_dumb :: "dumb \<Rightarrow> collect_state set" where
  "\<gamma>_dumb v  = \<gamma>_option (\<lambda>_. \<top>) v"

fun dumb_step :: "dumb astep" where
  "dumb_step _ _ None              = \<bottom>" |
  "dumb_step (JMPZ target) ipc ins = deep_merge {(target, Some Any), (Suc ipc, Some Any)}" |
  "dumb_step CALL ipc ins          = \<top>" |
  "dumb_step RETURN ipc ins        = \<top>" |
  "dumb_step HALT ipc ins          = \<bottom>" |
  "dumb_step _ ipc ins             = single (Suc ipc) (Some Any)"

global_interpretation Dumb: AbsInt
  where \<gamma> = \<gamma>_dumb
    and ai_step = dumb_step
  defines dumb_loop = Dumb.ai_loop
proof (standard, goal_cases)
  case (1 a b)
  then show ?case
  proof (cases a)
    case (Some aa)
    then show ?thesis
      apply(cases b)
      using 1 less_eq_option.simps(2) apply blast
      by simp
  qed simp
next
  case 2 then show ?case by (simp add: top_dumb_base_def)
next
  case (3 op ipc ins pc)
  then show ?case
  proof (cases ins)
    case None
    have "lookup (collect_step op ipc {}) pc \<subseteq> {}" using collect_step_none by blast
    then show ?thesis by (simp add: None)
  next
    case (Some a)
    then show ?thesis
    proof(cases op)
      case (ADD) then show ?thesis using Some collect_step_succ by fastforce
    next
      case (JMPZ target)
      show ?thesis unfolding JMPZ proof(rule jmpz_cases, goal_cases)
        case 1
        have "Some Any \<le> lookup (dumb_step (JMPZ target) ipc ins) (Suc ipc)" using deep_merge_lookup
          by (metis Some dumb_step.simps(2) insert_iff)
        hence "\<top> \<le> \<gamma>_dumb (lookup (dumb_step (JMPZ target) ipc ins) (Suc ipc))"
          by (metis \<gamma>_dumb.simps \<gamma>_option.simps(2) top.extremum_unique top_dumb_base_def top_option_def)
        thus ?case by blast
      next
        case 2
        have "Some Any \<le> lookup (dumb_step (JMPZ target) ipc ins) target" using deep_merge_lookup
          by (metis Some dumb_step.simps(2) insert_iff)
        hence "\<top> \<le> \<gamma>_dumb (lookup (dumb_step (JMPZ target) ipc ins) target)"
          by (metis \<gamma>_dumb.simps \<gamma>_option.simps(2) top.extremum_unique top_dumb_base_def top_option_def)
        thus ?case by blast
      qed
    next
      case (NOT) then show ?thesis using Some collect_step_succ by fastforce next
      case (AND) then show ?thesis using Some collect_step_succ by fastforce next
      case (LT) then show ?thesis using Some collect_step_succ by fastforce next
      case (LE) then show ?thesis using Some collect_step_succ by fastforce next
      case (EQ) then show ?thesis using Some collect_step_succ by fastforce next
      case (PUSH x) then show ?thesis by (simp add: Some) next
      case (POP) then show ?thesis using Some collect_step_succ by fastforce next
      case (LID) then show ?thesis using Some collect_step_succ by simp next
      case (STORE) then show ?thesis using Some collect_step_succ by fastforce next
      case (STOREI) then show ?thesis using Some collect_step_succ by simp next
      case (COPY) then show ?thesis using Some collect_step_succ by simp next
      case (STOREC c d) then show ?thesis using Some collect_step_succ by simp next
    qed auto
  qed
qed simp

end