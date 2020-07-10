theory UPPAAL_Asm_AbsInt_State_Dumb
imports UPPAAL_Asm_AbsInt UPPAAL_Asm_AbsInt_Option
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
  "dumb_step _ _ None _ = None" |
  "dumb_step (JMPZ target) ipc ins pc = (if pc = Suc ipc \<or> pc = target then Some Any else None)" |
  "dumb_step ADD ipc ins pc = (if pc = Suc ipc then Some Any else None)" |
  "dumb_step NOT ipc ins pc = (if pc = Suc ipc then Some Any else None)" |
  "dumb_step AND ipc ins pc = (if pc = Suc ipc then Some Any else None)" |
  "dumb_step LT ipc ins pc = Some Any" |
  "dumb_step LE ipc ins pc = Some Any" |
  "dumb_step EQ ipc ins pc = Some Any" |
  "dumb_step (PUSH _)ipc ins pc = Some Any" |
  "dumb_step POP ipc ins pc = Some Any" |
  "dumb_step (LID _) ipc ins pc = Some Any" |
  "dumb_step STORE ipc ins pc = Some Any" |
  "dumb_step (STOREI _ _) ipc ins pc = Some Any" |
  "dumb_step COPY ipc ins pc = Some Any" |
  "dumb_step CALL ipc ins pc = Some Any" |
  "dumb_step RETURN ipc ins pc = Some Any" |
  "dumb_step HALT ipc ins pc = Some Any" |
  "dumb_step (STOREC _ _) ipc ins pc = Some Any" |
  "dumb_step (SETF _) ipc ins pc = Some Any"

global_interpretation AbsInt
  where \<gamma> = \<gamma>_dumb
    and ai_step = dumb_step
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
  case 2 then show ?case by (simp add: top_dumb_base_def top_option_def)
next
  case (3 op ipc ins pc)
  then show ?case
  proof (cases ins)
    case None
    have "collect_step op ipc {} pc \<subseteq> {}" using collect_step.simps by blast
    then show ?thesis by (simp add: None)
  next
    case (Some a)
    then show ?thesis
    proof(cases op)
      case (JMPZ target) then show ?thesis by (simp add: Some) next
      case (ADD) then show ?thesis using Some collect_step_add_succ by fastforce next
      case (NOT) then show ?thesis using Some collect_step_not_succ by fastforce next
      case (AND) then show ?thesis using Some collect_step_and_succ by fastforce
    qed auto
  qed
qed

end