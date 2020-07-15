theory UPPAAL_Asm_AbsInt_State_Dumb
imports UPPAAL_Asm_AbsInt UPPAAL_Asm_AbsInt_Option
begin

datatype dumb_base = Any

lemma dumb_base_is_dumb: "(x::dumb_base) = y" for x y by (cases x; cases y) blast

instantiation dumb_base :: absstate
begin
  definition "\<top> \<equiv> Any"
  definition "\<bottom> \<equiv> Any"
  definition "is_bot_dumb_base (a::dumb_base) \<equiv> True"
  fun less_eq_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> bool" where "less_eq_dumb_base _ _ \<longleftrightarrow> True"
  fun less_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> bool" where "less_dumb_base _ _ \<longleftrightarrow> False"
  fun sup_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> dumb_base" where "sup_dumb_base _ _  = Any"
  fun inf_dumb_base :: "dumb_base \<Rightarrow> dumb_base \<Rightarrow> dumb_base" where "inf_dumb_base _ _  = Any"
  fun Sup_dumb_base :: "dumb_base set \<Rightarrow> dumb_base" where "Sup_dumb_base _ = Any"
  fun Inf_dumb_base :: "dumb_base set \<Rightarrow> dumb_base" where "Inf_dumb_base _ = Any"
instance by standard (auto simp: dumb_base_is_dumb is_bot_dumb_base_def)
end

(*instantiation dumb_base :: equal
begin
definition "HOL.equal (a::dumb_base) b \<longleftrightarrow> True"
instance sorry
end*)

type_synonym dumb = "dumb_base option"

fun \<gamma>_dumb :: "dumb \<Rightarrow> collect_state set" where
  "\<gamma>_dumb v  = \<gamma>_option (\<lambda>_. \<top>) v"

fun dumb_steps :: "instr \<Rightarrow> addr \<Rightarrow> dumb \<Rightarrow> (addr * dumb) set" where
  "dumb_steps _ _ None = {}" |
  "dumb_steps (JMPZ target) ipc ins = {(target, Some Any), (Suc ipc, Some Any)}" |
  "dumb_steps CALL ipc ins = \<top>" |
  "dumb_steps RETURN ipc ins = \<top>" |
  "dumb_steps HALT ipc ins = {}" |
  "dumb_steps _ ipc ins = {(Suc ipc, Some Any)}"

definition "dumb_step \<equiv> unique_astep dumb_steps"
declare dumb_step_def[simp]

fun dumb_step_direct :: "dumb astep" where
  "dumb_step_direct _ _ None _ = None" |
  "dumb_step_direct (JMPZ target) ipc ins pc = (if pc = Suc ipc \<or> pc = target then Some Any else None)" |
  "dumb_step_direct CALL ipc ins pc = Some Any" |
  "dumb_step_direct RETURN ipc ins pc = Some Any" |
  "dumb_step_direct HALT ipc ins pc = None" |
  "dumb_step_direct _ ipc ins pc = (if pc = Suc ipc then Some Any else None)"

lemma dumb_step_direct_eq[code]: "dumb_step = dumb_step_direct"
proof -
  have "dumb_step op ipc ins pc = dumb_step_direct op ipc ins pc" for op ipc ins pc
  proof(cases ins)
    case (Some a)
    then show ?thesis
    proof(cases op)
      case (JMPZ target)
      then show ?thesis
      proof(cases "pc = Suc ipc \<or> pc = target")
        case True
        then have "\<forall>sst. (pc, sst) \<in> dumb_steps op ipc ins \<longrightarrow> sst = Some Any" using JMPZ Some by auto
        then have "dumb_step op ipc ins pc = Some Any" using unique_astep_unique JMPZ Some True dumb_steps.simps(2)
          by (smt dumb_step_def insertI1 insert_commute)
        then show ?thesis by (simp add: JMPZ Some True)
      next
        case False
        then have "\<forall>sst. (pc, sst) \<in> dumb_steps op ipc ins \<longrightarrow> sst = None" using JMPZ Some by auto
        then have "dumb_step op ipc ins pc = None" using unique_astep_unique
          by (smt CollectD Sup_bot_conv(1) bot_option_def dumb_step_def unique_astep.simps)
        from this False show ?thesis by (simp add: JMPZ Some)
      qed
    next
      case CALL
      from this Some show ?thesis by (simp add: Some top_dumb_base_def top_option_def)
    next
      case RETURN
      from this Some show ?thesis by (simp add: Some top_dumb_base_def top_option_def)
    qed auto
  qed simp
  thus "dumb_step = dumb_step_direct" using ext by blast
qed

global_interpretation Dumb: AbsInt
  where \<gamma> = \<gamma>_dumb
    and ai_step = dumb_step_direct
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
      case (ADD) then show ?thesis using Some collect_step_succ by fastforce next
      case (JMPZ target) then show ?thesis by (simp add: Some) next
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
      case (STOREC c d) then show ?thesis using Some collect_step_succ by simp
    qed auto
  qed
qed simp

end