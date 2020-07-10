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
  "dumb_step op ipc ins pc = Some Any" (* TODO: this can be better *)

global_interpretation AbsInt
  where \<gamma> = \<gamma>_dumb
    and ai_step = dumb_step
proof (standard, goal_cases)
  case (1 a b)
  then show ?case
  proof (cases a)
    case (Some aa)
    then show ?thesis
    proof (cases b)
      case None
      then show ?thesis using 1 using Some less_eq_option.simps(2) by blast
    next
      case (Some bb)
      then show ?thesis by (cases bb) auto
    qed
  qed simp
next
  case 2
  then show ?case by (simp add: top_dumb_base_def top_option_def)
next
  case (3 op ipc a pc)
  then show ?case by simp
qed

end