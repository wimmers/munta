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

fun step_stackless_base :: "instr \<Rightarrow> addr \<Rightarrow> 'a stackless_base \<Rightarrow> 'a stackless state_map" where
  "step_stackless_base (JMPZ target) pc (Stackless regs BTrue)  = single (Suc pc) (Some (Stackless regs BTrue))" |
  "step_stackless_base (JMPZ target) pc (Stackless regs BFalse) = single target (Some (Stackless regs BFalse))" |
  "step_stackless_base (JMPZ target) pc (Stackless regs BBoth)  = deep_merge {(target, Some (Stackless regs BBoth)), (Suc pc, Some (Stackless regs BBoth))}" |
  "step_stackless_base ADD           pc (Stackless regs flag)   = single (Suc pc) (Some (Stackless regs flag))" |
  "step_stackless_base NOT           pc (Stackless regs flag)   = single (Suc pc) (Some (Stackless regs (not flag)))" |
  "step_stackless_base AND           pc (Stackless regs flag)   = single (Suc pc) (Some (Stackless regs BBoth))" |
  "step_stackless_base _ _ _ = \<top>"

fun step_stackless :: "('a::absword) stackless astep" where
  "step_stackless _ _ None = \<bottom>" |
  "step_stackless op pc (Some a) = step_stackless_base op pc a"

lemma gamma_stackless_mono:
  assumes "a \<le> b"
  shows "\<gamma>_stackless a \<subseteq> \<gamma>_stackless b"
proof (intro Set.subsetI)
  fix x assume ass: "x \<in> \<gamma>_stackless a"
  from ass obtain aregs aflag where asplit: "a = Some (Stackless aregs aflag)" by (metis \<gamma>_stackless.elims empty_iff)
  from this assms obtain bregs bflag where bsplit: "b = Some (Stackless bregs bflag)" by (metis \<gamma>_stackless.cases less_eq_option.simps(2))
  from ass obtain stack rstate flag nl where xsplit: "x = (stack, rstate, flag, nl)" using prod_cases4 by blast 
  from assms asplit bsplit have fine_le: "aregs \<le> bregs" "aflag \<le> bflag" by auto
  from asplit xsplit ass have "rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag" by simp
  from this fine_le have "rstate \<in> \<gamma>_regs bregs" "flag \<in> \<gamma>_power_bool bflag" using mono_gamma_power_bool mono_gamma_regs by (blast, blast)
  from this bsplit xsplit show "x \<in> \<gamma>_stackless b" by simp
qed

lemma gamma_stackless_top: "\<gamma>_stackless \<top> = \<top>"
proof -
  have "rstate \<in> \<gamma>_regs \<top>" "flag \<in> \<gamma>_power_bool \<top>" for rstate flag by auto
  then show ?thesis by auto
qed

lemma step_stackless_nonbot_correct:
  assumes "ost \<in> lookup (collect_step op ipc (\<gamma>_stackless (Some (Stackless iaregs iaflag)))) opc"
  shows "ost \<in> \<gamma>_stackless (lookup (step_stackless op ipc (Some (Stackless iaregs iaflag))) opc)"
proof -
  obtain ocstack ocregs ocflag ocrs where ost_split: "ost = (ocstack, ocregs, ocflag, ocrs)" by (rule prod_cases4)

  let ?ists = "\<gamma>_stackless (Some (Stackless iaregs iaflag))"
  from assms have "\<exists>ist\<in>?ists. step op (ipc, ist) = Some (opc, ost)" by simp
  from this obtain ist where ist_step: "ist \<in> ?ists" "step op (ipc, ist) = Some (opc, ost)" ..
  obtain icstack icregs icflag icrs where ist_split: "ist = (icstack, icregs, icflag, icrs)" by (rule prod_cases4)

  from ist_split ist_step ost_split have ist_split_step:
    "(icstack, icregs, icflag, icrs) \<in> ?ists"
    "step op (ipc, (icstack, icregs, icflag, icrs)) = Some (opc, (ocstack, ocregs, ocflag, ocrs))" by auto

  (* more properties can be added here if \<gamma>_stackless gets updated *)
  from ist_step(1) ist_split have ist_props: "icregs \<in> \<gamma>_regs iaregs" "icflag \<in> \<gamma>_power_bool iaflag" by auto

  show ?thesis 
  proof (cases op)
    case (JMPZ target)
    from JMPZ ist_split_step have stack_preserve: "ocstack = icstack" using step_jmpz(1) by blast
    from JMPZ ist_split_step have regs_preserve: "ocregs = icregs" using step_jmpz(2) by blast
    from JMPZ ist_split_step have flag_preserve: "ocflag = icflag" using step_jmpz(3) by blast
    from JMPZ ist_split_step have rs_preserve: "ocrs = icrs" using step_jmpz(4) by blast
    show ?thesis
    proof (cases iaflag)
      case BTrue
      from this have "icflag = True" using ist_props by simp
      from this JMPZ ist_split_step(2) have "opc = Suc ipc" using step_jmpz_true(4) by blast
      from this BTrue JMPZ have "lookup (step_stackless op ipc (Some (Stackless iaregs iaflag))) opc = Some (Stackless iaregs iaflag)" using single_lookup by simp
      then show ?thesis using ist_split flag_preserve ist_step(1) ost_split regs_preserve by simp
    next
      case BFalse
      from this have "icflag = False" using ist_props by simp
      from this JMPZ ist_split_step(2) have "opc = target" using step_jmpz_false(4) by blast
      from this BFalse JMPZ have "lookup (step_stackless op ipc (Some (Stackless iaregs iaflag))) opc = Some (Stackless iaregs iaflag)" using single_lookup by simp
      then show ?thesis using ist_split flag_preserve ist_step(1) ost_split regs_preserve by simp
    next
      case BBoth
      then show ?thesis
      proof (cases icflag)
        case True
        from this JMPZ ist_split_step(2) have "opc = Suc ipc" using step_jmpz_true(4) by (metis(full_types))
        from this BBoth JMPZ have lookup: "Some (Stackless iaregs iaflag) \<le> lookup (step_stackless op ipc (Some (Stackless iaregs iaflag))) opc" using deep_merge_lookup
          by (metis insert_iff step_stackless.simps(2) step_stackless_base.simps(3))
        have "ost \<in> \<gamma>_stackless (Some (Stackless iaregs iaflag))" using ist_split flag_preserve ist_step(1) ost_split regs_preserve by simp
        from this lookup show ?thesis using gamma_stackless_mono by blast
      next
        case False
        from this JMPZ ist_split_step(2) have "opc = target" using step_jmpz_false(4) by (metis(full_types))
        from this BBoth JMPZ have lookup: "Some (Stackless iaregs iaflag) \<le> lookup (step_stackless op ipc (Some (Stackless iaregs iaflag))) opc" using deep_merge_lookup
          by (metis insert_iff step_stackless.simps(2) step_stackless_base.simps(3))
        have "ost \<in> \<gamma>_stackless (Some (Stackless iaregs iaflag))" using ist_split flag_preserve ist_step(1) ost_split regs_preserve by simp
        from this lookup show ?thesis using gamma_stackless_mono by blast
      qed
    qed
  next
    case ADD
    hence f1: "step ADD (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)"
      using ist_split_step(2) by presburger
    then have f2: "ocregs = icregs" by (simp add: step_add(2))
    have "ocflag = icflag" using f1 by (simp add: step_add(3))
    then show ?thesis using f2 f1 ADD ist_split_step(1) ost_split step_add(1) by force
  next
    case NOT
    from NOT ist_split_step have pc: "opc = Suc ipc" using step_not(1) by blast
    from NOT ist_split_step have regs_preserve: "ocregs = icregs" using step_not(2) by blast
    from NOT ist_split_step have flag: "ocflag = (\<not> icflag)" using step_not(3) by blast
    from NOT ist_split_step have rs_preserve: "ocrs = icrs" using step_not(4) by blast
    then show ?thesis using NOT flag ist_props(1) ist_props(2) ost_split regs_preserve pc by (cases iaflag, auto)
  next
    case AND
    have f1: "step AND (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)"
      using AND ist_split_step(2) by blast
    then have "ocregs = icregs"
      by (simp add: step_and(2))
    then show ?thesis
      using f1 AND ist_split_step(1) ost_split step_and(1) by auto
  next
    case LT
    then show ?thesis by auto
  next
    case LE
    then show ?thesis by auto
  next
    case EQ
    then show ?thesis by auto
  next
    case (PUSH x8)
    then show ?thesis by auto
  next
    case POP
    then show ?thesis by auto
  next
    case (LID x10)
    then show ?thesis by auto
  next
    case STORE
    then show ?thesis by auto
  next
    case (STOREI x121 x122)
    then show ?thesis by auto
  next
    case COPY
    then show ?thesis by auto
  next
    case CALL
    then show ?thesis by auto
  next
    case RETURN
    then show ?thesis by auto
  next
    case HALT
    then show ?thesis by auto
  next
    case (STOREC x171 x172)
    then show ?thesis by auto
  next
    case (SETF x18)
    then show ?thesis by auto
  qed
qed

end

sublocale AbsWord \<subseteq> AbsInt
  where \<gamma> = "\<gamma>_stackless"
    and ai_step = step_stackless
proof (standard, goal_cases)
  case (1 a b)
  then show ?case by (rule gamma_stackless_mono)
next
  case 2 show ?case by (rule gamma_stackless_top)
next
  case (3 op ipc a pc)
  then show ?case using step_stackless_nonbot_correct
  proof (cases "a = \<bottom>")
    case True
    then show ?thesis by simp
  next
    case False
    have "lookup (collect_step op ipc (\<gamma>_stackless (Some (Stackless regs flag)))) pc
          \<le> \<gamma>_stackless (lookup (step_stackless op ipc (Some (Stackless regs flag))) pc)" for regs flag
      using step_stackless_nonbot_correct by blast
    from this False show ?thesis by (metis \<gamma>_stackless.elims bot_option_def)
  qed
next
  case (4 op ipc pc)
  then show ?case by simp
qed

end