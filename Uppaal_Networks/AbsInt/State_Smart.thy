theory State_Smart
  imports AbsInt ListLattice Toption Stack State_Option PowerBool Uppaal_Networks.UPPAAL_Asm_Map
begin

type_synonym 'a arstate = "'a list toption"

datatype ('a, 'b) smart_base = Smart 'b "'a arstate" power_bool
type_synonym ('a, 'b) smart = "('a, 'b) smart_base option"

instantiation smart_base :: (absword, absstack) order_top
begin
  definition[simp]: "\<top> \<equiv> Smart \<top> \<top> \<top>"

  fun less_eq_smart_base :: "('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base \<Rightarrow> bool" where
    "less_eq_smart_base (Smart astack aregs aflag) (Smart bstack bregs bflag) \<longleftrightarrow> astack \<le> bstack \<and> aregs \<le> bregs \<and> aflag \<le> bflag"

  fun less_smart_base :: "('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base \<Rightarrow> bool" where
    "less_smart_base a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
instance
proof (standard, goal_cases)
  case (2 x)
  then show ?case using State_Smart.less_eq_smart_base.elims(3) by fastforce
next
  case (3 x y z) then show ?case by (cases x; cases y; cases z; auto)
next
  case (4 x y) then show ?case by (cases x; cases y; auto)
next
  case (5 a) show ?case by (cases a; simp)
qed simp
end

instantiation smart_base :: (absword, absstack) semilattice_sup
begin
  fun sup_smart_base :: "('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base \<Rightarrow> ('a, 'b) smart_base" where
    "sup_smart_base (Smart astack aregs aflag) (Smart bstack bregs bflag) =
      Smart (astack \<squnion> bstack) (aregs \<squnion> bregs) (aflag \<squnion> bflag)"
instance
proof (standard, goal_cases)
  case (1 x y) show ?case by (cases x; cases y; simp)
next
  case (2 y x) show ?case by (cases x; cases y; simp)
next
  case (3 y x z) then show ?case by (cases x; cases y; cases z; simp)
qed
end

context AbsStack
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

fun \<gamma>_smart :: "('a, 'b) smart \<Rightarrow> collect_state set" where
  "\<gamma>_smart None = \<bottom>" |
  "\<gamma>_smart (Some (Smart astack aregs aflag)) = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack astack \<and> rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag}"

fun step_smart_base :: "instr \<Rightarrow> addr \<Rightarrow> ('a::absword, 'b::absstack) smart_base \<Rightarrow> ('a, 'b) smart state_map" where
  "step_smart_base (JMPZ target) pc (Smart stack regs BTrue)  = single (Suc pc) (Some (Smart stack regs BTrue))" |
  "step_smart_base (JMPZ target) pc (Smart stack regs BFalse) = single target (Some (Smart stack regs BFalse))" |
  "step_smart_base (JMPZ target) pc (Smart stack regs BBoth)  = deep_merge {(target, Some (Smart stack regs BBoth)), (Suc pc, Some (Smart stack regs BBoth))}" |

  "step_smart_base ADD           pc (Smart stack regs flag)   =
    (let (bstack, b) = pop stack;
        (astack, a) = pop bstack;
        rstack = push astack (aplus a b) in
    single (Suc pc) (Some (Smart rstack regs flag)))" |

  "step_smart_base NOT           pc (Smart stack regs flag)   = single (Suc pc) (Some (Smart (fst (pop stack)) regs (not flag)))" |

  "step_smart_base AND           pc (Smart stack regs flag)   =
    (let (rstack, a) = pop stack;
         r0 = if contains a 0 then {Some (Smart (fst (pop stack)) regs (and BFalse flag))} else {};
         r1 = r0 \<union> (if contains a 1 then {Some (Smart (fst (pop stack)) regs (and BTrue flag))} else {})
     in deep_merge ((\<lambda>v. (Suc pc, v)) ` r1))" |

  "step_smart_base _ _ _ = \<top>"

fun step_smart :: "('a::absword, 'b::absstack) smart astep" where
  "step_smart _ _ None = \<bottom>" |
  "step_smart op pc (Some a) = step_smart_base op pc a"

lemma gamma_smart_mono:
  assumes "a \<le> b"
  shows "\<gamma>_smart a \<subseteq> \<gamma>_smart b"
proof (intro Set.subsetI)
  fix x assume ass: "x \<in> \<gamma>_smart a"
  from ass obtain astack aregs aflag where asplit: "a = Some (Smart astack aregs aflag)" by (metis \<gamma>_smart.elims empty_iff)
  from this assms obtain bstack bregs bflag where bsplit: "b = Some (Smart bstack bregs bflag)" by (metis \<gamma>_smart.cases less_eq_option.simps(2))
  from ass obtain stack rstate flag nl where xsplit: "x = (stack, rstate, flag, nl)" using prod_cases4 by blast 
  from assms asplit bsplit have fine_le: "astack \<le> bstack" "aregs \<le> bregs" "aflag \<le> bflag" by auto
  from asplit xsplit ass have ain: "stack \<in> \<gamma>_stack astack \<and> rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag" by simp
  from ain fine_le have regs: "rstate \<in> \<gamma>_regs bregs" using mono_gamma_regs by blast
  from ain fine_le have flag: "flag \<in> \<gamma>_power_bool bflag" using mono_gamma_power_bool by blast
  from ain fine_le have stack: "stack \<in> \<gamma>_stack bstack" using mono_gamma_stack by blast
  from regs flag stack bsplit xsplit show "x \<in> \<gamma>_smart b" by simp
qed

lemma gamma_smart_top: "\<gamma>_smart \<top> = \<top>"
proof -
  have "rstate \<in> \<gamma>_regs \<top>" "flag \<in> \<gamma>_power_bool \<top>" for rstate flag by auto
  then show ?thesis by auto
qed

lemma step_smart_nonbot_correct:
  assumes "ost \<in> lookup (collect_step op ipc (\<gamma>_smart (Some (Smart iastack iaregs iaflag)))) opc"
  shows "ost \<in> \<gamma>_smart (lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc)"
proof -
  obtain ocstack ocregs ocflag ocrs where ost_split: "ost = (ocstack, ocregs, ocflag, ocrs)" by (rule prod_cases4)

  let ?ists = "\<gamma>_smart (Some (Smart iastack iaregs iaflag))"
  from assms have "\<exists>ist\<in>?ists. step op (ipc, ist) = Some (opc, ost)" by simp
  from this obtain ist where ist_step: "ist \<in> ?ists" "step op (ipc, ist) = Some (opc, ost)" ..
  obtain icstack icregs icflag icrs where ist_split: "ist = (icstack, icregs, icflag, icrs)" by (rule prod_cases4)

  from ist_split ist_step ost_split have ist_split_step:
    "(icstack, icregs, icflag, icrs) \<in> ?ists"
    "step op (ipc, (icstack, icregs, icflag, icrs)) = Some (opc, (ocstack, ocregs, ocflag, ocrs))" by auto

  from ist_step(1) ist_split have ist_props: "icstack \<in> \<gamma>_stack iastack" "icregs \<in> \<gamma>_regs iaregs" "icflag \<in> \<gamma>_power_bool iaflag" by auto

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
      from this BTrue JMPZ have "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = Some (Smart iastack iaregs iaflag)" using single_lookup by simp
      then show ?thesis using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
    next
      case BFalse
      from this have "icflag = False" using ist_props by simp
      from this JMPZ ist_split_step(2) have "opc = target" using step_jmpz_false(4) by blast
      from this BFalse JMPZ have "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = Some (Smart iastack iaregs iaflag)" using single_lookup by simp
      then show ?thesis using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
    next
      case BBoth
      then show ?thesis
      proof (cases icflag)
        case True
        from this JMPZ ist_split_step(2) have "opc = Suc ipc" using step_jmpz_true(4) by (metis(full_types))
        from this BBoth JMPZ have lookup: "Some (Smart iastack iaregs iaflag) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc" using deep_merge_lookup
          by (metis insert_iff step_smart.simps(2) step_smart_base.simps(3))
        have "ost \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
        from this lookup show ?thesis using gamma_smart_mono by blast
      next
        case False
        from this JMPZ ist_split_step(2) have "opc = target" using step_jmpz_false(4) by (metis(full_types))
        from this BBoth JMPZ have lookup: "Some (Smart iastack iaregs iaflag) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc" using deep_merge_lookup
          by (metis insert_iff step_smart.simps(2) step_smart_base.simps(3))
        have "ost \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split flag_preserve ist_step(1) ost_split regs_preserve stack_preserve by simp
        from this lookup show ?thesis using gamma_smart_mono by blast
      qed
    qed
  next
    case ADD
    hence f1: "step ADD (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)" using ist_split_step(2) by simp
    then have f2: "ocregs = icregs" by (simp add: step_add(2))
    have flag: "ocflag = icflag" using f1 by (simp add: step_add(3))
    from f1 obtain a b rest where stack: "icstack = a # b # rest" "ocstack = (a + b) # rest" using step_add(5) by blast
    let ?oastack = "let (bstack, b) = pop iastack;
        (astack, a) = pop bstack in
        push astack (aplus a b)"
    have lookup: "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = (Some (Smart ?oastack iaregs iaflag))"
      by (metis (mono_tags, lifting) ADD case_prod_beta' f1 single_lookup step_add(1) step_smart.simps(2) step_smart_base.simps(4))
    have "ocstack \<in> \<gamma>_stack ?oastack"
      by (smt case_prod_beta' ist_props(1) plus_correct pop_return_correct pop_stack_correct push_correct stack(1) stack(2))
    then show ?thesis using f2 flag ist_props(2) ist_props(3) lookup ost_split by auto
  next
    case NOT
    from NOT ist_split_step have pc: "opc = Suc ipc" using step_not(1) by blast
    from NOT ist_split_step have regs_preserve: "ocregs = icregs" using step_not(2) by blast
    from NOT ist_split_step have flag: "ocflag = (\<not> icflag)" using step_not(3) by blast
    from NOT ist_split_step have rs_preserve: "ocrs = icrs" using step_not(4) by blast
    from NOT ist_split_step obtain ia where pop: "icstack = ia # ocstack" using step_not(5) by blast
    from this have stack: "ocstack \<in> \<gamma>_stack (fst (pop iastack))" using pop_stack_correct ist_props(1) by simp
    have regs: "ocregs \<in> \<gamma>_regs iaregs" by (simp add: ist_props(2) regs_preserve)
    have flag: "ocflag \<in> \<gamma>_power_bool (not iaflag)" using power_bool_not by (simp add: flag ist_props(3)) 
    from stack regs flag pc show ?thesis by (simp add: NOT ost_split)
  next
    case AND
    have f1: "step AND (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)" using AND ist_split_step(2) by blast
    then have "ocregs = icregs" by (simp add: step_and(2))
    from f1 obtain ia where "icstack = ia # ocstack" "ia = 1 \<or> ia = 0" "ocflag = (ia = 1 \<and> icflag)" using step_and(4) by blast
    then show ?thesis using f1 AND ist_split_step(1) ost_split step_and(1) sorry
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

sublocale AbsStack \<subseteq> AbsInt
  where \<gamma> = "\<gamma>_smart"
    and ai_step = step_smart
proof (standard, goal_cases)
  case (1 a b)
  then show ?case by (rule gamma_smart_mono)
next
  case 2 show ?case by (rule gamma_smart_top)
next
  case (3 op ipc a pc)
  then show ?case using step_smart_nonbot_correct
  proof (cases "a = \<bottom>")
    case True
    then show ?thesis by simp
  next
    case False
    have "lookup (collect_step op ipc (\<gamma>_smart (Some (Smart stack regs flag)))) pc
          \<le> \<gamma>_smart (lookup (step_smart op ipc (Some (Smart stack regs flag))) pc)" for stack regs flag
      using step_smart_nonbot_correct by blast
    from this False show ?thesis by (metis \<gamma>_smart.elims bot_option_def)
  qed
next
  case (4 op ipc pc)
  then show ?case by simp
qed

end