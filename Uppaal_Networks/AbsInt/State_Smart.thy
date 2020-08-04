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
  "\<gamma>_regs_list (a # as) = {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_regs_list as} \<squnion> {[]}"

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

lemma regs_length:
  assumes "regs \<in> \<gamma>_regs (Minor l)"
  shows "length regs \<le> length l"
using assms proof (induction l arbitrary: regs)
  case (Cons a as)
  from Cons.prems have "regs = [] \<or> (\<exists>x xs. regs = x # xs \<and> x \<in> \<gamma>_word a \<and> xs \<in> \<gamma>_regs_list as)" by auto
  then show ?case using Cons 
  proof (safe, goal_cases)
    case 1 then show ?case using Cons.IH by (simp add: le_SucI)
  qed simp
qed simp

lemma regs_cons:
  assumes "a # as \<in> \<gamma>_regs (Minor (la # ls))"
  shows "as \<in> \<gamma>_regs (Minor ls)"
  using assms by simp

fun load :: "('a::absword) arstate \<Rightarrow> reg \<Rightarrow> 'a" where
  "load Top _ = \<top>" |
  "load (Minor l) r = (if r < length l then l ! r else \<bottom>)"

lemma load:
  assumes 
    "r < length regs"
    "regs \<in> \<gamma>_regs aregs"
  shows "(regs ! r) \<in> \<gamma>_word (load aregs r)"
proof (cases aregs)
  case (Minor l)
  from this assms(2) have length: "length regs \<le> length l" using regs_length by blast
  from this Minor assms(1) have load: "load aregs r = l ! r" using Minor by auto
  from length assms Minor have "regs ! r \<in> \<gamma>_word (l ! r)"
  proof (induction regs arbitrary: l r aregs)
    case (Cons a regs)
    obtain la ls where lsplit: "l = la # ls" by (metis Cons.prems(3) Cons.prems(4) \<gamma>_regs.simps(2) \<gamma>_regs_list.elims empty_iff insert_iff list.distinct(1))
    then show ?case
    proof (cases r)
      case 0
      from this have "a # regs \<in> \<gamma>_regs_list (la # ls)" using Cons by (simp add: lsplit)
      hence "a # regs \<in> {l. \<exists>x xs. l = x # xs \<and> x \<in> \<gamma>_word la \<and> xs \<in> \<gamma>_regs_list ls}" by simp
      hence "a \<in> \<gamma>_word la" by blast
      from this 0 lsplit show ?thesis using Cons.prems(2) by auto 
    next
      case (Suc rr)
      have length: "length regs \<le> length ls" using Cons.prems(1) lsplit by auto
      have rrlength: "rr < length regs" using Cons.prems(2) Suc by auto
      have "regs \<in> \<gamma>_regs (Minor ls)" using regs_cons Cons.prems(3) Cons.prems(4) lsplit by blast
      from this length rrlength have rr: "regs ! rr \<in> \<gamma>_word (ls ! rr)" using Cons.IH by blast
      from Suc have "(a # regs) ! r = regs ! rr" by simp
      from this rr Suc lsplit show ?thesis using Cons.IH by simp
    qed
  qed simp
  from this load show ?thesis by simp
qed simp

fun store :: "('a::absword) arstate \<Rightarrow> reg \<Rightarrow> 'a \<Rightarrow> 'a arstate" where
  "store Top _ _ = Top" |
  "store (Minor l) r v = Minor (l[r := v])" (* store (Minor l) r v where r \<ge> length l is undefined because we don't need it. *)

fun pop2 :: "'b \<Rightarrow> ('a * 'a * 'b)" where
  "pop2 stack =
    (let (a, astack) = pop stack;
         (b, bstack) = pop astack
    in (a, b, bstack))"

(*lemma[simp]: "pop2 stack =
  (fst (pop (snd (pop stack))), fst (pop stack), snd (pop (snd (pop stack))))"
  by (simp add: case_prod_beta)*)

lemma pop2_stack_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> c \<in> \<gamma>_stack (snd (snd (pop2 b)))"
  by (metis (no_types, lifting) Pair_inject case_prod_beta' pop2.elims pop_stack_correct prod.exhaust_sel)

lemma pop2_return_b_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> cb \<in> \<gamma>_word (fst (snd (pop2 b)))"
proof -
  assume ass: "(ca # cb # c) \<in> \<gamma>_stack b"
  hence i: "(cb # c) \<in> \<gamma>_stack (snd (pop b))" using pop_stack_correct by simp
  have "snd (pop2 b) = pop (snd (pop b))"
    by (metis (no_types, lifting) case_prod_beta' pop2.elims prod.exhaust_sel snd_conv)
  from this i show "cb \<in> \<gamma>_word (fst (snd (pop2 b)))" using pop_return_correct by auto
qed

lemma pop2_return_a_correct: "(ca # cb # c) \<in> \<gamma>_stack b \<Longrightarrow> ca \<in> \<gamma>_word (fst (pop2 b))"
  by (metis (no_types, lifting) case_prod_beta' fst_conv pop2.elims pop_return_correct)

fun pop2_push :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" where
  "pop2_push f stack =
    (let (a, b, rstack) = pop2 stack
    in push rstack (f a b))"

lemma[simp]: "pop2_push f stack =
  push (snd (snd (pop2 stack))) (f (fst (pop2 stack)) (fst (snd (pop2 stack))))"
  by (simp add: case_prod_beta)

lemma pop2_push:
  assumes
    "\<And>x y a b. x \<in> \<gamma>_word a \<Longrightarrow> y \<in> \<gamma>_word b \<Longrightarrow> (cop x y) \<in> \<gamma>_word (f a b)"
    "a # b # rcstack \<in> \<gamma>_stack iastack"
  shows "(cop a b) # rcstack \<in> \<gamma>_stack (pop2_push f iastack)"
  using assms pop2_stack_correct pop2_return_b_correct pop2_return_a_correct
    by (smt case_prod_beta' pop2_push.elims push_correct)

fun \<gamma>_smart :: "('a, 'b) smart \<Rightarrow> collect_state set" where
  "\<gamma>_smart None = \<bottom>" |
  "\<gamma>_smart (Some (Smart astack aregs aflag)) = {(stack, rstate, flag, nl). stack \<in> \<gamma>_stack astack \<and> rstate \<in> \<gamma>_regs aregs \<and> flag \<in> \<gamma>_power_bool aflag}"

lemma in_gamma_smartI:
  assumes
    "stack \<in> \<gamma>_stack astack"
    "rstate \<in> \<gamma>_regs aregs"
    "flag \<in> \<gamma>_power_bool aflag"
  shows
    "(stack, rstate, flag, rs) \<in> \<gamma>_smart (Some (Smart astack aregs aflag))"
  using assms by simp

fun cmp_op :: "('a \<Rightarrow> 'a \<Rightarrow> power_bool) \<Rightarrow> addr \<Rightarrow> ('a::absword, 'b::absstack) smart_base \<Rightarrow> ('a, 'b) smart state_map" where
  "cmp_op f pc (Smart stack regs flag) =
    single (Suc pc) (let (a, b, rstack) = pop2 stack
    in (Some (Smart rstack regs (f a b))))"

lemma cmp_op:
  assumes
    "\<And>c d. f c d = (if \<forall>x y. x \<in> \<gamma>_word c \<longrightarrow> y \<in> \<gamma>_word d \<longrightarrow> op x y then BTrue
                else if \<exists>x y. x \<in> \<gamma>_word c \<longrightarrow> y \<in> \<gamma>_word d \<longrightarrow> op x y then BBoth
                else BFalse)"
    "(a # b # rstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))"
  shows
    "(rstack, icregs, op a b, icrs) \<in> \<gamma>_smart (lookup (cmp_op f ipc (Smart iastack iaregs iaflag)) (Suc ipc))"
proof -
  from assms(2) have istack: "a # b # rstack \<in> \<gamma>_stack iastack" by simp
  from assms(2) have iregs: "icregs \<in> \<gamma>_regs iaregs" by simp
  from assms(2) have iflag: "icflag \<in> \<gamma>_power_bool iaflag" by simp

  let ?oastate = "(Some (Smart (snd (snd (pop2 iastack))) iaregs (f (fst (pop2 iastack)) (fst (snd (pop2 iastack))))))"
  have lookup: "lookup (cmp_op f ipc (Smart iastack iaregs iaflag)) (Suc ipc) = ?oastate" using single_lookup by (metis (mono_tags, lifting) case_prod_beta' cmp_op.simps)

  from istack have ostack: "rstack \<in> \<gamma>_stack (snd (snd (pop2 iastack)))" using pop2_stack_correct by blast
  from assms(1) istack have oflag: "op a b \<in> \<gamma>_power_bool (f (fst (pop2 iastack)) (fst (snd (pop2 iastack))))" using pop2_return_a_correct pop2_return_b_correct by auto
  from ostack iregs oflag have "(rstack, icregs, op a b, icrs) \<in> \<gamma>_smart ?oastate" by (rule in_gamma_smartI)

  from this lookup show ?thesis by simp
qed

fun astore :: "'a::absword \<Rightarrow> 'a arstate \<Rightarrow> 'a arstate" where
  "astore v regs = undefined"
(* (folding.F astore vals regs) *)

fun step_smart_base :: "instr \<Rightarrow> addr \<Rightarrow> ('a::absword, 'b::absstack) smart_base \<Rightarrow> ('a, 'b) smart state_map" where
  "step_smart_base (JMPZ target) pc (Smart stack regs BTrue)  = single (Suc pc) (Some (Smart stack regs BTrue))" |
  "step_smart_base (JMPZ target) pc (Smart stack regs BFalse) = single target (Some (Smart stack regs BFalse))" |
  "step_smart_base (JMPZ target) pc (Smart stack regs BBoth)  = deep_merge {(target, Some (Smart stack regs BBoth)), (Suc pc, Some (Smart stack regs BBoth))}" |

  "step_smart_base ADD           pc (Smart stack regs flag)   =
    single (Suc pc) (Some (Smart (pop2_push aplus stack) regs flag))" |

  "step_smart_base NOT           pc (Smart stack regs flag)   = single (Suc pc) (Some (Smart (snd (pop stack)) regs (not flag)))" |

  "step_smart_base AND           pc (Smart stack regs flag)   =
    (let (a, rstack) = pop stack;
         r0 = if contains a 0 then {(Suc pc, Some (Smart rstack regs (and BFalse flag)))} else {};
         r1 = r0 \<union> (if contains a 1 then {(Suc pc, Some (Smart rstack regs (and BTrue flag)))} else {})
     in deep_merge r1)" |

  "step_smart_base LT pc smart = cmp_op lt pc smart" |
  "step_smart_base LE pc smart = cmp_op le pc smart" |
  "step_smart_base EQ pc smart = cmp_op eq pc smart" |

  "step_smart_base (PUSH v)     pc (Smart stack regs flag)    = single (Suc pc) (Some (Smart (push stack (make v)) regs flag))" |
  "step_smart_base POP          pc (Smart stack regs flag)    = single (Suc pc) (Some (Smart (snd (pop stack)) regs flag))" |

  "step_smart_base (LID r)      pc (Smart stack regs flag)    = single (Suc pc) (Some (Smart (push stack (load regs r)) regs flag))" |

  "step_smart_base STORE        pc (Smart stack regs flag) =
    (let (v, r, rstack) = pop2 stack
     in case concretize r of
          Minor vals \<Rightarrow> single (Suc pc) (Some (Smart rstack undefined flag)) |
          Top \<Rightarrow> \<top> \<comment> \<open>TODO: this can probably be more specific\<close>)" |

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
    let ?oastack = "pop2_push aplus iastack"
    have lookup: "lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc = (Some (Smart ?oastack iaregs iaflag))"
      using ADD f1 step_add(1) by auto
    have "ocstack \<in> \<gamma>_stack ?oastack" using plus_correct pop2_push stack ist_props(1) by metis
    then show ?thesis using f2 flag ist_props(2) ist_props(3) lookup ost_split by auto
  next
    case NOT
    from NOT ist_split_step have pc: "opc = Suc ipc" using step_not(1) by blast
    from NOT ist_split_step have regs_preserve: "ocregs = icregs" using step_not(2) by blast
    from NOT ist_split_step have flag: "ocflag = (\<not> icflag)" using step_not(3) by blast
    from NOT ist_split_step have rs_preserve: "ocrs = icrs" using step_not(4) by blast
    from NOT ist_split_step obtain ia where pop: "icstack = ia # ocstack" using step_not(5) by blast
    from this have stack: "ocstack \<in> \<gamma>_stack (snd (pop iastack))" using pop_stack_correct ist_props(1) by simp
    have regs: "ocregs \<in> \<gamma>_regs iaregs" by (simp add: ist_props(2) regs_preserve)
    have flag: "ocflag \<in> \<gamma>_power_bool (not iaflag)" using power_bool_not by (simp add: flag ist_props(3)) 
    from stack regs flag pc show ?thesis by (simp add: NOT ost_split)
  next
    case AND
    have step: "step AND (ipc, icstack, icregs, icflag, icrs) = Some (opc, ocstack, ocregs, ocflag, ocrs)" using AND ist_split_step(2) by blast
    from step have pc: "opc = Suc ipc" by (simp add: step_and(1))
    from step have regs: "ocregs = icregs" by (simp add: step_and(2))
    from step obtain ia where ia: "icstack = ia # ocstack" "ia = 1 \<or> ia = 0" "ocflag = (ia = 1 \<and> icflag)" using step_and(4) by blast

    let ?mergeset = "let (a, rstack) = pop iastack in
      (if contains a 0 then {(Suc ipc, Some (Smart rstack iaregs (and BFalse iaflag)))} else {})
      \<union> (if contains a 1 then {(Suc ipc, Some (Smart rstack iaregs (and BTrue iaflag)))} else {})"

    have step_mergeset: "step_smart op ipc (Some (Smart iastack iaregs iaflag)) = deep_merge ?mergeset"
      by (metis (no_types, lifting) AND AbsStack.step_smart_base.simps(6) AbsStack_axioms case_prod_beta' step_smart.simps(2))

    from ia(2) have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc)"
    proof(safe, goal_cases 1 0)
      case 1
      have init: "Some (Smart (snd (pop iastack)) iaregs (and BTrue iaflag)) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc"
      proof -
        from 1 have "contains (fst (pop iastack)) 1" using contains_correct ia(1) ist_props(1) pop_return_correct by blast
        hence "(Suc ipc, Some (Smart (snd (pop iastack)) iaregs (and BTrue iaflag))) \<in> ?mergeset" by auto
        from this show ?thesis using step_mergeset deep_merge_lookup by (metis (no_types, lifting) pc)
      qed

      have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (Some (Smart (snd (pop iastack)) iaregs (and BTrue iaflag)))"
      proof (rule in_gamma_smartI, goal_cases)
        case 1 then show ?case using ia(1) ist_props(1) pop_stack_correct by blast next
        case 2 then show ?case using ist_props(2) regs by blast next
        case 3 then show ?case by (smt 1 and.simps(1) and.simps(3) and.simps(5) ia(3) ist_props(3) power_bool.exhaust)
      qed
      from this init show ?case using gamma_smart_mono by blast
    next
      case 0
      have init: "Some (Smart (snd (pop iastack)) iaregs (and BFalse iaflag)) \<le> lookup (step_smart op ipc (Some (Smart iastack iaregs iaflag))) opc"
      proof -
        from 0 have "contains (fst (pop iastack)) 0" using contains_correct ia(1) ist_props(1) pop_return_correct by blast
        hence "(Suc ipc, Some (Smart (snd (pop iastack)) iaregs (and BFalse iaflag))) \<in> ?mergeset" by auto
        from this show ?thesis using step_mergeset deep_merge_lookup by (metis (no_types, lifting) pc)
      qed

      have "(ocstack, ocregs, ocflag, ocrs) \<in> \<gamma>_smart (Some (Smart (snd (pop iastack)) iaregs (and BFalse iaflag)))"
      proof (rule in_gamma_smartI, goal_cases)
        case 1 then show ?case using ia(1) ist_props(1) pop_stack_correct by blast next
        case 2 then show ?case using ist_props(2) regs by blast next
        case 3 then show ?case by (simp add: "0" ia(3))
      qed
      from this init show ?case using gamma_smart_mono by blast
    qed
    thus ?thesis using ost_split by simp
  next
    case LT
    from LT ist_step(2) ist_split ost_split have pc: "opc = Suc ipc" using step_lt(1) by simp
    from LT ist_step(2) ist_split ost_split have regs: "ocregs = icregs" using step_lt(2) by simp
    from LT ist_step(2) ist_split ost_split have rs: "ocrs = icrs" using step_lt(3) by simp
    from LT ist_step(2) ist_split ost_split obtain ia ib where stack: "icstack = ia # ib # ocstack \<and> ocflag = (ia < ib)" using step_lt(4) by blast
    hence "(ia # ib # ocstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split_step(1) by blast
    hence "(ocstack, icregs, ia < ib, icrs) \<in> \<gamma>_smart (lookup (cmp_op lt ipc (Smart iastack iaregs iaflag)) (Suc ipc))" using cmp_op lt_correct by blast
    from this LT pc stack ost_split regs rs show ?thesis by simp
  next
    case LE
    from LE ist_step(2) ist_split ost_split have pc: "opc = Suc ipc" using step_le(1) by simp
    from LE ist_step(2) ist_split ost_split have regs: "ocregs = icregs" using step_le(2) by simp
    from LE ist_step(2) ist_split ost_split have rs: "ocrs = icrs" using step_le(3) by simp
    from LE ist_step(2) ist_split ost_split obtain ia ib where stack: "icstack = ia # ib # ocstack \<and> ocflag = (ia \<le> ib)" using step_le(4) by blast
    hence "(ia # ib # ocstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split_step(1) by blast
    hence "(ocstack, icregs, ia \<le> ib, icrs) \<in> \<gamma>_smart (lookup (cmp_op le ipc (Smart iastack iaregs iaflag)) (Suc ipc))" using cmp_op le_correct by blast
    from this LE pc stack ost_split regs rs show ?thesis by simp
  next
    case EQ
    from EQ ist_step(2) ist_split ost_split have pc: "opc = Suc ipc" using step_eq(1) by simp
    from EQ ist_step(2) ist_split ost_split have regs: "ocregs = icregs" using step_eq(2) by simp
    from EQ ist_step(2) ist_split ost_split have rs: "ocrs = icrs" using step_eq(3) by simp
    from EQ ist_step(2) ist_split ost_split obtain ia ib where stack: "icstack = ia # ib # ocstack \<and> ocflag = (ia = ib)" using step_eq(4) by blast
    hence "(ia # ib # ocstack, icregs, icflag, icrs) \<in> \<gamma>_smart (Some (Smart iastack iaregs iaflag))" using ist_split_step(1) by blast
    hence "(ocstack, icregs, ia = ib, icrs) \<in> \<gamma>_smart (lookup (cmp_op eq ipc (Smart iastack iaregs iaflag)) (Suc ipc))" using cmp_op eq_correct by blast
    from this EQ pc stack ost_split regs rs show ?thesis by simp
  next
    case (PUSH v)
    from PUSH ist_split_step(2) have regs: "ocregs = icregs" using step_push(3) by blast
    from PUSH ist_split_step(2) have flag: "ocflag = icflag" using step_push(4) by blast
    have "v # icstack \<in> \<gamma>_stack (push iastack (make v))" by (meson AbsStack.push_correct AbsStack_axioms ist_props(1) make_correct)
    from this PUSH flag regs show ?thesis using ist_props(2) ist_props(3) ist_split ist_step(2) by auto
  next
    case POP
    from POP ist_split_step(2) have regs: "ocregs = icregs" using step_pop(2) by blast
    from POP ist_split_step(2) have flag: "ocflag = icflag" using step_pop(3) by blast
    from POP ist_split_step(2) obtain v where stack: "v # ocstack = icstack" using step_pop(5) by blast
    from POP regs flag stack show ?thesis using step_pop using ist_props(1) ist_props(2) ist_props(3) ist_split_step(2) ost_split pop_stack_correct by auto
  next
    case (LID r)
    from this ist_split_step(2) have preds: "opc = Suc ipc \<and> ocstack = (icregs ! r) # icstack \<and> ocregs = icregs \<and> ocflag = icflag \<and> ocrs = icrs \<and> r < length icregs" using step_lid by blast
    hence "(icregs ! r) # icstack \<in> \<gamma>_stack (push iastack (load iaregs r))" using load ist_props(1) ist_props(2) push_correct by auto
    from this preds show ?thesis by (simp add: LID ist_props(2) ist_props(3) ost_split)
  next
    case STORE
    then show ?thesis sorry
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