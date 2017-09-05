theory UPPAAL_State_Networks_Impl
  imports Normalized_Zone_Semantics_Impl UPPAAL_State_Networks
begin

chapter \<open>Implementation of UPPAAL Style Networks\<close>

no_notation OR (infix "or" 60)

lemma step_resets:
  "\<forall> c \<in> set r'. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc"
  if "stepc cmd u (pc, st, s, f, r) = Some (pc', st', s', f', r')"
    "\<forall> c \<in> set r. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc" "P pc = Some cmd"
  using that
  apply -
  apply (erule stepc.elims)
  by (auto split: option.splits if_splits elim!: step.elims) metis+

lemma step_resets':
  "\<forall> c \<in> set r'. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc"
  if "step instr (pc, st, s, f, r) = Some (pc', st', s', f', r')"
    "\<forall> c \<in> set r. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc" "P pc = Some (INSTR instr)"
  using that
  by (auto split: option.splits if_splits elim!: step.elims) metis+

lemma step_resets'':
  "\<forall> c \<in> set r'. \<exists> x pc. Some (STOREC c x) = P pc"
  if "step instr (pc, st, s, f, r) = Some (pc', st', s', f', r')"
    "\<forall> c \<in> set r. \<exists> x pc. Some (STOREC c x) = P pc" "P pc = Some instr"
  using that
  by (auto split: option.splits if_splits elim!: step.elims) metis+

lemma steps_reset:
  "\<forall> c \<in> set r'. \<exists> x pc. Some (STOREC c x) = P pc"
  if "steps P n (pc, st, s, f, r) (pc', st', s', f', r')" "\<forall> c \<in> set r. \<exists> x pc. Some (STOREC c x) = P pc"
  using that
  by (induction P \<equiv> P n "(pc, st, s, f, r :: nat list)" "(pc', st', s', f', r')" arbitrary: pc st s f r rule: steps.induct)
     (auto dest!: step_resets''[where P = P])

lemma exec_reset:
  "\<forall> c \<in> set r'. \<exists> x pc. Some (STOREC c x) = P pc"
  if "Some ((pc', st', s', f', r'), pcs') = exec P n (pc, st, s, f, []) pcs"
  using exec_steps[OF that[symmetric]] steps_reset by force

lemma exec_pointers:
  "\<forall> pc \<in> set pcs'. \<exists> pc instr. Some instr = P pc"
  if "Some ((pc', st', s', f', r'), pcs') = exec P n (pc, st, s, f, r) pcs"
     "\<forall> pc \<in> set pcs. \<exists> pc instr. Some instr = P pc"
  using that
  apply (induction rule: exec.induct)
  by (auto split: option.splits if_splits) metis+

lemma exec_pointers':
  "\<forall> pc \<in> set pcs'. \<exists> pc instr. Some instr = P pc"
  if "Some ((pc', st', s', f', r'), pcs') = exec P n (pc, st, s, f, r) []"
  using that exec_pointers by fastforce

context Prod_TA_Defs
begin

lemma finite_range_I':
  assumes "\<forall>A\<in>{0..<p}. finite (range (snd (N ! A)))"
    shows "finite (range (I' s))"
    using assms unfolding inv_of_def Product_TA_Defs.product_ta_def N_s_def
    by (auto simp: inv_of_def p_def intro!: Product_TA_Defs.finite_invariant_of_product)

lemma range_prod_invariant:
  "range prod_invariant = range (I' s)"
  unfolding prod_invariant_def using I'_simp by auto

lemma finite_rangeI:
  assumes "\<forall>A\<in>{0..<p}. finite (range (snd (N ! A)))"
  shows "finite (range prod_invariant)"
  using assms by (metis finite_range_I' range_prod_invariant)

thm prod_trans_i_alt_def

end


context Equiv_TA_Defs
begin

thm defs.prod_trans_i_alt_def

lemma states'_len_simp[simp]:
  "length L = p" if "L \<in> defs.states' s"
  using that
  using Product_TA_Defs.states_length defs.N_s_def state_ta_def by fastforce

lemma [simp]:
  "length defs.N = p"
  unfolding state_ta_def by simp

 lemma [simp]:
  "defs.p = p"
  unfolding defs.p_def by simp

lemma P_Storec_iff:
  "(Some (INSTR (STOREC x xa)) = P pc) \<longleftrightarrow> (Some (STOREC x xa) = PF pc)"
  unfolding stripfp_def apply (cases "P pc")
   apply force
  subgoal for a
    by (cases a) auto
  done

(* XXX Unused but is explaining what is going on below *)
lemma product_trans_i_resets:
  "collect_clkvt (Product_TA_Defs.product_trans_i (defs.N_s s))
  \<subseteq> {c. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc}"
  unfolding collect_clkvt_def
  unfolding Product_TA_Defs.product_trans_i_def
  apply clarsimp
  unfolding defs.N_s_def
  unfolding trans_of_def
  unfolding defs.T_s_def
  unfolding state_ta_def
  unfolding state_trans_t_def
  unfolding make_f_def
  apply (clarsimp split: option.split_asm)
  by (auto dest: exec_reset simp: P_Storec_iff)

(* XXX Unused but is explaining what is going on below *)
lemma product_trans_s_resets:
  "collect_clkvt (Product_TA_Defs.product_trans_s (defs.N_s s))
  \<subseteq> {c. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc}"
  unfolding collect_clkvt_def
  unfolding Product_TA_Defs.product_trans_s_def
  apply clarsimp
  unfolding defs.N_s_def
  unfolding trans_of_def
  unfolding defs.T_s_def
  unfolding state_ta_def
  unfolding state_trans_t_def
  unfolding make_f_def
  apply (clarsimp split: option.split_asm)
  by (auto dest: exec_reset simp: P_Storec_iff)

lemma product_trans_resets:
  "collect_clkvt (\<Union>s. defs.T' s) \<subseteq> {c. \<exists> x pc. Some (INSTR (STOREC c x)) = P pc}"
  unfolding trans_of_def
  unfolding Product_TA_Defs.product_ta_def
  apply simp
  unfolding Product_TA_Defs.product_trans_def
  unfolding collect_clkvt_def
  apply safe
  unfolding Product_TA_Defs.product_trans_i_def Product_TA_Defs.product_trans_s_def
   apply clarsimp_all
  unfolding defs.N_s_def
  unfolding trans_of_def
  unfolding defs.T_s_def
  unfolding state_ta_def
  unfolding state_trans_t_def
  unfolding make_f_def
  apply (clarsimp_all split: option.split_asm)
  by (auto dest: exec_reset simp: P_Storec_iff)

lemma product_trans_guards:
  "Timed_Automata.collect_clkt (\<Union>s. defs.T' s)
  \<subseteq> {constraint_pair ac | ac. \<exists> pc. Some (CEXP ac) = P pc}"
  unfolding trans_of_def
  unfolding Product_TA_Defs.product_ta_def
  apply simp
  unfolding Product_TA_Defs.product_trans_def
  unfolding Timed_Automata.collect_clkt_def collect_clock_pairs_def
  apply safe
  unfolding Product_TA_Defs.product_trans_i_def Product_TA_Defs.product_trans_s_def
   apply clarsimp_all
  unfolding defs.N_s_def
  unfolding trans_of_def
  unfolding defs.T_s_def
  unfolding state_ta_def
  unfolding state_trans_t_def
  unfolding make_g_def
   apply (clarsimp_all split: option.split_asm)
  subgoal premises prems
    using prems(1,3-)
    unfolding set_map_filter
    by - (drule exec_pointers'; auto split: option.splits; auto split: instrc.split_asm; metis)
  subgoal premises prems
    using prems(1,2,4-)
    apply safe
    unfolding set_map_filter
    by (drule exec_pointers'; auto split: option.splits; auto split: instrc.split_asm; metis)+
  done

end

datatype bexp =
  not bexp | "and" bexp bexp | or bexp bexp | imply bexp bexp | -- "Boolean connectives"
  loc nat nat | -- "Is process p in location l?"
  eq nat int -- "Does var i equal x?" |
  le nat int |
  lt nat int |
  ge nat int |
  gt nat int

fun check_bexp :: "bexp \<Rightarrow> nat list \<Rightarrow> int list \<Rightarrow> bool" where
  "check_bexp (not a) L s \<longleftrightarrow> \<not> check_bexp a L s" |
  "check_bexp (and a b ) L s \<longleftrightarrow> check_bexp a L s \<and> check_bexp b L s" |
  "check_bexp (or a b ) L s \<longleftrightarrow> check_bexp a L s \<or> check_bexp b L s" |
  "check_bexp (imply a b ) L s \<longleftrightarrow> (check_bexp a L s \<longrightarrow> check_bexp b L s)" |
  "check_bexp (loc p l) L _ \<longleftrightarrow> L ! p = l" |
  "check_bexp (eq i x) _ s \<longleftrightarrow> s ! i = x" |
  "check_bexp (le i x) _ s \<longleftrightarrow> s ! i \<le> x" |
  "check_bexp (lt i x) _ s \<longleftrightarrow> s ! i < x" |
  "check_bexp (ge i x) _ s \<longleftrightarrow> s ! i \<ge> x" |
  "check_bexp (gt i x) _ s \<longleftrightarrow> s ! i > x"

datatype formula =
  EX bexp | EG bexp | AX bexp | AG bexp | Leadsto bexp bexp

abbreviation "repeat x n \<equiv> map (\<lambda> _. x) [0..<n]"

abbreviation "conv_prog P pc \<equiv> map_option (map_instrc real_of_int) (P pc)"
abbreviation "conv_A' \<equiv> \<lambda> (T, I). (T, conv_cc o I)"

subsection \<open>Pre-compiled networks with states and clocks as natural numbers\<close>
locale UPPAAL_Reachability_Problem_precompiled_defs =
  fixes p :: nat -- "Number of processes"
    and m :: nat -- "Number of clocks"
    (*
    and k :: "nat list list"
      -- "Clock ceiling. Maximal constant appearing in automaton for each state"
    *)
    and max_steps :: nat -- "Maximal number of execution for steps of programs in the automaton"
    and inv :: "(nat, int) cconstraint list list" -- "Clock invariants on locations per process"
    and pred :: "addr list list" -- "State invariants on locations per process"
    and trans :: "(addr * nat act * addr * nat) list list list"
      -- "Transitions between states per process"
    and prog :: "int instrc option list"
    and formula :: bexp -- "Model checking formula"
    and bounds :: "(int * int) list"
begin
  definition "clkp_set' \<equiv>
    \<Union> (collect_clock_pairs ` set (concat inv))
    \<union> {constraint_pair ac | ac. Some (CEXP ac) \<in> set prog}"
  definition clk_set'_def: "clk_set' =
    (fst ` clkp_set' \<union> {c. \<exists> x. Some (INSTR (STOREC c x)) \<in> set prog})"

  text \<open>Definition of the corresponding network\<close>
  definition "I i l \<equiv> if l < length (inv ! i) then inv ! i ! l else []"
  definition "T i \<equiv>
    {(l, trans ! i ! l ! j) | l j. l < length (trans ! i) \<and> j < length (trans ! i ! l)}"
  definition "P \<equiv> map (\<lambda> P l. P ! l) pred"
  definition "PROG pc \<equiv> (if pc < length prog then prog ! pc else None)"
  definition N :: "(nat, int, nat) unta" where
    "N \<equiv> (PROG, map (\<lambda> i. (T i, I i)) [0..<p], P, bounds)"
  definition "init \<equiv> repeat (0::nat) p"
  definition "F \<equiv> check_bexp formula"

  sublocale equiv: Equiv_TA_Defs N max_steps .

  thm equiv.defs.prod_trans_i_alt_def

  abbreviation "EA \<equiv> equiv.state_ta"

  abbreviation "A \<equiv> equiv.defs.prod_ta"

  lemma [simp]:
    "equiv.p = p"
    unfolding equiv.p_def N_def Equiv_TA_Defs.p_def by simp

  lemma [simp]:
    "length (equiv.defs.N_s s) = p"
    unfolding equiv.defs.N_s_def by simp

  lemma length_N[simp]:
    "length equiv.defs.N = p"
    by simp

  lemma
    "equiv.defs.I' s L = concat (map (\<lambda> q. if q < p then I q (L ! q) else []) [0..<length L])"
    unfolding inv_of_def
    unfolding Product_TA_Defs.product_ta_def
    apply simp
    unfolding Product_TA_Defs.product_invariant_def
    unfolding equiv.defs.N_s_def inv_of_def
    apply (rule arg_cong[where f = concat])
    unfolding Equiv_TA_Defs.state_ta_def
      apply simp
    unfolding N_def Equiv_TA_Defs.state_inv_def
      by simp

end (* End of definitions locale *)

  lemma snd_comp[simp]:
    "snd o (\<lambda> i. (f i, g i)) = g"
  by auto

locale UPPAAL_Reachability_Problem_precompiled =
  UPPAAL_Reachability_Problem_precompiled_defs +
  assumes process_length: "length inv = p" "length trans = p" "length pred = p"
    and lengths:
    "\<forall> i < p. length (pred ! i) = length (trans ! i) \<and> length (inv ! i) = length (trans ! i)"
    and state_set: "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, l) \<in> set xs. l < length T"
  assumes consts_nats: "snd ` clkp_set' \<subseteq> \<nat>"
  (* XXX This could also be subset for now but is left like this as an input sanity check right now *)
  assumes clock_set: "clk_set' = {1..m}"
    and p_gt_0: "p > 0"
    and m_gt_0: "m > 0"
    (* XXX Can get rid of these two? *)
    and processes_have_trans: "\<forall> i < p. trans ! i \<noteq> []" -- \<open>Necessary for refinement\<close>
    and start_has_trans: "\<forall> q < p. trans ! q ! 0 \<noteq> []" -- \<open>Necessary for refinement\<close>
  (* XXX Do not need this but a useful cautious check for the user? *)
  assumes resets_zero: "\<forall> x c. Some (INSTR (STOREC c x)) \<in> set prog \<longrightarrow> x = 0"

(*
locale UPPAAL_Reachability_Problem_precompiled =
  UPPAAL_Reachability_Problem_precompiled_raw +
  assumes discrete_state_finite: "\<forall> i < p. \<forall> l < length (trans ! i). finite {s. (pred ! i ! l) s}"
*)
begin

  lemma consts_nats':
    "\<forall> I \<in> set inv. \<forall> cc \<in> set I. \<forall> (c, d) \<in> collect_clock_pairs cc. d \<in> \<nat>"
    (* "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (g, _) \<in> set xs. \<forall> (c, d) \<in> collect_clock_pairs g. d \<in> \<nat>" *)
    "\<forall> ac. Some (CEXP ac) \<in> set prog \<longrightarrow> (snd (constraint_pair ac) \<in> \<nat>)"
    using consts_nats unfolding clkp_set'_def by force+

  thm equiv.defs.collect_clkt_prod_trans_subs
  thm equiv.defs.collect_clki_prod_invariant[of init]
  thm equiv.defs.collect_clkvt_prod_trans_subs

  term "range (snd (equiv.defs.N ! p))" term "snd (equiv.defs.N ! p)"
    term "set inv" term "set (concat inv)"
    term "equiv.defs.N"

  lemma clk_pairs_N_inv:
    "\<Union> (collect_clock_pairs ` range (snd x)) \<subseteq> \<Union> (collect_clock_pairs ` set (concat inv))"
    if "x \<in> set equiv.defs.N" for x
    using that
    unfolding equiv.state_ta_def equiv.state_inv_def
    unfolding equiv.p_def
    unfolding N_def
    unfolding I_def
    unfolding collect_clock_pairs_def
    using process_length(1) by (force dest!: nth_mem)

  lemma clkp_set_simp_1:
    "\<Union> (collect_clock_pairs ` set (concat inv)) \<supseteq> Timed_Automata.collect_clki (snd A)"
    unfolding equiv.defs.prod_ta_def inv_of_def
    apply (rule subset_trans)
     apply simp
     apply (rule equiv.defs.collect_clki_prod_invariant')
    unfolding Timed_Automata.collect_clki_def
    by (force dest!: nth_mem clk_pairs_N_inv)

  lemma clk_set_simp_2:
    "{c. \<exists> x. Some (INSTR (STOREC c x)) \<in> set prog} \<supseteq> collect_clkvt (trans_of A)"
    unfolding equiv.defs.prod_ta_def trans_of_def
    apply (rule subset_trans)
     apply simp
     apply (rule equiv.defs.collect_clkvt_prod_trans_subs)
    apply (rule subset_trans)
     apply (rule equiv.product_trans_resets)
    unfolding N_def PROG_def by (auto dest!: nth_mem) metis

  lemma clkp_set_simp_3:
    "{constraint_pair ac | ac. Some (CEXP ac) \<in> set prog} \<supseteq> Timed_Automata.collect_clkt (trans_of A)"
    unfolding equiv.defs.prod_ta_def trans_of_def
    apply (rule subset_trans)
     apply simp
     apply (rule equiv.defs.collect_clkt_prod_trans_subs)
    apply (rule subset_trans)
     apply (rule equiv.product_trans_guards)
    unfolding N_def PROG_def by (auto dest!: nth_mem)

  lemma clkp_set'_subs:
    "Timed_Automata.clkp_set A \<subseteq> clkp_set'"
    using clkp_set_simp_1 clkp_set_simp_3
    by (auto simp add: clkp_set'_def Timed_Automata.clkp_set_def inv_of_def)

  lemma clk_set'_subs:
    "clk_set A \<subseteq> clk_set'"
    using clkp_set'_subs clk_set_simp_2 by (auto simp: clk_set'_def)

  lemma clk_set:
    "clk_set A \<subseteq> {1..m}"
    using clock_set m_gt_0 clk_set'_subs by auto

  lemma
    "\<forall>(_, d)\<in>Timed_Automata.clkp_set A. d \<in> \<int>"
    unfolding Ints_def by auto

  lemma clkp_set'_consts_nat:
    "\<forall>(_, d)\<in>clkp_set'. d \<in> \<nat>"
    using consts_nats' unfolding clkp_set'_def
    apply auto
     apply force
    by (metis snd_conv)

  lemma clkp_set_consts_nat:
    "\<forall>(_, d)\<in>Timed_Automata.clkp_set A. d \<in> \<nat>"
    using clkp_set'_subs clkp_set'_consts_nat by auto

  lemma finite_clkp_set':
    "finite clkp_set'"
    unfolding clkp_set'_def
    using [[simproc add: finite_Collect]]
    by (auto simp: inj_on_def intro!: finite_vimageI)

  lemma finite_clkp_set_A[intro, simp]:
    "finite (Timed_Automata.clkp_set A)"
    using clkp_set'_subs finite_clkp_set' by (rule finite_subset)

  lemma clkp_set'_bounds:
    "a \<in> {Suc 0..m}" if "(a, b) \<in> clkp_set'"
    using that clock_set unfolding clk_set'_def by auto

  lemma finite_range_inv_of_A[intro, simp]:
    "finite (range (inv_of A))"
    unfolding inv_of_def equiv.defs.prod_ta_def
    apply simp
    apply (rule equiv.defs.finite_rangeI)
      apply simp
    unfolding Equiv_TA_Defs.state_ta_def
    apply simp
    unfolding equiv.state_inv_def
    unfolding N_def
    unfolding I_def
    by (auto intro: finite_subset[where B = "{[]}"])

  (* XXX Interesting for finiteness *)
  (* XXX Move *)
  lemma Collect_fold_pair:
    "{f a b | a b. P a b} = (\<lambda> (a, b). f a b) ` {(a, b). P a b}" for P
    by auto

  lemma finite_T[intro, simp]:
    "finite (trans_of A)"
  unfolding trans_of_def equiv.defs.prod_ta_def
  proof (simp, rule equiv.defs.finite_prod_trans, goal_cases)
    case (1 s)
    show "\<forall>l q. q < equiv.defs.p \<longrightarrow> (equiv.defs.P ! q) l s \<longrightarrow> (bounded equiv.B) s"
      apply simp
      unfolding equiv.state_ta_def equiv.state_pred_def
      by (simp split: option.split)
  next
    case 2
    show "finite {s. bounded equiv.B s}" by (rule equiv.bounded_finite)
  next
    case 3
    show ?case
    proof
      fix A assume A: "A \<in> set equiv.defs.N"
      have
        "{(l, j). l < length (trans ! i) \<and> j < length (trans ! i ! l)}
        = \<Union> ((\<lambda> l. {(l, j) | j. j < length (trans ! i ! l)}) ` {l. l < length (trans ! i)})" for i
        by auto
      then have "finite (T q)" if "q < p" for q
        using that unfolding T_def by (fastforce simp: Collect_fold_pair)
      then have "finite (fst (equiv.N ! q))" if "q < p" for q
        using that unfolding N_def by simp
      then have "finite (equiv.state_trans q)" if "q < p" for q
        using that
        unfolding Equiv_TA_Defs.state_trans_t_def
        using [[simproc add: finite_Collect]]
          by auto
      then show "finite (fst A)" using A unfolding Equiv_TA_Defs.state_ta_def by auto
    qed
  qed (auto simp: p_gt_0)

  sublocale Reachability_Problem_no_ceiling A "(init, s\<^sub>0)" "PR_CONST (\<lambda> (l, s). F l s)" m
    using clkp_set_consts_nat clk_set m_gt_0 by - (standard; blast)

  lemma [simp]:
    "length P = p"
    unfolding P_def using process_length(3) by simp

  lemma [simp]:
    "length equiv.I = p"
    unfolding N_def by simp

  lemma [simp]:
    "length equiv.N = p"
    unfolding N_def by simp

end (* End of locale *)

(*
context UPPAAL_Reachability_Problem_precompiled_defs
begin
  (*definition "clkp_set'' \<equiv>
    \<Union> (collect_clock_pairs ` set (concat inv))
    \<union> {constraint_pair ac | ac. Some (CEXP ac) \<in> set prog}"
*)

  definition "clkp_set'' i l \<equiv>
    collect_clock_pairs (inv ! i ! l) \<union> \<Union> ((\<lambda> (g, _). collect_clock_pairs g) ` set (trans ! i ! l))"

end
*)

(*
locale UPPAAL_Reachability_Problem_precompiled_ceiling =
  UPPAAL_Reachability_Problem_precompiled +
  fixes k :: "nat list list list"
  (*
    and k_length: "length k = p" "\<forall> l \<in> set k. length l = m + 1"
      -- \<open>Zero entry is just a dummy for the zero clock\<close>
    (* XXX Make this an abbreviation? *)
  assumes k_ceiling:
    (* "\<forall> c \<in> {1..m}. k ! c = Max ({d. (c, d) \<in> clkp_set'} \<union> {0})" *)
    "\<forall> (c, d) \<in> clkp_set'. int (k ! c) \<ge> d"
    "k ! 0 = 0"
  *)
begin

  definition
    "k_fun \<equiv> \<lambda> (l, s). \<lambda> c. if 0 < c \<and> c \<le> m then Max {k ! i ! (l ! i) ! c | i. i < p} else 0"

  lemma [intro, simp]:
    "k_fun st 0 = 0"
    unfolding k_fun_def by (simp split: prod.split)

  lemma [intro, simp]:
    "k_fun st i = 0" if "i > m"
    unfolding k_fun_def using that by (simp split: prod.split)

  lemma [intro]:
    "b \<le> int (k_fun a)" if "(a, b) \<in> clkp_set A"
    using that k_ceiling clkp_set'_subs k_length clkp_set'_bounds unfolding k_fun_def by force

  sublocale Reachability_Problem "(init, s\<^sub>0)" "PR_CONST (\<lambda> (l, s). F l s)" m A k_fun
    using clkp_set_consts_nat clk_set m_gt_0 apply - apply standard
       prefer 4 apply simp
      prefer 3 apply simp
      oops

end (* End of locale *)
*)

end (* End of theory *)