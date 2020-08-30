theory Program_Analysis_AbsInt
  imports
    UPPAAL_State_Networks_Impl
    TA_Library.More_Methods
    "HOL-Library.Lattice_Syntax"
    "AbsInt_Final"
    "UPPAAL_Asm_Assemble"
begin

definition "window_size \<equiv> (16::nat)"
definition "concretize_max \<equiv> (16::nat)"

lemma bounded_less_simp[simp]:
  "\<forall>q\<in>{..<p::nat}. P q \<equiv> \<forall> q < p. P q"
  by (rule eq_reflection) auto

definition[simp]: "cextract_prog prog i \<equiv> if i < length prog then prog ! i else None"

definition "lowest_top \<equiv> \<top>" (* TODO: make a better top *)

fun steps_approx_absint_state :: "nat \<Rightarrow> int instrc option list \<Rightarrow> addr * si_state \<Rightarrow> addr set" where
  "steps_approx_absint_state n cprog (pc, est) = domain (final_loopc window_size concretize_max (conv_prog (cextract_prog cprog)) n (single pc est))"

fun steps_approx_absint :: "nat \<Rightarrow> int instrc option list \<Rightarrow> addr \<Rightarrow> addr set" where
  "steps_approx_absint (Suc n) cprog pc = steps_approx_absint_state n cprog (pc, lowest_top)" |
  "steps_approx_absint 0 _ _ = {}"

lemma steps_approx_absint_finite: "steps_approx_absint n prog pc = \<top> \<or> finite (steps_approx_absint n prog pc)"
proof (cases "steps_approx_absint n prog pc = \<top>")
  case False
  then show ?thesis
  proof (cases n)
    case (Suc nn)
    let ?res = "final_loopc window_size concretize_max (conv_prog (cextract_prog prog)) nn (single pc lowest_top)"
    have "finite (domain (single pc lowest_top))" using single_domain by simp
    hence a: "single pc lowest_top = \<top> \<or> finite (domain (single pc lowest_top))" by blast
    have "?res = \<top> \<or> finite (domain ?res)"
      unfolding final_loopc_def using finite_loop_finite[OF a] .
    then show ?thesis
    proof (rule disjE, goal_cases)
      case 1
      hence "domain ?res = \<top>" using option_domain_top by simp
      then show ?case using Suc by simp
    next
      case 2
      then show ?case using Suc by simp
    qed
  qed simp
qed blast

context
  fixes prog :: "int instrc option list"
begin

private abbreviation "P i \<equiv> if i < length prog then prog ! i else None"

lemma stepsc_steps_approx:
  assumes "stepsc (conv_prog P) n u (pc, st, s, f, rs) (pc', st', s', f', rs')"
  shows "pc' \<in> steps_approx_absint n prog pc"
proof -
  from assms obtain nn where suc: "n = Suc nn" using stepsc.cases by blast
  hence "stepsc (conv_prog P) (Suc nn) u (pc, st, s, f, rs) (pc', st', s', f', rs')" using assms(1) by simp
  moreover have "(st, s, f, rs) \<in> final_\<gamma> window_size lowest_top" by (simp add: lowest_top_def)
  ultimately have "pc' \<in> domain (final_loopc window_size concretize_max (conv_prog P) nn (single pc lowest_top))" by (rule final_loop_stepsc_pc)
  hence "pc' \<in> domain (final_loopc window_size concretize_max (conv_prog P) nn (single pc lowest_top))" .
  thus ?thesis using suc by simp
qed

definition
  "time_indep_check_absint pc n \<equiv>
    \<forall> pc' \<in> steps_approx_absint n prog pc. pc' < length prog
    \<longrightarrow> (case prog ! pc' of Some cmd \<Rightarrow> is_instr cmd | _ \<Rightarrow> True)"

lemma time_indep_overapprox:
  assumes
    "time_indep_check_absint pc n"
  shows "time_indep (conv_prog P) n (pc, st, s, f, rs)"
proof -
  { fix pc' st' s' f' rs' cmd u
    assume A:
      "stepsc (conv_prog local.P) n u (pc, st, s, f, rs) (pc', st', s', f', rs')"
      "conv_prog local.P pc' = Some cmd"
    have "is_instr cmd"
    proof (cases "pc' < length prog")
      case True
      with A(2) obtain cmd' where "prog ! pc' = Some cmd'" by auto
      with True stepsc_steps_approx[OF A(1)] A(2) assms show ?thesis
        by (cases cmd') (auto simp: time_indep_check_absint_def)
    next
      case False
      with A(2) show ?thesis by (auto split: option.split_asm)
    qed
  }
  then show ?thesis unfolding time_indep_def by blast
qed

end (* End of context for fixed program *)

context UPPAAL_Reachability_Problem_precompiled_defs
begin

  definition
    "collect_cexp' pc = {ac. Some (CEXP ac) \<in> ((!) prog) ` steps_approx_absint max_steps prog pc}"

  definition "clkp_set'' i l \<equiv>
    collect_clock_pairs (inv ! i ! l) \<union>
    \<Union> ((\<lambda> (g, _). constraint_pair ` collect_cexp' g) ` set (trans ! i ! l))"

  definition
    "collect_cexp = {ac. Some (CEXP ac) \<in> set prog}"

  definition
    "collect_store' pc =
    {(c, x). Some (INSTR (STOREC c x)) \<in> ((!) prog) ` steps_approx_absint max_steps prog pc}"

end

(* XXX Unused *)
(* XXX Move *)
lemma visited_resets_mono:
  "set r \<subseteq> set r'" if "visited P n (pc, st, s, f, r) (pc', st', s', f', r') pcs"
  using that
  apply (
    induction P \<equiv> P n "(pc, st, s, f, r :: nat list)" "(pc', st', s', f', r')" pcs
    arbitrary: pc st s f r  rule: visited.induct
    )
   apply blast
  by (erule step.elims; force split: option.splits if_splits elim!: step.elims)+

(* XXX Unused *)
(* XXX Move *)
lemma visitedc_resets_mono:
  "set r \<subseteq> set r'" if "visitedc P n u (pc, st, s, f, r) (pc', st', s', f', r') pcs"
  using that
  apply (
    induction P \<equiv> P n u "(pc, st, s, f, r :: nat list)" "(pc', st', s', f', r')" pcs
    arbitrary: pc st s f r  rule: visitedc.induct
    )
   apply blast
  by (erule stepc.elims; force split: option.splits if_splits elim!: step.elims)+

(* XXX Move *)
lemma visited_reset:
  "\<exists> x. \<exists> pc \<in> set pcs. Some (STOREC c x) = P pc"
  if "visited P n (pc, st, s, f, r) (pc', st', s', f', r') pcs" "c \<in> set r' - set r"
  using that
  apply (
      induction P \<equiv> P n "(pc, st, s, f, r :: nat list)" "(pc', st', s', f', r')" pcs
      arbitrary: pc st s f r rule: visited.induct
      )
   apply blast
  by (erule step.elims; force split: option.split_asm if_split_asm elim!: step.elims)

(* XXX Move *)
lemma visitedc_reset:
  "\<exists> x. \<exists> pc \<in> set pcs. Some (INSTR (STOREC c x)) = P pc"
  if "visitedc P n u (pc, st, s, f, r) (pc', st', s', f', r') pcs" "c \<in> set r' - set r"
  using that
  apply (
      induction P \<equiv> P n u "(pc, st, s, f, r :: nat list)" "(pc', st', s', f', r')" pcs
      arbitrary: pc st s f r rule: visitedc.induct
      )
   apply blast
  by (erule stepc.elims; force split: option.split_asm if_split_asm elim!: step.elims)

(* TTT Automate *)
lemma visited_fuel_mono:
  "visited P n' s s' pcs" if "visited P n s s' pcs" "n' \<ge> n"
  using that
  apply (induction arbitrary: n')
  subgoal for _ _ _ n'
    by (cases n') (auto intro: visited.intros)
  subgoal for _ _ _ _ _ _ _ _ _ _ _ n'
    by (cases n') (auto intro: visited.intros)
  done

(* TTT Automate *)
lemma visitedc_fuel_mono:
  "visitedc P n' u s s' pcs" if "visitedc P n u s s' pcs" "n' \<ge> n"
  using that
  apply (induction arbitrary: n')
  subgoal for _ _ _ _ n'
    by (cases n') (auto intro: visitedc.intros)
  subgoal for _ _ _ _ _ _ _ _ _ _ _ _ n'
    by (cases n') (auto intro: visitedc.intros)
  done

lemma visted_split:
  assumes "visited P n (pc, st, s, f, r) s'' (pcs' @ pc' # pcs)"
  obtains st' s' f' r' where
    "visited P n (pc, st, s, f, r) (pc', st', s', f', r') pcs"
    "visited P n (pc', st', s', f', r') s'' (pcs' @ [pc'])"
  using assms
    apply atomize_elim
  proof (induction _ _ _ _ "pcs' @ pc' # pcs" arbitrary: pcs rule: visited.induct)
    case (1 prog n u start)
    then show ?case by simp
  next
    case prems: (2 cmd pc st m f rs s prog n s' pcs pcs'')
    show ?case
    proof (cases "pcs'' = []")
      case True
      with prems show ?thesis by (blast intro: visited.intros)
    next
      case False
      with \<open>pcs @ [pc] = _\<close> obtain pcs3 where "pcs'' = pcs3 @ [pc]"
        by (metis append_butlast_last_id last_ConsR last_append last_snoc list.distinct(1))
      with prems obtain st' s'a f' r' where
        "visited prog n s (pc', st', s'a, f', r') pcs3"
        "visited prog n (pc', st', s'a, f', r') s' (pcs' @ [pc'])"
        by (auto 9 2)
      with prems \<open>pcs'' = _\<close> show ?thesis by (auto 4 6 intro: visited.intros visited_fuel_mono)
    qed
  qed

lemma visited_steps':
  assumes "visited P n (pc, st, s, f, r) s'' pcs" "pc' \<in> set pcs"
  obtains st' s' f' r' where "steps P n (pc, st, s, f, r) (pc', st', s', f', r')"
  using assms by (force dest!: split_list dest: visited_steps elim: visted_split)

lemma vistedc_split:
  assumes "visitedc P n u (pc, st, s, f, r) s'' (pcs' @ pc' # pcs)"
  obtains st' s' f' r' where
    "visitedc P n u (pc, st, s, f, r) (pc', st', s', f', r') pcs"
    "visitedc P n u (pc', st', s', f', r') s'' (pcs' @ [pc'])"
  using assms
    apply atomize_elim
  proof (induction _ _ _ _ _ "pcs' @ pc' # pcs" arbitrary: pcs rule: visitedc.induct)
    case (1 prog n u start)
    then show ?case by simp
  next
    case prems: (2 cmd u pc st m f rs s prog n s' pcs pcs'')
    show ?case
    proof (cases "pcs'' = []")
      case True
      with prems show ?thesis by (blast intro: visitedc.intros)
    next
      case False
      with \<open>pcs @ [pc] = _\<close> obtain pcs3 where "pcs'' = pcs3 @ [pc]"
        by (metis append_butlast_last_id last_ConsR last_append last_snoc list.distinct(1))
      with prems obtain st' s'a f' r' where
        "visitedc prog n u s (pc', st', s'a, f', r') pcs3"
        "visitedc prog n u (pc', st', s'a, f', r') s' (pcs' @ [pc'])"
        by (auto 9 2)
      with prems \<open>pcs'' = _\<close> show ?thesis by (auto 4 6 intro: visitedc.intros visitedc_fuel_mono)
    qed
  qed

lemma visitedc_stepsc':
  assumes "visitedc P n u (pc, st, s, f, r) s'' pcs" "pc' \<in> set pcs"
  obtains st' s' f' r' where "stepsc P n u (pc, st, s, f, r) (pc', st', s', f', r')"
  using assms  by (force dest!: split_list dest: visitedc_stepsc elim: vistedc_split)

(* XXX Automate *)
lemma steps_fuel_mono:
  "steps P n' s s'" if "steps P n s s'" "n' \<ge> n"
  using that
  apply (induction arbitrary: n')
  subgoal for _ _ _ n'
    by (cases n') auto
  subgoal for _ _ _ _ _ _ _ _ _ _ n'
    by (cases n') auto
  done

lemma exec_steps':
  assumes "exec prog n s pcs = Some (s', pcs')" "pc' \<in> set pcs' - set pcs"
  obtains st m f rs where "steps prog n s (pc', st, m, f, rs)"
  using assms
    apply atomize_elim
proof (induction P \<equiv> prog n s pcs arbitrary: s' rule: exec.induct)
  case 1
  then show ?case by simp
next
  case (2 n pc st m f rs pcs)
  then obtain instr where "prog pc = Some instr" by (cases "prog pc") auto
  show ?case
  proof (cases "instr = HALT")
    case True
    with "2.prems" \<open>prog pc = _\<close> show ?thesis by (auto; blast)
  next
    case F: False
    show ?thesis
    proof (cases "pc' = pc")
      case True
      with \<open>prog pc = _\<close> show ?thesis by (auto; blast)
    next
      case False
      (* XXX A lot of implicit forward reasoning hides in here *)
      with \<open>prog pc = _\<close> 2(2,3) F show ?thesis
        by - (
          erule exec.elims;
          auto 5 6
            dest!: 2(1)[OF \<open>prog pc = _\<close> F, rotated, OF sym]
            simp: option.split_asm if_split_asm
          )
    qed
  qed
qed

lemma exec_visited:
  assumes "exec prog n s pcs = Some ((pc, st, m, f, rs), pcs')"
  obtains pcs'' where
    "visited prog n s (pc, st, m, f, rs) pcs'' \<and> pcs' = pc # pcs'' @ pcs \<and> prog pc = Some HALT"
  apply atomize_elim
  using assms proof (induction P \<equiv> prog n s pcs arbitrary: pc st m f rs rule: exec.induct)
  case 1
  then show ?case by simp
next
  case (2 n pc' st' m' f' rs' pcs')
  then obtain instr where "prog pc' = Some instr" by (cases "prog pc'") auto
  show ?case
  proof (cases "instr = HALT")
    case True
    with "2.prems" \<open>prog pc' = _\<close> show ?thesis by (auto elim: exec.elims intro: visited.intros)
  next
    case False
    with 2(2) \<open>prog pc' = _\<close> show ?thesis
      by - (
          erule exec.elims;
          auto split: option.split_asm if_split_asm intro: visited.intros
          dest!: 2(1)[OF \<open>prog pc' = _\<close> False, rotated, OF sym]
          )
  qed
qed

lemma exec_reset':
  "\<exists> x. \<exists> pc \<in> set pcs'. Some (STOREC c x) = P pc"
  if "exec P n (pc, st, s, f, r) pcs = Some ((pc', st', s', f', r'), pcs')" "c \<in> set r' - set r"
proof -
  from exec_visited[OF that(1)] obtain pcs'' where *:
    "visited P n (pc, st, s, f, r) (pc', st', s', f', r') pcs''"
    "pcs' = pc' # pcs'' @ pcs \<and> P pc' = Some HALT"
    by auto
  from visited_reset[OF this(1) that(2)] obtain x pc where
    "pc\<in>set pcs''" "Some (STOREC c x) = P pc"
    by auto
  with *(2) show ?thesis by auto
qed

(*
lemma steps_approx_out_of_range:
  "steps_approx_absint n prog pc = {}" if "pc \<ge> length prog"
  using that by (induction n) auto
*)

lemma steps_resets_mono:
  "set r \<subseteq> set r'" if "steps P n (pc, st, s, f, r) (pc', st', s', f', r')"
  using that
  by (induction "(pc, st, s, f, r)" "(pc', st', s', f', r')" arbitrary: pc st s f r;
      fastforce intro: visited.intros elim!: step.elims split: if_split_asm)

lemma resets_start:
  assumes
    "\<forall> pc \<in> {pc..pc'}. \<exists> c x. prog ! pc = Some (INSTR (STOREC c x))"
    "steps
      (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None))
      n (pc, st, s, f, r) (pc_t, st', s', f', r')"
    "prog ! pc_t = Some (INSTR HALT)"
  shows "{c. \<exists> x. \<exists> pc \<in> {pc .. pc'}. prog ! pc = Some (INSTR (STOREC c x))} \<subseteq> set r'"
    using assms(2,3,1)
  proof (induction
    "(map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None))" n "(pc, st, s, f, r)"
    "(pc_t, st', s', f', r')" arbitrary: pc st s f r
    )
      case prems: 1
      show ?case
      proof (cases "pc' \<ge> pc_t")
        case True (* XXX Automate forward step *)
        with prems obtain c x where "prog ! pc_t = Some (INSTR (STOREC c x))"
          by fastforce
        with prems show ?thesis by simp
      next
        case False
        with prems show ?thesis by auto
      qed
    next
      case prems: (2 cmd pc st m f rs s n)
      show ?case
      proof (cases "pc' \<ge> pc")
        case True (* XXX Automate forward step *)
        with prems(6) obtain c d where "prog ! pc = Some (INSTR (STOREC c d))"
          by fastforce
        moreover obtain pc1 st' s' f' r1 where "s = (pc1, st', s', f', r1)"
          using prod.exhaust by metis
        ultimately have "pc1 = pc + 1"
          using prems(1,2) by (auto elim!: step.elims split: if_split_asm)
        with prems(4)[OF \<open>s = _\<close> prems(5)] prems(6) have
          "{c. \<exists>x. \<exists>pc\<in>{pc1..pc'}. prog ! pc = Some (INSTR (STOREC c x))} \<subseteq> set r'"
          by auto
        moreover have "c \<in> set r1"
          using prems(1,2) \<open>s = _\<close> \<open>prog ! pc = _\<close> by (auto elim!: step.elims split: if_split_asm)
        moreover then have "c \<in> set r'"
          using prems(3) \<open>s = _\<close> by (auto dest: steps_resets_mono)
        ultimately show ?thesis
          using \<open>pc1 = _\<close> \<open>prog ! pc = _\<close> apply clarsimp
          subgoal for _ _ pc''
            by (cases "pc'' = pc"; force)
          done
      next
        case False
        then show ?thesis by auto
      qed
    qed

function find_resets_start where
  "find_resets_start prog pc =
    (
    if pc < length prog
    then
      case prog ! pc of
        Some (INSTR (STOREC c x)) \<Rightarrow> (Some pc \<squnion> find_resets_start prog (pc + 1)) |
        _ \<Rightarrow> None
    else None
    )
  "
  by auto

termination
  by (relation "measure (\<lambda> (prog, pc). length prog - pc)") auto

lemma find_resets_start:
  "\<forall> pc \<in> {pc..pc'}. \<exists> c x. prog ! pc = Some (INSTR (STOREC c x))" if
  "find_resets_start prog pc = Some pc'"
  using that
  proof (induction arbitrary: pc' rule: find_resets_start.induct)
    case prems: (1 prog pc)
    from prems(2) show ?case
      apply (simp split: if_split_asm option.split_asm instrc.split_asm)
      apply (
          auto simp del: find_resets_start.simps simp: le_max_iff_disj sup_nat_def sup_option_def
          split: option.split_asm instr.split_asm dest!: prems(1)
          )
      by (metis atLeastAtMost_iff le_antisym not_less_eq_eq)
  qed

lemmas resets_start' = resets_start[OF find_resets_start]

context UPPAAL_Reachability_Problem_precompiled_defs
begin

  definition
    "collect_store'' pc \<equiv>
    case find_resets_start prog pc of
      None \<Rightarrow> {} |
      Some pc' \<Rightarrow>
        {(c, x). Some (INSTR (STOREC c x)) \<in> ((!) prog) ` {pc .. pc'}}"

end

(* XXX Move to Misc *)
(* XXX Unused *)
lemma bexp_atLeastAtMost_iff:
  "(\<forall> pc \<in> {pc_s..pc_t}. P pc) \<longleftrightarrow> (\<forall> pc. pc_s \<le> pc \<and> pc \<le> pc_t \<longrightarrow> P pc)"
  by auto

(* XXX Move to Misc *)
(* XXX Unused *)
lemma bexp_atLeastLessThan_iff:
  "(\<forall> pc \<in> {pc_s..<pc_t}. P pc) \<longleftrightarrow> (\<forall> pc. pc_s \<le> pc \<and> pc < pc_t \<longrightarrow> P pc)"
  by auto

lemma guaranteed_execution:
  assumes
    "\<forall> pc \<in> {pc..<pc_t}.
      prog ! pc \<noteq> None
      \<and> prog ! pc \<notin> Some ` INSTR `
        {STORE, HALT, POP, CALL, RETURN, instr.AND, instr.NOT, instr.ADD, instr.LT, instr.LE, instr.EQ}
      \<and> (\<nexists>c d. prog ! pc = Some (INSTR (STOREI c d)))
      \<and> (\<nexists>c. prog ! pc = Some (INSTR (LID c)))
      \<and> (\<forall> c d. prog ! pc = Some (INSTR (STOREC c d)) \<longrightarrow> d = 0)
      "
    "\<forall> pc \<in> {pc..<pc_t}. \<forall> pc'. prog ! pc = Some (INSTR (JMPZ pc')) \<longrightarrow> pc' > pc \<and> pc' \<le> pc_t"
    "prog ! pc_t = Some (INSTR HALT)" "pc_t \<ge> pc" "n > pc_t - pc" "pc_t < length prog"
  shows "\<exists> st' s' f' r'. steps
      (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None))
      n (pc, st, s, f, r) (pc_t, st', s', f', r')"
  using assms
proof (induction "pc_t - pc" arbitrary: pc st s f r n rule: less_induct)
  case less
  let ?prog = "(map_option stripf \<circ> (\<lambda>pc. if pc < length prog then prog ! pc else None))"
  from \<open>pc_t - pc < n\<close> obtain n' where [simp]: "n = Suc n'" by (cases n) auto
  from less.prems(3-) have [simp]: "pc < length prog" "pc_t < length prog" by auto
  show ?case
  proof (cases "pc_t = pc")
    case True
    then show ?thesis by force
  next
    case False
    with less.prems(1,4) have valid_instr:
      "prog ! pc \<notin> Some ` INSTR `
       {STORE, HALT, POP, CALL, RETURN, instr.AND, instr.NOT, instr.ADD, instr.LT, instr.LE, instr.EQ}"
      "\<nexists>c d. prog ! pc = Some (INSTR (STOREI c d))"
      "\<nexists>c. prog ! pc = Some (INSTR (LID c))"
      "prog ! pc \<noteq> None"
      by auto
    from \<open>pc \<le> _\<close> \<open>pc_t \<noteq> _\<close> less.prems(2) have jumps:
      "pc' > pc \<and> pc' \<le> pc_t" if "prog ! pc = Some (INSTR (JMPZ pc'))" for pc'
      using that by fastforce
    from \<open>pc \<le> _\<close> \<open>pc_t \<noteq> _\<close> less.prems(1) have stores:
      "d = 0" if "prog ! pc = Some (INSTR (STOREC c d))" for c d
      using that by fastforce
    show ?thesis
    proof (cases "prog ! pc")
      case None
      from \<open>pc_t \<noteq> _\<close> less.prems(1,4) have "prog ! pc \<noteq> None"
        by simp
      with None show ?thesis by auto
    next
      case (Some a)
      then show ?thesis
      proof (cases a)
        case (INSTR instr)
        have *:
          "\<exists>st' s' f' r'. steps ?prog n' (pc', st, s, f, r) (pc_t, st', s', f', r')"
          if "pc < pc'" "pc' \<le> pc_t" for pc' st s f r
          apply (rule less.hyps[of pc'])
          subgoal
            using that by simp
          subgoal
            using that less.prems(1) by force
          subgoal
            apply clarsimp
            subgoal premises prems for pc_s pc'
            proof -
              from prems that have "pc_s \<in> {pc..<pc_t}" by simp
              with prems(1) less.prems(2) show ?thesis by blast
            qed
            done
          using \<open>prog ! pc_t = _\<close> \<open>pc_t - pc < n\<close> that by auto
        from \<open>pc_t \<noteq> pc\<close> \<open>pc \<le> _\<close> have "Suc pc \<le> pc_t" by simp
        then obtain pc' st' s' f' r' where
          "step instr (pc, st, s, f, r) = Some (pc', st', s', f', r')" "pc < pc'" "pc' \<le> pc_t"
          apply atomize_elim
          apply (cases instr)
          using valid_instr \<open>a = _\<close> \<open>_ = Some a\<close> by (auto simp: stores jumps)
        with \<open>a = _\<close> \<open>_ = Some a\<close> show ?thesis by (force dest!: *)
      next
        case (CEXP x2)
        have *:
          "\<exists>st' s' f' r'. steps ?prog n' (Suc pc, st, s, f, r) (pc_t, st', s', f', r')"
          if "Suc pc \<le> pc_t" for st s f r
          apply (rule less.hyps[of "Suc pc"])
          subgoal
            using \<open>pc \<le> _\<close> \<open>pc_t \<noteq> pc\<close> by simp
          subgoal
            using less.prems(1) by force
          subgoal
            apply clarsimp
            subgoal premises prems for pc_s pc'
            proof -
              from prems have "pc_s \<in> {pc..<pc_t}" by simp
              with prems(1) less.prems(2) show ?thesis by blast
            qed
            done
          using \<open>prog ! pc_t = _\<close> \<open>pc_t - pc < n\<close> that by auto
        from \<open>pc_t \<noteq> pc\<close> \<open>pc \<le> _\<close> have "Suc pc \<le> pc_t" by simp
        with \<open>a = _\<close> \<open>_ = Some a\<close> show ?thesis by (force dest!: *)
      qed
    qed
  qed
qed

function find_next_halt where
  "find_next_halt prog pc =
    (
    if pc < length prog
    then
      case prog ! pc of
        Some (INSTR HALT) \<Rightarrow> Some pc |
        _ \<Rightarrow> find_next_halt prog (pc + 1)
    else None
    )
  "
  by auto

termination
  by (relation "measure (\<lambda> (prog, pc). length prog - pc)") auto

lemma find_next_halt_finds_halt:
  "prog ! pc' = Some (INSTR HALT) \<and> pc \<le> pc' \<and> pc' < length prog"
  if "find_next_halt prog pc = Some pc'"
using that proof (induction prog pc rule: find_next_halt.induct)
  case prems: (1 prog pc)
  from prems(21) show ?case
    by (
        simp,
        simp
        split: if_split_asm option.split_asm instrc.split_asm instr.split_asm
        del: find_next_halt.simps;
        fastforce dest: prems(1-20) simp del: find_next_halt.simps)
qed

definition
  "guaranteed_execution_cond prog pc_s n \<equiv>
    case find_next_halt prog pc_s of
      None \<Rightarrow> False |
      Some pc_t \<Rightarrow>
       (
       \<forall> pc \<in> {pc_s..<pc_t}.
          prog ! pc \<noteq> None
          \<and> prog ! pc \<notin> Some ` INSTR `
            {NOP, STORE, HALT, POP, CALL, RETURN, instr.AND, instr.NOT, instr.ADD, instr.LT, instr.LE, instr.EQ}
          \<and> (\<forall> c d. prog ! pc = Some (INSTR (STOREC c d)) \<longrightarrow> d = 0)
          \<and> (\<forall> c d. prog ! pc = Some (INSTR (STOREI c d)) \<longrightarrow> False)
          \<and> (\<forall> c. prog ! pc = Some (INSTR (LID c)) \<longrightarrow> False)
        ) \<and>
        (\<forall> pc \<in> {pc_s..<pc_t}. \<forall> pc'. prog ! pc = Some (INSTR (JMPZ pc')) \<longrightarrow> pc' > pc \<and> pc' \<le> pc_t)
       \<and> n > pc_t - pc_s
  "

lemma guaranteed_execution_cond_alt_def[code]:
  "guaranteed_execution_cond prog pc_s n \<equiv>
    case find_next_halt prog pc_s of
      None \<Rightarrow> False |
      Some pc_t \<Rightarrow>
       (
       \<forall> pc \<in> {pc_s..<pc_t}.
          prog ! pc \<noteq> None
          \<and> prog ! pc \<notin> Some ` INSTR `
            {NOP, STORE, HALT, POP, CALL, RETURN, instr.AND, instr.NOT, instr.ADD, instr.LT, instr.LE, instr.EQ}
          \<and> (case prog ! pc of Some (INSTR (STOREC c d)) \<Rightarrow> d = 0 | _ \<Rightarrow> True)
          \<and> (case prog ! pc of Some (INSTR (STOREI c d)) \<Rightarrow> False | _ \<Rightarrow> True)
          \<and> (case prog ! pc of Some (INSTR (LID c)) \<Rightarrow> False | _ \<Rightarrow> True)
        ) \<and>
        (\<forall> pc \<in> {pc_s..<pc_t}.
          case prog ! pc of Some (INSTR (JMPZ pc')) \<Rightarrow> pc' > pc \<and> pc' \<le> pc_t | _ \<Rightarrow> True)
       \<and> n > pc_t - pc_s
  "
proof (rule eq_reflection, goal_cases)
  case 1
  have *:
    "(\<forall> c d. prog ! pc = Some (INSTR (STOREC c d)) \<longrightarrow> d = 0) \<longleftrightarrow>
     (case prog ! pc of Some (INSTR (STOREC c d)) \<Rightarrow> d = 0 | _ \<Rightarrow> True)" for pc
    by (auto split: option.split instrc.split instr.split)
  have **:
    "(\<forall> pc'. prog ! pc = Some (INSTR (JMPZ pc')) \<longrightarrow> pc' > pc \<and> pc' \<le> pc_t) \<longleftrightarrow>
     (case prog ! pc of Some (INSTR (JMPZ pc')) \<Rightarrow> pc' > pc \<and> pc' \<le> pc_t | _ \<Rightarrow> True)" for pc pc_t
    by (auto split: option.split instrc.split instr.split)
  have ***:
    "(\<forall> c d. prog ! pc = Some (INSTR (STOREI c d)) \<longrightarrow> False) \<longleftrightarrow>
     (case prog !pc of Some (INSTR (STOREI c d)) \<Rightarrow> False | _ \<Rightarrow> True)" for pc
    by (auto split: option.split instrc.split instr.split)
  have ****:
    "(\<forall> c. prog ! pc = Some (INSTR (LID c)) \<longrightarrow> False) \<longleftrightarrow>
     (case prog !pc of Some (INSTR (LID c)) \<Rightarrow> False | _ \<Rightarrow> True)" for pc
    by (auto split: option.split instrc.split instr.split)
  show ?case unfolding guaranteed_execution_cond_def * ** *** **** ..
qed

lemma guaranteed_execution':
  "\<exists> pc_t st' s' f' r' pcs'. exec
      (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None))
      n (pc, st, s, f, r) pcs = Some ((pc_t, st', s', f', r'), pcs')"
  if "guaranteed_execution_cond prog pc n"
proof -
  from that obtain pc_t where "find_next_halt prog pc = Some pc_t"
    unfolding guaranteed_execution_cond_def bexp_atLeastAtMost_iff
    by (auto split: option.split_asm)
  then have "prog ! pc_t = Some (INSTR HALT) \<and> pc \<le> pc_t \<and> pc_t < length prog"
    by (rule find_next_halt_finds_halt)
  moreover then have "\<exists> st' s' f' r'. steps
      (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None))
      n (pc, st, s, f, r) (pc_t, st', s', f', r')"
    using \<open>_ = Some pc_t\<close> that
    unfolding guaranteed_execution_cond_def bexp_atLeastAtMost_iff
    by - (rule guaranteed_execution, auto)
  ultimately show ?thesis by (force dest: steps_exec)
  qed

(*
context UPPAAL_Reachability_Problem_precompiled_defs
begin

  lemma collect_cexp_alt_def:
    "collect_cexp =
      set (List.map_filter
        (\<lambda> x. case x of Some (CEXP ac) \<Rightarrow> Some ac | _ \<Rightarrow> None)
         prog)"
    unfolding collect_cexp_def set_map_filter by (auto split: option.split_asm instrc.split_asm)

  lemma clkp_set'_alt_def:
    "clkp_set' =
      \<Union> (collect_clock_pairs ` set (concat inv)) \<union> (constraint_pair ` collect_cexp)"
    unfolding clkp_set'_def collect_cexp_def by auto

  definition
    "collect_store = {(c, x). Some (INSTR (STOREC c x)) \<in> set prog}"

  lemma collect_store_alt_def:
    "collect_store =
      set (List.map_filter
        (\<lambda> x. case x of Some (INSTR (STOREC c x)) \<Rightarrow> Some (c, x) | _ \<Rightarrow> None)
         prog)"
    unfolding collect_store_def set_map_filter
    by (auto split: option.split_asm instrc.split_asm instr.split_asm)

  lemma clk_set'_alt_def: "clk_set' = (fst ` clkp_set' \<union> fst ` collect_store)"
    unfolding clk_set'_def collect_store_def by auto

end
*)

fun conj_instr :: "'t instrc \<Rightarrow> addr \<Rightarrow> bool" where
  "conj_instr (CEXP _) _ = True" |
  "conj_instr (INSTR COPY) _ = True" |
  "conj_instr (INSTR (JMPZ pc)) pc_t = (pc = pc_t)" |
  "conj_instr (INSTR instr.AND) _ = True" |
  "conj_instr _ _ = False"

(*
inductive is_conj_block :: "'t instrc option list \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> bool" where
  (* "is_conj_block prog pc pc" if "prog ! pc = Some (INSTR HALT)" | *)
  "is_conj_block prog pc (pc' + 1)" if
  "prog ! (pc' + 1) = Some (INSTR HALT)" "is_conj_block prog pc pc'" |
  "is_conj_block prog pc pc" if "prog ! pc = Some (CEXP ac)" |
  "is_conj_block prog pc (pc' + 3)" if
  "prog ! (pc' + 1) = Some (INSTR COPY)" "prog ! (pc' + 2) = Some (CEXP ac)"
  "prog ! (pc' + 3) = Some (INSTR instr.AND)"
  "is_conj_block prog pc pc'" |
  "is_conj_block prog pc (pc' + 4)" if
  "prog ! (pc' + 1) = Some (INSTR COPY)"
  "prog ! (pc' + 2) = Some (INSTR (JMPZ pc_t))" "prog ! pc_t = Some (INSTR HALT)"
  "prog ! (pc' + 3) = Some (CEXP ac)" "prog ! (pc' + 4) = Some (INSTR instr.AND)"
  "is_conj_block prog pc pc'"
*)

inductive is_conj_block' :: "'t instrc option list \<Rightarrow> addr \<Rightarrow> addr \<Rightarrow> bool" where
  "is_conj_block' prog pc pc" if
  "pc < length prog"
  "prog ! pc = Some (INSTR HALT)" |
  (*
  "is_conj_block' prog pc (pc + 2)" if
  "pc + 2 < length prog"
  "prog ! (pc) = Some (INSTR COPY)" "prog ! (pc + 1) = Some (CEXP ac)"
  "prog ! (pc + 2) = Some (INSTR instr.AND)" |
  *)
  (*
  "is_conj_block' prog pc (pc' + 2)" if
  "pc' + 2 < length prog"
  "prog ! (pc') = Some (INSTR COPY)" "prog ! (pc' + 1) = Some (CEXP ac)"
  "prog ! (pc' + 2) = Some (INSTR instr.AND)"
  "is_conj_block' prog pc pc'"
  *)
  "is_conj_block' prog pc pc'" if
  "pc' < length prog"
  "prog ! pc = Some (INSTR COPY)" "prog ! (pc + 1) = Some (CEXP ac)"
  "prog ! (pc + 2) = Some (INSTR instr.AND)"
  "is_conj_block' prog (pc + 3) pc'" |
  "is_conj_block' prog pc pc'" if
  "pc' < length prog"
  "prog ! pc = Some (INSTR COPY)"
  "prog ! (pc + 1) = Some (INSTR (JMPZ pc'))" (* "prog ! pc_t = Some (INSTR HALT)" *)
  "prog ! (pc + 2) = Some (CEXP ac)"
  "prog ! (pc + 3) = Some (INSTR instr.AND)"
  "is_conj_block' prog (pc + 4) pc'"

inductive_cases stepscE: "stepsc prog n u (pc, st, m, f, rs) (pc', st', m', f', rs')"

function check_conj_block' :: "'t instrc option list \<Rightarrow> addr \<Rightarrow> addr option" where
  "check_conj_block' prog pc = (
    if pc \<ge> length prog then None
    else if prog ! pc = Some (INSTR HALT) then Some pc
    else if
      prog ! pc = Some (INSTR COPY) \<and> (case prog ! (pc + 1) of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False)
      \<and> prog ! (pc + 2) = Some (INSTR instr.AND)
    then check_conj_block' prog (pc + 3)
    else if
      prog ! pc = Some (INSTR COPY) \<and> (case prog ! (pc + 2) of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False)
      \<and> prog ! (pc + 3) = Some (INSTR instr.AND)
      \<and> (case prog ! (pc + 1) of Some (INSTR (JMPZ pc')) \<Rightarrow> True | _ \<Rightarrow> False)
    then
      (case (prog ! (pc + 1), check_conj_block' prog (pc + 4)) of (Some (INSTR (JMPZ pc')), Some pc'')
        \<Rightarrow> if pc' = pc'' then Some pc' else None | _ \<Rightarrow> None)
    else None
    )
  "
  by pat_completeness auto

termination
  by (relation "measure (\<lambda> (prog, pc). length prog - pc)") auto

lemma is_conj_block'_len_prog:
  "pc' < length prog" if "is_conj_block' prog pc pc'"
  using that by induction auto

lemma check_conj_block':
  "check_conj_block' prog pc = Some pc' \<Longrightarrow> is_conj_block' prog pc pc'"
  apply (induction prog pc rule: check_conj_block'.induct)
    apply (erule check_conj_block'.elims)
  by (auto
        split: if_split_asm option.split_asm instrc.split_asm instr.split_asm
        simp del: check_conj_block'.simps
        intro: is_conj_block'.intros is_conj_block'_len_prog)

lemma stepsc_reverseE':
  assumes "stepsc prog (Suc n) u s s''" "s'' \<noteq> s"
  obtains pc' st' m' f' rs' cmd where
    "stepc cmd u (pc', st', m', f', rs') = Some s''"
    "prog pc' = Some cmd"
    "stepsc prog n u s (pc', st', m', f', rs')"
  apply atomize_elim
  using assms
proof (induction prog "Suc n" u s s'' arbitrary: n rule: stepsc.induct) thm stepsc.induct
  case (1 prog n u start)
  then show ?case by simp
next
  case prems: (2 cmd u pc st m f rs s prog n s')
  then show ?case
  proof (cases "s' = s")
    case True
    with prems show ?thesis
      apply simp
      apply solve_ex_triv+
      by (auto elim: stepsc.cases)
  next
    case False
    with prems(3) have "n > 0" by (auto elim!: stepsc.cases)
    then obtain n' where "n = Suc n'" by (cases n) auto
    from prems(4)[OF this False] obtain cmd pc' st' m' f' rs' where
      "stepc cmd u (pc', st', m', f', rs') = Some s'" "prog pc' = Some cmd"
      "stepsc prog n' u s (pc', st', m', f', rs')"
      by atomize_elim
    with prems show ?thesis unfolding \<open>n = _\<close> by blast
  qed
qed

lemma stepsc_reverseE:
  assumes "stepsc prog n u s s''" "s'' \<noteq> s"
  obtains n' pc' st' m' f' rs' cmd where
    "n = Suc n'"
    "stepc cmd u (pc', st', m', f', rs') = Some s''"
    "prog pc' = Some cmd"
    "stepsc prog n' u s (pc', st', m', f', rs')"
proof -
  from assms have "n > 0" by (auto elim!: stepsc.cases)
  then obtain n' where "n = Suc n'" by (cases n) auto
  with assms show ?thesis by (auto elim!: stepsc_reverseE' intro!: that)
qed

lemma
  "pc = pc' - 1" if
  "stepc (CEXP cc) u (pc, st, m, f, rs) = Some (pc', st', m', f', rs')"
  using that by auto

lemma
  "pc = pc' - 1" if
  "stepc (INSTR instr) u (pc, st, m, f, rs) = Some (pc', st', m', f', rs')"
  "\<not> (\<exists> x. instr = JMPZ pc')" "instr \<noteq> RETURN" "instr \<noteq> CALL"
  using that by (auto split: option.split_asm if_split_asm elim!: step.elims)

lemma stepc_pc_no_jump:
  "pc = pc' - 1" if
  "stepc cmd u (pc, st, m, f, rs) = Some (pc', st', m', f', rs')"
  "cmd \<noteq> INSTR (JMPZ pc')" "cmd \<noteq> INSTR RETURN" "cmd \<noteq> INSTR CALL"
  using that by (cases cmd) (auto split: option.split_asm if_split_asm elim!: step.elims)

inductive stepsn :: "'t programc \<Rightarrow> nat \<Rightarrow> (nat, 't :: time) cval \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
  for prog where
  "stepsn prog 0 u start start" | (*
  "stepsc prog (Suc n) u s s'" if
    "stepc cmd u (pc, st, m, f, rs) = Some s'"
    "stepsc prog n u s (pc, st, m, f, rs)"
    "prog pc = Some cmd" *)
  "stepsn prog (Suc n) u (pc, st, m, f, rs) s'" if
    "stepc cmd u (pc, st, m, f, rs) = Some s"
    "prog pc = Some cmd"
    "stepsn prog n u s s'"

declare stepsn.intros[intro]

lemma stepsc_stepsn:
  assumes "stepsc P n u s s'"
  obtains n' where "stepsn P n' u s s'" "n' < n"
  using assms by induction auto

lemma stepsn_stepsc:
  assumes "stepsn P n' u s s'" "n' < n"
  shows "stepsc P n u s s'"
  using assms
  proof (induction arbitrary: n)
    case (1 u start)
    then obtain n' where "n = Suc n'" by (cases n) auto
    then show ?case by auto
  next
    case (2 cmd u pc st m f rs s n s' n')
    from \<open>_ < n'\<close> have "n < n' - 1" by simp
    from 2(4)[OF this] 2(1,2,3,5) show ?case
    proof -
      have "(\<exists>fa n fb p. P = fa \<and> n' = Suc n \<and> u = fb \<and> (pc, st, m, f, rs) = p \<and> s' = p) \<or> (\<exists>i fa n is isa b ns p fb na pa. P = fb \<and> n' = Suc na \<and> u = fa \<and> (pc, st, m, f, rs) = (n, is, isa, b, ns) \<and> s' = pa \<and> stepc i fa (n, is, isa, b, ns) = Some p \<and> fb n = Some i \<and> stepsc fb na fa p pa)"
        using "2.prems" Suc_pred' \<open>P pc = Some cmd\<close> \<open>stepc cmd u (pc, st, m, f, rs) = Some s\<close> \<open>stepsc P (n' - 1) u s s'\<close> gr_implies_not_zero by blast
      then show ?thesis
        by blast
    qed
  qed

lemma stepsn_extend:
  assumes "stepsn P n1 u s s1" "stepsn P n2 u s s2" "n1 \<le> n2"
  shows "stepsn P (n2 - n1) u s1 s2"
using assms
proof (induction arbitrary: n2 s2)
  case (1 u start)
  then show ?case by simp
next
  case (2 cmd u pc st m f rs s n s')
  from 2(1,2,5-) have "stepsn P (n2 - 1) u s s2" by (auto elim: stepsn.cases)
  from 2(4)[OF this] \<open>Suc n <= _\<close> show ?case by simp
qed

(* XXX Move *)
lemma stepsc_halt:
  "s' = (pc, s)" if "stepsc P n u (pc, s) s'" "P pc = Some (INSTR HALT)"
  using that by (induction P n u "(pc, s)" s') auto

lemma stepsn_halt:
  "s' = (pc, s)" if "stepsn P n u (pc, s) s'" "P pc = Some (INSTR HALT)"
  apply (rule stepsc_halt[OF stepsn_stepsc[where n = "Suc n"]])
  using that by simp+

lemma is_conj_block'_pc_mono:
  "pc \<le> pc'" if "is_conj_block' prog pc pc'"
  using that by induction auto

lemma is_conj_block'_halt:
  "prog ! pc' = Some (INSTR HALT)" if "is_conj_block' prog pc pc'"
  using that by induction auto

lemma numeral_4_eq_4:
  "4 = Suc (Suc (Suc (Suc 0)))"
  by simp

lemma is_conj_block'_is_conj:
  assumes "is_conj_block' P pc pc'"
    and "stepsn (\<lambda> i. if i < length P then P ! i else None) n u (pc, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
    and "P ! pc_t = Some (INSTR HALT)"
    (* and "pc < pc_t" (* "pc_t \<le> pc'" *) *)
  shows "f \<and> pc_t = pc'"
  using assms
proof (induction arbitrary: n st s f rs)
  case (1 pc prog)
  with stepsn_halt[OF this(3)] show ?case by simp
next
  case prems: (2 pc' prog pc ac)
  let ?P = "(\<lambda>i. if i < length prog then prog ! i else None)"
  consider (0) "n = 0" | (1) "n = 1" | (2) "n = 2" | (3) "n \<ge> 3" by force
  then show ?case
  proof cases
    case 0
    with prems show ?thesis by (auto elim!: stepsn.cases)
  next
    case 1
    with prems show ?thesis by (auto elim!: stepsn.cases simp: int_of_def split: if_split_asm)
  next
    case 2
    with prems show ?thesis by (auto elim!: stepsn.cases simp: int_of_def numeral_2_eq_2 split: if_split_asm)
  next
    case 3
    from prems have "pc + 2 < length prog" by (auto dest: is_conj_block'_pc_mono)
    with prems(2-4) obtain st1 s1 rs1 where
      "stepsn ?P 3 u (pc, st, s, f, rs) (pc + 3, st1, s1, f \<and> (u \<turnstile>\<^sub>a ac), rs1)"
      by (force simp: int_of_def numeral_3_eq_3)
    from stepsn_extend[OF this prems(7) 3] have
      "stepsn ?P (n - 3) u (pc + 3, st1, s1, f \<and> (u \<turnstile>\<^sub>a ac), rs1) (pc_t, st_t, s_t, True, rs_t)" .
    from prems(6)[OF this \<open>prog ! pc_t = _\<close>] have "pc_t = pc'" "u \<turnstile>\<^sub>a ac" f by auto
    then show ?thesis by simp
  qed
next
  case prems: (3 pc' prog pc ac)
  let ?P = "(\<lambda>i. if i < length prog then prog ! i else None)"
  consider (0) "n = 0" | (1) "n = 1" | (2) "n = 2" | (3) "n = 3" | (4) "n \<ge> 4" by force
  then show ?case
  proof cases
    case 0
    with prems show ?thesis by (auto elim!: stepsn.cases)
  next
    case 1
    with prems show ?thesis by (auto elim!: stepsn.cases simp: int_of_def split: if_split_asm)
  next
    case 2
    with prems show ?thesis by (auto elim!: stepsn.cases simp: int_of_def numeral_2_eq_2 split: if_split_asm)
  next
    case 3
    with prems show ?thesis
      by (auto elim!: stepsn.cases simp: int_of_def numeral_3_eq_3 split: if_split_asm dest!: is_conj_block'_halt)
  next
    case 4
    from prems have "pc + 3 < length prog" by (auto dest: is_conj_block'_pc_mono)
    show ?thesis
    proof (cases f)
      case True
      with \<open>pc + 3 < _\<close> prems(2-6) obtain st1 s1 rs1 where
        "stepsn ?P 4 u (pc, st, s, f, rs) (pc + 4, st1, s1, f \<and> (u \<turnstile>\<^sub>a ac), rs1)"
      by (force simp: int_of_def numeral_3_eq_3 numeral_4_eq_4)
      from stepsn_extend[OF this prems(8) 4] have
        "stepsn ?P (n - 4) u (pc + 4, st1, s1, f \<and> (u \<turnstile>\<^sub>a ac), rs1) (pc_t, st_t, s_t, True, rs_t)" .
      from prems(7)[OF this \<open>prog ! pc_t = _\<close>] have "pc_t = pc'" "u \<turnstile>\<^sub>a ac" f by auto
      then show ?thesis by simp
    next
      case False
      with \<open>pc + 3 < _\<close> prems(1-6) obtain st1 s1 rs1 where
        "stepsn ?P 2 u (pc, st, s, f, rs) (pc', st1, s1, False, rs1)"
        by (force simp: int_of_def numeral_2_eq_2)
      from stepsn_extend[OF this prems(8)] 4 have
        "stepsn ?P (n - 2) u (pc', st1, s1, False, rs1) (pc_t, st_t, s_t, True, rs_t)" by simp
      from stepsn_halt[OF this] prems(1,6) show ?thesis by (auto dest: is_conj_block'_halt)
    qed
  qed
qed

lemma is_conj_block'_is_conj':
  assumes "is_conj_block' P pc pc'"
    and "stepst (\<lambda> i. if i < length P then P ! i else None) n u (pc, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
    (* and "pc < pc_t" (* "pc_t \<le> pc'" *) *)
  shows "f \<and> pc_t = pc'"
  using assms
  unfolding stepst_def by (auto split: if_split_asm elim!: is_conj_block'_is_conj stepsc_stepsn)

lemma is_conj_block'_is_conj2:
  assumes "is_conj_block' P (pc + 1) pc'" "P ! pc = Some (CEXP ac)"
    and "stepst (\<lambda> i. if i < length P then P ! i else None) n u (pc, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
  shows "(u \<turnstile>\<^sub>a ac) \<and> pc_t = pc'"
proof -
  let ?P = "(\<lambda> i. if i < length P then P ! i else None)"
  from assms(1) have "pc < pc'" "pc' < length P"
    by (auto dest: is_conj_block'_pc_mono is_conj_block'_len_prog)
  with assms(2,3) obtain st' s' rs' where
    "stepst ?P (n - 1) u (pc + 1, st', s', u \<turnstile>\<^sub>a ac, rs') (pc_t, st_t, s_t, True, rs_t)"
    unfolding stepst_def
    apply (clarsimp split: if_split_asm)
    apply (erule stepsc.cases)
    by auto
  from is_conj_block'_is_conj'[OF assms(1) this] show ?thesis .
qed

lemma is_conj_block'_is_conj3:
  assumes "is_conj_block' P (pc + 2) pc'" "P ! pc = Some (CEXP ac)" "P ! (pc + 1) = Some (INSTR instr.AND)"
    and "stepst (\<lambda> i. if i < length P then P ! i else None) n u (pc, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
  shows "(u \<turnstile>\<^sub>a ac) \<and> pc_t = pc'"
proof -
  let ?P = "(\<lambda> i. if i < length P then P ! i else None)"
  from assms(1) have "pc < pc'" "pc' < length P"
    by (auto dest: is_conj_block'_pc_mono is_conj_block'_len_prog)
  with assms(2,3,4) obtain st' s' rs' f where
    "stepst ?P (n - 2) u (pc + 2, st', s', f \<and> (u \<turnstile>\<^sub>a ac), rs') (pc_t, st_t, s_t, True, rs_t)"
    unfolding stepst_def
    apply (clarsimp split: if_split_asm)
    apply (erule stepsc.cases)
     apply force
    apply (erule stepsc.cases)
    by (auto split: if_split_asm option.split_asm elim!: UPPAAL_Asm.step.elims)
  from is_conj_block'_is_conj'[OF assms(1) this] show ?thesis by simp
qed

definition
  "is_conj_block P pc pc' \<equiv>
   (\<exists> ac. P ! pc = Some (CEXP ac)) \<and> is_conj_block' P (pc + 1) pc'
   \<or> (\<exists> ac.
      P ! pc = Some (CEXP ac)) \<and> P ! (pc + 1) = Some (INSTR instr.AND)
      \<and> is_conj_block' P (pc + 2) pc'"

lemma is_conj_block_alt_def[code]:
"is_conj_block P pc pc' \<equiv>
   (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False) \<and> is_conj_block' P (pc + 1) pc'
   \<or> (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False) \<and> P ! (pc + 1) = Some (INSTR instr.AND)
      \<and> is_conj_block' P (pc + 2) pc'"
  unfolding is_conj_block_def
  by (rule eq_reflection) (auto split: option.split_asm instrc.split_asm)

lemma is_conj_block_is_conj:
  assumes "is_conj_block P pc pc'" "P ! pc = Some (CEXP ac)"
    and
      "stepst
        (\<lambda> i. if i < length P then P ! i else None) n u
        (pc, st, s, f, rs)
        (pc_t, st_t, s_t, True, rs_t)"
  shows "(u \<turnstile>\<^sub>a ac) \<and> pc_t = pc'"
  using assms
  unfolding is_conj_block_def
  apply safe
  by ((drule is_conj_block'_is_conj2 is_conj_block'_is_conj3; simp), simp)+

lemma is_conj_block'_decomp:
  "is_conj_block P pc' pc''" if
  "is_conj_block' P pc pc''" "P ! pc' = Some (CEXP ac)" "pc \<le> pc'" "pc' \<le> pc''"
  using that
proof (induction arbitrary: pc')
  case (1 pc prog)
  then show ?case by (simp add: is_conj_block_def)
next
  case prems: (2 pc'' prog pc ac)
  with \<open>pc \<le> _\<close> consider "pc' = pc" | "pc' = Suc pc" | "pc' = Suc (Suc pc)" | "pc + 3 \<le> pc'"
    by force
  then show ?case using prems by cases (auto simp add: numeral_3_eq_3 is_conj_block_def)
next
  case prems: (3 pc'' prog pc ac)
  with \<open>pc \<le> _\<close> consider
    "pc' = pc" | "pc' = Suc pc" | "pc' = Suc (Suc pc)" | "pc' = Suc (Suc (Suc pc))" | "pc + 4 \<le> pc'"
    by force
  then show ?case using prems by cases (auto simp add: numeral_3_eq_3 numeral_4_eq_4 is_conj_block_def)+
qed

lemma is_conj_block_decomp:
  "is_conj_block P pc' pc''" if
  "is_conj_block P pc pc''" "P ! pc' = Some (CEXP ac)" "pc \<le> pc'" "pc' \<le> pc''"
  using that
  apply (subst (asm) is_conj_block_def)
  apply safe
  (* XXX Should work without metis *)
  apply (metis
    One_nat_def add_Suc_right diff_diff_cancel diff_is_0_eq diff_le_self gr_zeroI
    is_conj_block'_decomp le_simps(3) mpl_lem pl_pl_mm that(1))
  by (metis
    One_nat_def Suc_1 add.right_neutral add_Suc_right instrc.simps(4) is_conj_block'_decomp
    le_antisym not_less_eq_eq option.inject that(1))

abbreviation "conv_P \<equiv> map (map_option (map_instrc real_of_int))"

lemma stepst_stepc_extend:
  "stepst P n u (pc', s') (pc'', s'')"
  if "stepst P n u (pc, s) (pc'', s'')" "stepsc P n u (pc, s) (pc', s')"
proof -
  from that have "P pc'' = Some (INSTR HALT)" unfolding stepst_def by auto
  from that obtain n1 n2 where *:
    "stepsn P n1 u (pc, s) (pc'', s'')" "stepsn P n2 u (pc, s) (pc', s')" "n1 < n" "n2 < n"
    unfolding stepst_def by (auto elim!: stepsc_stepsn)
  show ?thesis
  proof (cases "n1 \<ge> n2")
    case True
    from stepsn_extend[OF *(2,1) this] \<open>n1 < _\<close> \<open>n2 < _\<close> \<open>P pc'' = _\<close> show ?thesis
      unfolding stepst_def by (auto intro: stepsn_stepsc)
  next
    case False
    with stepsn_extend[OF *(1,2)] \<open>n1 < _\<close> \<open>n2 < _\<close> \<open>P pc'' = _\<close> show ?thesis
      unfolding stepst_def by (auto intro: stepsn_stepsc dest!: stepsn_halt)
  qed
qed

lemma conv_P_conj_block'[intro]:
  "is_conj_block' (conv_P P) pc pc'" if "is_conj_block' P pc pc'"
  using that
  apply induction
    apply (rule is_conj_block'.intros(1))
     apply (simp; fail)
    apply (simp; fail)
   apply (rule is_conj_block'.intros(2))
       apply (simp; fail)
      apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
     apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
    apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
   apply (simp; fail)
  apply (rule is_conj_block'.intros(3))
       apply (simp; fail)
      apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
     apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
    apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
   apply (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog)
  apply (simp; fail)
  done

lemma conv_P_conj_block[intro]:
  "is_conj_block (conv_P P) pc pc'" if "is_conj_block P pc pc'"
  using that[unfolded is_conj_block_def]
  apply safe
  by (frule is_conj_block'_pc_mono; force dest: is_conj_block'_len_prog simp: is_conj_block_def)+

context
  fixes P :: "int instrc option list"
    and pc_s :: addr
    and n :: nat
begin

private abbreviation "prog i \<equiv> if i < length P then P ! i else None"

lemma stepst_conv_P:
  "stepst (\<lambda> i. if i < length (conv_P P) then conv_P P ! i else None) n u s s'" if
  "stepst (conv_prog prog) n u s s'" using that unfolding stepst_def
  apply safe
  subgoal for pc a aa ab b z
    apply rotate_tac
    by (induction "conv_prog prog" n u s "(pc, a, aa, ab, b)" rule: stepsc.induct)
      (auto split: if_split_asm)
  by (auto split: if_split_asm)


lemma is_conj:
  fixes u :: "nat \<Rightarrow> real"
  defines "S \<equiv> steps_approx_absint n P pc_s"
  defines "pc_c \<equiv> Min {pc. \<exists> ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)}"
  assumes "is_conj_block P pc_c (Max S)"
    and "stepst (conv_prog prog) n u (pc_s, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
    and "stepsc (conv_prog prog) n u (pc_s, st, s, f, rs) (pc', st', s', f', rs')"
    and "P ! pc' = Some (CEXP ac)" "pc' < length P"
    and S_fin: "finite S"
  shows "(u \<turnstile>\<^sub>a conv_ac ac) \<and> pc_t = Max S"
proof -
  from stepst_stepc_extend[OF assms(4,5)] have *:
    "stepst (conv_prog prog) n u (pc', st', s', f', rs') (pc_t, st_t, s_t, True, rs_t)" .

  from \<open>stepsc _ _ _ _ _\<close> have in_S: "pc' \<in> S" unfolding S_def by (rule stepsc_steps_approx)
  from in_S have max: "pc' \<le> Max S" unfolding S_def using Max_ge S_fin S_def by blast

  let ?pulled = "{pc. pc \<in> S \<and> (\<exists> ac. P ! pc = Some (CEXP ac))}"
  have fin: "finite ?pulled" using S_def S_fin by fastforce
  have pull: "?pulled = {pc. \<exists>ac. P ! pc = Some (CEXP ac)} \<inter> S"
  proof -
    have "{pc. \<exists>ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)} = ?pulled" by simp
    thus ?thesis by blast
  qed
  hence pc_c_min: "pc_c = Min ({pc. \<exists>ac. P ! pc = Some (CEXP ac)} \<inter> S)" unfolding S_def pc_c_def using S_def by auto
  hence min: "pc_c \<le> pc'" using max.bounded_iff fin using pull assms(6) in_S by auto

  from is_conj_block_decomp[OF assms(3) \<open>P ! pc' = _\<close> min max] have
    "is_conj_block P pc' (Max S)" .
  then have "is_conj_block (conv_P P) pc' (Max S)" by auto
  from is_conj_block_is_conj[OF this _ stepst_conv_P[OF *]] \<open>P ! pc' = _\<close> \<open>pc' < _\<close>
    show ?thesis
    by auto
qed

lemma is_conj':
  fixes u :: "nat \<Rightarrow> real"
  defines "S \<equiv> steps_approx_absint n P pc_s"
  assumes "{pc. \<exists> ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)} = {}"
    and "stepsc (conv_prog prog) n u (pc_s, st, s, f, rs) (pc', st', s', f', rs')"
    and "P ! pc' = Some (CEXP ac)"
  shows False
  using stepsc_steps_approx[OF assms(3)] assms(4) assms(2) unfolding S_def by auto

term is_conj_block

definition
"check_conj_block pc pc' \<equiv>
   (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False) \<and> check_conj_block' P (pc + 1) = Some pc'
   \<or> (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False) \<and> P ! (pc + 1) = Some (INSTR instr.AND)
      \<and> check_conj_block' P (pc + 2) = Some pc'"

lemma check_conj_block:
  "check_conj_block pc pc' \<Longrightarrow> is_conj_block P pc pc'"
  unfolding is_conj_block_alt_def check_conj_block_def
  by (auto dest!: check_conj_block' simp del: check_conj_block'.simps)

definition
  "conjunction_check \<equiv>
    let S = steps_approx_absint n P pc_s; S' = {pc. \<exists> ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)} in
      S \<noteq> \<top> \<and> (S' = {} \<or> check_conj_block (Min S') (Max S))
  "

lemma conjunction_check_alt_def[code]:
  "conjunction_check =
    (
     let
        S = steps_approx_absint n P pc_s;
        S' = {pc. pc \<in> S \<and> (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False)}
      in
        S \<noteq> \<top> \<and> (S' = {} \<or> check_conj_block (Min S') (Max S))
    )
  "
proof -
  let ?S = "steps_approx_absint n P pc_s"
  have "
    {pc. pc \<in> ?S \<and> (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False)}
  = {pc. \<exists> ac. pc \<in> ?S \<and> P ! pc = Some (CEXP ac)}
  " by safe (auto split: option.splits instrc.splits)
  show ?thesis unfolding conjunction_check_def Let_def \<open>_ = _\<close> by simp
qed

lemma conjunction_check:
  fixes u :: "nat \<Rightarrow> real"
  assumes "conjunction_check"
    and "stepst (conv_prog prog) n u (pc_s, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
    and "stepsc (conv_prog prog) n u (pc_s, st, s, f, rs) (pc', st', s', f', rs')"
    and "P ! pc' = Some (CEXP ac)" "pc' < length P"
  shows "u \<turnstile>\<^sub>a conv_ac ac"
  using assms
  unfolding conjunction_check_def Let_def
  by (metis (no_types, lifting) check_conj_block is_conj is_conj' steps_approx_absint_finite)

end (* End of context for fixed program *)

end (* Theory *)