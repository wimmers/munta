theory AbsInt_Instrc
  imports AbsInt UPPAAL_Asm_Clocks UPPAAL_Asm_Assemble
begin

definition extract_prog :: "'t programc \<Rightarrow> program" where
  "extract_prog p = (\<lambda>cop. case cop of Some (INSTR op) \<Rightarrow> Some op | Some (CEXP _) \<Rightarrow> Some NOP | None \<Rightarrow> None) \<circ> p"

fun astep_liftc :: "'a::absstate astep \<Rightarrow> 't programc \<Rightarrow> instr \<Rightarrow> addr \<Rightarrow> 'a \<Rightarrow> 'a state_map" where
  "astep_liftc f prog op pc s =
    (case prog pc of
      (Some (CEXP _)) \<Rightarrow> (if s = \<bottom> then \<bottom> else undefined) |
      _ \<Rightarrow> f op pc s)"

lemma astep_liftc_keep_bot:
  assumes "lookup (f op ipc \<bottom>) pc = \<bottom>"
  shows "lookup (astep_liftc f prog op ipc \<bottom>) pc = \<bottom>"
using assms proof (cases "prog ipc")
  case (Some cop)
  then show ?thesis using assms by (cases cop; simp)
qed simp

context Abs_Int
begin

lemma astep_liftc_keep_bot_map:
  "astep_liftc ai_step prog op ipc \<bottom> = \<bottom>"
proof (rule state_map_eq_fwd, goal_cases)
  case (1 p)
  have "lookup (astep_liftc ai_step prog op ipc \<bottom>) p = \<bottom>"
    using astep_keep_bot by (rule astep_liftc_keep_bot)
  also have "\<dots> = lookup \<bottom> p" by simp
  finally show ?case .
qed

definition "ai_loopc cprog \<equiv> finite_loop (astep_liftc ai_step cprog) (extract_prog cprog)"

theorem ai_stepsc:
  assumes "stepsc cprog (Suc n) u (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> \<gamma> (lookup entry pc)"
  shows "(st', s', f', rs') \<in> \<gamma> (lookup (ai_loopc cprog n entry) pc')"
using assms proof (induction n arbitrary: pc st s f rs entry)
  case 0
  moreover from \<open>stepsc _ (Suc 0) _ _ _ \<close> have "pc' = pc \<and> st' = st \<and> s' = s \<and> f' = f \<and> rs' = rs"
    using stepsc.cases by (cases; blast)
  ultimately show ?case unfolding ai_loopc_def by simp
next
  case (Suc n)
  from \<open>stepsc cprog (Suc (Suc n)) _ _ _\<close> show ?case
  proof (cases)
    case 1
    have "entry \<le> ai_loopc cprog (Suc n) entry"
      unfolding ai_loopc_def by (rule finite_loop_preserve)
    then show ?thesis using 1 Suc.prems \<gamma>_lookup_le \<gamma>_lookup \<gamma>_map_mono by blast
  next
    case (2 cmd inter)
    then obtain pc'' st'' s'' f'' rs'' where inter: "inter = (pc'', st'', s'', f'', rs'')"
      using state_pc.cases by blast
    let ?anter = "ai_loopc cprog 1 entry"
    have "(st'', s'', f'', rs'') \<in> \<gamma> (lookup (finite_step_map (astep_liftc ai_step cprog) (extract_prog cprog) entry) pc'')"
    proof (cases cmd)
      case (INSTR instr)
      hence same: "astep_liftc ai_step cprog instr pc (lookup entry pc) = ai_step instr pc (lookup entry pc)" using 2 by simp
      have "(st'', s'', f'', rs'') \<in> \<gamma> (lookup (ai_step instr pc (lookup entry pc)) pc'')"
      proof -
        from \<open>stepc _ _ _ = _\<close> have "UPPAAL_Asm.step instr (pc, st, s, f, rs) = Some (pc'', st'', s'', f'', rs'')"
          unfolding INSTR stepc.simps inter by (cases "UPPAAL_Asm.step instr (pc, st, s, f, rs)"; simp)
        hence "(st'', s'', f'', rs'') \<in> lookup (collect_step instr pc (\<gamma> (lookup entry pc))) pc''"
          using Suc.prems(2) by auto
        thus ?thesis using astep_correct by blast
      qed
      hence "(st'', s'', f'', rs'') \<in> \<gamma> (lookup ((astep_liftc ai_step cprog) instr pc (lookup entry pc)) pc'')" using same by simp
      moreover have "astep_liftc ai_step cprog instr pc (lookup entry pc) \<le> finite_step_map (astep_liftc ai_step cprog) (extract_prog cprog) entry"
      proof -
        have "(extract_prog cprog) pc = Some instr" unfolding extract_prog_def using 2 INSTR by simp
        then show ?thesis using calculation astep_liftc_keep_bot_map finite_step_map_step by blast
      qed
      ultimately show ?thesis using less_eq_state_map_def mono_gamma by blast
    next
      case (CEXP x2)
      then show ?thesis sorry
    qed
    hence "(st'', s'', f'', rs'') \<in> \<gamma> (lookup (finite_advance (astep_liftc ai_step cprog) (extract_prog cprog) entry) pc'')"
      by (metis (no_types, lifting) finite_advance.elims le_sup_iff less_eq_state_map_def mono_gamma order_refl subsetD)
    hence "(st'', s'', f'', rs'') \<in> \<gamma> (lookup ?anter pc'')" by (simp add: ai_loopc_def)
    then show ?thesis using Suc.IH by (metis (no_types, lifting) "2"(3) One_nat_def inter ai_loopc_def finite_loop.simps(1) finite_loop.simps(2))
  qed
qed

theorem ai_stepsc_single:
  assumes
    "stepsc cprog (Suc n) u (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> \<gamma> entry"
  shows "(st', s', f', rs') \<in> \<gamma> (lookup (ai_loopc cprog n (single pc entry)) pc')"
  using assms ai_stepsc by fastforce

lemma ai_stepsc_pc:
  assumes
    "stepsc cprog (Suc n) u (pc, st, s, f, rs) (pc', st', s', f', rs')"
    "(st, s, f, rs) \<in> \<gamma> (lookup entry pc)"
  shows "pc' \<in> domain (ai_loopc cprog n entry)"
proof -
  from assms have "(st', s', f', rs') \<in> \<gamma> (lookup (ai_loopc cprog n entry) pc')" by (rule ai_stepsc)
  hence "lookup (ai_loopc cprog n entry) pc' \<noteq> \<bottom>" by auto
  thus ?thesis by (smt domain.elims lookup.simps mem_Collect_eq)
qed

end

end