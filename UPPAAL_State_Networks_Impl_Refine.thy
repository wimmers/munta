theory UPPAAL_State_Networks_Impl_Refine
  imports
    UPPAAL_State_Networks_Impl Normalized_Zone_Semantics_Impl_Refine TA_Impl_Misc
    "~/Isabelle/Util/ML_Util"
begin

(* XXX Rename this way *)
lemmas mem_nth = aux

subsection \<open>Method setup for quantifier trickery\<close>

ML \<open>fun mini_ex ctxt = SIMPLE_METHOD (mini_ex_tac ctxt 1)\<close>
ML \<open>fun defer_ex ctxt = SIMPLE_METHOD (defer_ex_tac ctxt 1)\<close>

method_setup mini_existential =
  \<open>Scan.succeed mini_ex\<close> \<open>Miniscope existential quantifiers\<close>
method_setup defer_existential =
  \<open>Scan.succeed defer_ex\<close> \<open>Rotate first conjunct under existential quantifiers to last position\<close>

method mini_ex = ((simp only: ex_simps[symmetric])?, mini_existential, (simp)?)
method defer_ex = ((simp only: ex_simps[symmetric])?, defer_existential, (simp)?)
method defer_ex' = (defer_existential, (simp)?)

method solve_triv =
  fo_assumption | refl_match | simp; fail | assumption | (erule image_eqI[rotated], solve_triv)

method solve_ex_triv2 = (((rule exI)+)?, (rule conjI)+, solve_triv)

method solve_conj_triv = solve_triv | (rule conjI, solve_conj_triv)

method solve_conj_triv2 =
  (match conclusion in
    "_ \<and> _" \<Rightarrow> \<open>rule conjI, solve_conj_triv2\<close>
  \<bar> _ \<Rightarrow> solve_triv)

method solve_ex_triv = (((rule exI)+)?, solve_conj_triv)

subsection \<open>Executable successor computation\<close>

no_notation Ref.update ("_ := _" 62)
no_notation test_bit (infixl "!!" 100)

locale UPPAAL_Reachability_Problem_precompiled_defs' =
  UPPAAL_Reachability_Problem_precompiled_defs +
  fixes na :: nat
begin

text \<open>Definition of implementation auxiliaries (later connected to the automaton via proof)\<close>

  (*
  definition
    "trans_i_map \<equiv>
      map (map (map (\<lambda> (g, a, r, l').
        case a of Sil a \<Rightarrow> (g, a, r, l')) o filter (\<lambda> (g, a, r, l').
        case a of Sil a \<Rightarrow> True | _ \<Rightarrow> False))) trans"
  *)

  definition
    "trans_i_map =
      map (map (List.map_filter
        (\<lambda> (g, a, m, l'). case a of Sil a \<Rightarrow> Some (g, a, m, l') | _ \<Rightarrow> None)
      )) trans"

  definition
    "trans_in_map \<equiv>
      map (map (map
        (\<lambda> (g, a, m, l'). case a of In a \<Rightarrow> (g, a, m, l')) o filter (\<lambda> (g, a, m, l').
          case a of In a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  definition
    "trans_out_map \<equiv>
      map (map (map
        (\<lambda> (g, a, m, l'). case a of Out a \<Rightarrow> (g, a, m, l')) o filter (\<lambda> (g, a, m, l').
          case a of Out a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  abbreviation
    "nested_list_to_iarray xs \<equiv> IArray (map IArray xs)"

  (* XXX Optimize by using a better data structure? *)
  definition
    "actions_by_state i \<equiv> fold (\<lambda> t acc. acc[fst (snd t) := (i, t) # (acc ! fst (snd t))])"

  definition
    "all_actions_by_state t L \<equiv>
      fold (\<lambda> i. actions_by_state i (t !! i !! (L ! i))) [0..<p] (repeat [] na)"

  abbreviation "PF \<equiv> stripfp PROG"
  abbreviation "PT \<equiv> striptp PROG"
  definition "runf pc s \<equiv> exec PF max_steps (pc, [], s, True, []) []"
  definition "runt pc s \<equiv> exec PT max_steps (pc, [], s, True, []) []"

  definition
    "check_pred L s \<equiv>
      list_all
        (\<lambda> q.
          case runf (pred ! q ! (L ! q)) s of
            Some ((_, _, _, f, _), _) \<Rightarrow> f \<and> bounded bounds s
          | None \<Rightarrow> False
        )
        [0..<p]
      "

  definition
    "make_cconstr pcs = List.map_filter
      (\<lambda> pc.
        case PROG pc of
          Some (CEXP ac) \<Rightarrow> Some ac
        | _ \<Rightarrow> None
      )
      pcs"

  definition
    "check_g pc s \<equiv>
      case runt pc s of
        Some ((_, _, _, True, _), pcs) \<Rightarrow> Some (make_cconstr pcs)
      | _ \<Rightarrow> None
      "

   definition
    "trans_i_from \<equiv> \<lambda> (L, s) i.
      List.map_filter (\<lambda> (g, a, m, l').
        case check_g g s of
          Some cc \<Rightarrow>
          case runf m s of
            Some ((_, _, s', _, r), _) \<Rightarrow>
              if check_pred (L[i := l']) s'
              then Some (cc, a, r, (L[i := l'], s'))
              else None
         | _ \<Rightarrow> None
      | _ \<Rightarrow> None)
        ((IArray (map IArray trans_i_map)) !! i !! (L ! i))"

  definition
    "trans_i_fun L \<equiv> concat (map (trans_i_from L) [0..<p])"

  definition
    "make_reset m1 s \<equiv>
      case runf m1 s of
        Some ((_, _, _, _, r1), _) \<Rightarrow> r1
      | None \<Rightarrow> []
    "

  definition
    "pairs_by_action \<equiv> \<lambda> (L, s) OUT. concat o
      map (\<lambda> (i, g1, a, m1, l1). List.map_filter
      (\<lambda> (j, g2, a, m2, l2).
        if i = j then None else
        case (check_g g1 s, check_g g2 s) of
          (Some cc1, Some cc2) \<Rightarrow>
          case runf m2 s of
            Some ((_, _, s1, _, r2), _) \<Rightarrow>
            case runf m1 s1 of
              Some (( _, _, s', _, _), _) \<Rightarrow>
                if check_pred (L[i := l1, j := l2]) s'
                then Some (cc1 @ cc2, a, make_reset m1 s @ r2, (L[i := l1, j := l2], s'))
                else None
            | _ \<Rightarrow> None
          | _ \<Rightarrow> None
        | _ \<Rightarrow> None
      )
      OUT)
        "

  definition
    "trans_s_fun \<equiv> \<lambda> (L, s).
      let
        In = all_actions_by_state (nested_list_to_iarray trans_in_map) L;
        Out = all_actions_by_state (nested_list_to_iarray trans_out_map) L
      in
        concat (map (\<lambda> a. pairs_by_action (L, s) (Out ! a) (In ! a)) [0..<na])
    "

  definition
    "trans_fun L \<equiv> trans_s_fun L @ trans_i_fun L"

  lemma trans_i_fun_trans_fun:
    assumes "(g, a, r, L') \<in> set (trans_i_fun L)"
    shows "(g, a, r, L') \<in> set (trans_fun L)"
    using assms unfolding trans_fun_def by auto

  lemma trans_s_fun_trans_fun:
    assumes "(g, a, r, L') \<in> set (trans_s_fun L)"
    shows "(g, a, r, L') \<in> set (trans_fun L)"
    using assms unfolding trans_fun_def by auto

end (* End of locale for implementation definitions *)

context Prod_TA_Defs
begin

  (* XXX Can overwrite this theorem from other context in SAME locale *)
  lemma prod_trans_i_alt_def:
    "prod_trans_i =
      {((L, s), g, a, r, (L', s')) | L s g c a r m L' s'.
       (L, g, (a, Act (c, m)), r, L') \<in> Product_TA_Defs.product_trans_i (N_s s) \<and>
       (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) s')
       \<and> c s \<and> Some s' = m s}"
    unfolding
      prod_trans_i_def trans_of_def Product_TA_Defs.product_ta_def
      Product_TA_Defs.product_trans_def
      Product_TA_Defs.product_trans_i_def Product_TA_Defs.product_trans_s_def
    by (safe; simp; metis)

  lemma prod_trans_s_alt_def:
    "prod_trans_s =
      {((L, s), g, a, r, (L', s')) | L s g ci co a r mi mo L' s1 s'.
        ci s \<and> co s
        \<and> (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) s')
        \<and> (L, g, (a, Syn (ci, mi) (co, mo)), r, L') \<in> Product_TA_Defs.product_trans_s (N_s s)
        \<and> Some s' = mi s1 \<and> Some s1 = mo s
      }"
    unfolding
      prod_trans_s_def trans_of_def Product_TA_Defs.product_ta_def
      Product_TA_Defs.product_trans_def
      Product_TA_Defs.product_trans_i_def
      Product_TA_Defs.product_trans_s_def
    by (safe; simp; metis)

end

context UPPAAL_Reachability_Problem_precompiled_defs
begin

  lemma T_s_unfold_1:
    "fst ` equiv.defs.T_s q s = fst ` fst (equiv.N ! q)" if "q < p"
    using \<open>q < p\<close>
    unfolding equiv.defs.T_s_def
    unfolding equiv.state_ta_def
    unfolding equiv.state_trans_t_def
    by force

  lemma T_s_unfold_2:
    "(snd o snd o snd o snd) ` equiv.defs.T_s q s = (snd o snd o snd o snd) ` fst (equiv.N ! q)"
    if "q < p"
    using \<open>q < p\<close>
    unfolding equiv.defs.T_s_def
    unfolding equiv.state_ta_def
    unfolding equiv.state_trans_t_def
    by force

end

context Equiv_TA_Defs
begin

  lemma p_p:
    "defs.p = p"
    by simp

end

context
  Prod_TA_Defs
begin

  lemma states'_alt_def:
    "states' s =
    {L. length L = p \<and>
        (\<forall> q < p. (L ! q) \<in> fst ` (fst (fst A ! q)) \<union> (snd o snd o snd o snd) ` (fst (fst A ! q)))}"
    unfolding trans_of_def Product_TA_Defs.product_ta_def N_s_def
    unfolding Product_TA_Defs.product_trans_def
    unfolding Product_TA_Defs.product_trans_i_def Product_TA_Defs.product_trans_s_def
    apply simp
    apply safe
    unfolding T_s_def
      apply (fastforce simp: Product_TA_Defs.states_def trans_of_def p_def)
     apply (force simp: Product_TA_Defs.states_def trans_of_def p_def)
    by (fastforce simp: Product_TA_Defs.states_def trans_of_def p_def image_iff)

end

(*
fun step_approx :: "instr \<Rightarrow> addr set" where
  "step_approx (JMPZ q) (pc, _) = {pc + 1, q}" |
  "step_approx CALL (pc, q # st, _) = {nat q}
    (if q \<ge> 0 then Some (nat q, int pc # st, m, f, rs) else None)" |
  "step RETURN (pc, q # st, m, f, rs) =
    (if q \<ge> 0 then Some (nat q + 1, st, m, f, rs) else None)" |
  (*
  "step HALT s = Some s" |
  *)
  "step (STOREC c d) (pc, st, m, f, rs) =
    (if d = 0 then Some (pc + 1, st, m, f, c # rs) else None)" |
  "step (SETF b) (pc, st, m, f, rs) = Some (pc + 1, st, m, b, rs)" |
  "step _ _ = None"
*)

fun steps_approx :: "nat \<Rightarrow> 't instrc option list \<Rightarrow> addr \<Rightarrow> addr set" where
  "steps_approx 0 prog pc = (if pc < length prog then {pc} else {})" |
  "steps_approx (Suc n) prog pc =
    (
      if pc \<ge> length prog
      then {}
      else
        case prog ! pc of
          None \<Rightarrow> {pc}
        | Some cmd \<Rightarrow>
          let succs =
            (
              case cmd of
                CEXP ac \<Rightarrow> {pc + 1}
              | INSTR instr \<Rightarrow>
                  case instr of
                    CALL   \<Rightarrow> {..<length prog}
                  | RETURN \<Rightarrow> {..<length prog}
                  | JMPZ pc' \<Rightarrow> {pc + 1, pc'}
                  | HALT \<Rightarrow> {}
                  |    _ \<Rightarrow> {pc + 1}
            )
          in {pc} \<union> \<Union> (steps_approx n prog ` succs)
    )
  "

lemma bounded_less_simp[simp]:
  "\<forall>q\<in>{..<p::nat}. P q \<equiv> \<forall> q < p. P q"
  by (rule eq_reflection) auto

context
  fixes prog :: "int instrc option list"
begin

private abbreviation "P i \<equiv> if i < length prog then prog ! i else None"

lemma steps_out_of_range:
  assumes "stepsc (conv_prog P) n u (pc, st, s, f, rs) (pc', st', s', f', rs')" "pc \<ge> length prog"
  shows "pc' = pc"
  using assms by cases auto

lemma stepsc_steps_approx:
  assumes "stepsc (conv_prog P) n u (pc, st, s, f, rs) (pc', st', s', f', rs')" "pc' < length prog"
  shows "pc' \<in> steps_approx n prog pc"
  using assms
  apply (induction "conv_prog P" n u "(pc, st, s, f, rs)" "(pc', st', s', f', rs')" arbitrary: pc st s f rs rule: stepsc.induct)
   apply (simp split: option.split)
  apply clarsimp
  apply rule
   apply (simp split: if_split_asm; fail)
  apply (clarsimp split: option.split)
  apply rule
   apply (simp split: if_split_asm; fail)
  apply (case_tac z)
   apply (simp split: option.split_asm if_split_asm)
   apply (case_tac x1)
                  apply (simp split: if_split_asm)
                 apply (auto elim: UPPAAL_Asm.step.elims)[]
                apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
               apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
              apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
             apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
            apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
           apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
          apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
         apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
        apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
       apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
      apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
       apply (case_tac "q < length prog")
        apply force
       apply (drule steps_out_of_range; simp)
      apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
      apply (case_tac "q + 1 < length prog")
       apply force
      apply (drule steps_out_of_range; simp)
     apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
    apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
   apply (auto elim!: UPPAAL_Asm.step.elims split: if_split_asm)[]
  by (force split: if_split_asm)

definition
  "time_indep_check pc n \<equiv>
    \<forall> pc' \<in> steps_approx n prog pc. pc' < length prog
    \<longrightarrow> (case prog ! pc' of Some cmd \<Rightarrow> is_instr cmd | _ \<Rightarrow> True)"

lemma time_indep_overapprox:
  assumes
    "time_indep_check pc n"
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
        by (cases cmd') (auto simp: time_indep_check_def)
    next
      case False
      with A(2) show ?thesis by (auto split: option.split_asm)
    qed
  }
  then show ?thesis unfolding time_indep_def by blast
qed

end

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

lemma steps_approx_finite[intro,simp]:
  "finite (steps_approx n P pc_s)"
  by (induction rule: steps_approx.induct; clarsimp split: option.split instrc.split instr.split)

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
  defines "S \<equiv> steps_approx n P pc_s"
  defines "pc_c \<equiv> Min {pc. \<exists> ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)}"
  assumes "is_conj_block P pc_c (Max S)"
    and "stepst (conv_prog prog) n u (pc_s, st, s, f, rs) (pc_t, st_t, s_t, True, rs_t)"
    and "stepsc (conv_prog prog) n u (pc_s, st, s, f, rs) (pc', st', s', f', rs')"
    and "P ! pc' = Some (CEXP ac)" "pc' < length P"
  shows "(u \<turnstile>\<^sub>a conv_ac ac) \<and> pc_t = Max S"
proof -
  from stepst_stepc_extend[OF assms(4,5)] have *:
    "stepst (conv_prog prog) n u (pc', st', s', f', rs') (pc_t, st_t, s_t, True, rs_t)" .
  from \<open>stepsc _ _ _ _ _\<close> \<open>P ! pc' = _\<close> \<open>pc' < _\<close> have "pc_c \<le> pc'" "pc' \<le> Max S"
    unfolding pc_c_def S_def by (auto intro: stepsc_steps_approx Min_le Max_ge)
  from is_conj_block_decomp[OF assms(3) \<open>P ! pc' = _\<close> this] have
    "is_conj_block P pc' (Max S)" .
  then have "is_conj_block (conv_P P) pc' (Max S)" by auto
  from is_conj_block_is_conj[OF this _ stepst_conv_P[OF *]] \<open>P ! pc' = _\<close> \<open>pc' < _\<close>
    show ?thesis
    by auto
qed

lemma is_conj':
  fixes u :: "nat \<Rightarrow> real"
  defines "S \<equiv> steps_approx n P pc_s"
  assumes "{pc. \<exists> ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)} = {}"
    and "stepsc (conv_prog prog) n u (pc_s, st, s, f, rs) (pc', st', s', f', rs')"
    and "P ! pc' = Some (CEXP ac)" "pc' < length P"
  shows False
  using stepsc_steps_approx[OF assms(3,5)] assms(4) assms(2) unfolding S_def by auto

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
    let S = steps_approx n P pc_s; S' = {pc. \<exists> ac. pc \<in> S \<and> P ! pc = Some (CEXP ac)} in
      S' = {} \<or> check_conj_block (Min S') (Max S)
  "

lemma conjunction_check_alt_def[code]:
  "conjunction_check =
    (
     let
        S = steps_approx n P pc_s;
        S' = {pc. pc \<in> S \<and> (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False)}
      in
        S' = {} \<or> check_conj_block (Min S') (Max S)
    )
  "
proof -
  let ?S = "steps_approx n P pc_s"
  have "
    {pc. pc \<in> ?S \<and> (case P ! pc of Some (CEXP ac) \<Rightarrow> True | _ \<Rightarrow> False)}
  = {pc. \<exists> ac. pc \<in> ?S \<and> P ! pc = Some (CEXP ac)}
  " by safe (auto split: option.splits instrc.splits)
  show ?thesis unfolding conjunction_check_def Let_def \<open>_ = _\<close> ..
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
  apply -
  apply (erule disjE)
   apply (drule is_conj'; simp)
    apply (drule check_conj_block)
  apply (subst is_conj; simp)
  done

end

abbreviation "conv B \<equiv> (conv_prog (fst B), (map conv_A' (fst (snd B))), snd (snd B))"

locale UPPAAL_Reachability_Problem_precompiled_start_state =
  UPPAAL_Reachability_Problem_precompiled _ _ _ _ _ pred
  for pred :: "nat list list" +
  fixes s\<^sub>0 :: "int list" (* XXX Why does nat not work? *)
  assumes start_pred:
    "\<forall> q < p. \<exists> pc st s' rs pcs.
       exec (stripfp PROG) max_steps ((pred ! q ! (init ! q)), [], s\<^sub>0, True, []) []
     = Some ((pc, st, s', True, rs), pcs)"
      and bounded: "bounded bounds s\<^sub>0"
      and pred_time_indep: "\<forall> x \<in> set pred. \<forall> pc \<in> set x. time_indep_check prog pc max_steps"
      and upd_time_indep:
        "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, pc_u, _) \<in> set xs.
           time_indep_check prog pc_u max_steps"
     and clock_conj:
       "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (pc_g, _, _, _) \<in> set xs.
           conjunction_check prog pc_g max_steps"
begin

sublocale defs':
  Equiv_TA_Defs "conv N" max_steps .

    lemma equiv_states'_alt_def:
    "equiv.defs.states' s =
      {L. length L = p \<and>
        (\<forall> q < p. L ! q \<in> fst ` fst (equiv.N ! q)
                \<or> L ! q \<in> (snd o snd o snd o snd) ` fst (equiv.N ! q))}"
    unfolding Product_TA_Defs.states_def
    unfolding equiv.defs.N_s_def trans_of_def
    by (simp add: T_s_unfold_1 T_s_unfold_2)

  lemma init_states:
    "init \<in> equiv.defs.states' s\<^sub>0"
    using processes_have_trans start_has_trans
    unfolding equiv_states'_alt_def
    unfolding init_def N_def T_def by force

  lemma p_p[simp]:
    "defs'.p = p"
    unfolding defs'.p_def by simp

  lemma T_s_unfold_1':
    "fst ` defs'.defs.T_s q s = fst ` fst (defs'.N ! q)" if "q < p"
    using \<open>q < p\<close>
    unfolding defs'.defs.T_s_def
    unfolding defs'.state_ta_def
    unfolding defs'.state_trans_t_def p_p
    by force

  lemma T_s_unfold_2':
    "(snd o snd o snd o snd) ` defs'.defs.T_s q s = (snd o snd o snd o snd) ` fst (defs'.N ! q)"
    if "q < p"
    using \<open>q < p\<close>
    unfolding defs'.defs.T_s_def
    unfolding defs'.state_ta_def
    unfolding defs'.state_trans_t_def p_p
    by force

  lemma product_states'_alt_def:
    "defs'.defs.states' s =
      {L. length L = p \<and>
        (\<forall> q < p. L ! q \<in> fst ` fst (defs'.N ! q)
                \<or> L ! q \<in> (snd o snd o snd o snd) ` fst (defs'.N ! q))}"
    unfolding Product_TA_Defs.states_def
    unfolding defs'.defs.N_s_def trans_of_def
    using T_s_unfold_1' T_s_unfold_2'
    by force

  lemma states'_conv[simp]:
    "defs'.defs.states' s = equiv.defs.states' s"
    unfolding product_states'_alt_def equiv_states'_alt_def
    unfolding N_def T_def by simp

  lemma [intro]:
    "init \<in> defs'.defs.states' s\<^sub>0"
    using init_states by simp

  lemma [intro]:
    "bounded defs'.B s\<^sub>0"
    using bounded unfolding bounded_def N_def by simp

  lemma
    "defs'.I = equiv.I"
    by simp

  lemma PF_PF[simp]:
    "defs'.PF = equiv.PF"
    apply simp
    unfolding stripfp_def
    apply (rule ext)
    apply clarsimp
    subgoal for x
      apply (cases "equiv.P x")
       apply simp
      subgoal for a
        by (cases a) auto
      done
    done

  lemma PF_PROG[simp]:
    "equiv.PF = stripfp PROG"
    unfolding N_def by simp

  lemma I_simp[simp]:
    "(equiv.I ! q) l = pred ! q ! l" if "q < p"
    unfolding N_def P_def using \<open>q < p\<close> process_length(3) by simp

  lemma
    "defs'.P = conv_prog PROG"
    by (simp add: N_def)

  lemma states_len[intro]:
    assumes
      "q < p" "L \<in> equiv.defs.states' s"
    shows
      "L ! q < length (trans ! q)"
    using assms unfolding Product_TA_Defs.states_def
    apply simp
    unfolding trans_of_def equiv.defs.N_s_def
    apply (simp add: T_s_unfold_1 T_s_unfold_2)
    unfolding N_def
    apply simp
    unfolding T_def
      using state_set
    unfolding process_length(2)[symmetric]
    apply auto
    apply (erule allE)
    apply (erule impE)
     apply assumption
    apply auto
    by (clarsimp dest!: nth_mem; force)

  lemma equiv_P_simp:
    "equiv.P = PROG"
    unfolding N_def by simp

  lemma [intro]:
    "time_indep (conv_prog equiv.P) max_steps (pred ! q ! (L ! q), [], s, True, [])"
    if "q < p" "L \<in> equiv.defs.states' s"
  proof -
    from that lengths process_length have "q < length pred" "L ! q < length (pred ! q)" by auto
    then have "pred ! q \<in> set pred" "pred ! q ! (L ! q) \<in> set (pred ! q)" by auto
    with pred_time_indep time_indep_overapprox show ?thesis
      by (auto simp: PROG_def equiv_P_simp)
  qed

  lemma [intro]:
    "time_indep (conv_prog PROG) max_steps (pc_u, [], s, True, [])"
    if "q < p" "(l, pc_g, a, pc_u, l') \<in> T q"
  proof -
    from that lengths process_length have
      "q < length trans" "l < length (trans ! q)" "(pc_g, a, pc_u, l') \<in> set (trans ! q ! l)"
      unfolding T_def by auto
    moreover then have "trans ! q \<in> set trans" "trans ! q ! l \<in> set (trans ! q)" by auto
    ultimately show ?thesis using upd_time_indep time_indep_overapprox
      unfolding PROG_def by blast
  qed

  lemma [intro]:
    "u \<turnstile>\<^sub>a ac" if
    "q < defs'.p"
    "(l, pc_g, a, pc_u, l') \<in> fst (defs'.N ! q)"
    "stepst defs'.P max_steps u (pc_g, [], s, True, []) (pc_t, st_t, s_t, True, rs_t)"
    "stepsc defs'.P max_steps u (pc_g, [], s, True, []) (pc', st, s', f', rs)"
    "defs'.P pc' = Some (CEXP ac)"
  proof -
    let ?P = "conv_P prog"
    from that(5) obtain ac' where
      "ac = conv_ac ac'" "prog ! pc' = Some (CEXP ac')" "pc' < length prog"
      apply (clarsimp split: option.split_asm if_split_asm simp add: PROG_def N_def)
      subgoal for z
        by (cases z) auto
      done
    with that have "u \<turnstile>\<^sub>a conv_ac ac'"
      apply -
      apply (rule conjunction_check)
      using clock_conj apply simp_all
      unfolding N_def apply simp_all
      using lengths process_length(2) by (force dest!: nth_mem simp: PROG_def N_def T_def)+
    with \<open>ac = _\<close> show ?thesis by simp
  qed

  sublocale product':
    Equiv_TA "conv N" max_steps init s\<^sub>0
    apply standard
          apply rule
         apply (simp; blast)
         subgoal
           apply clarsimp
           apply (force simp: N_def)
           done
       apply blast
      apply (simp; fail)
    unfolding PF_PF using start_pred apply simp
    by rule

  lemma [simp]:
    "fst ` (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` S = fst ` S"
    by force

  lemma [simp]:
    "(snd \<circ> snd \<circ> snd \<circ> snd) ` (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` S
    = (snd \<circ> snd \<circ> snd \<circ> snd) ` S"
    by force

  (*
  lemma map_trans_of:
    "map trans_of (map conv_A (fst N)) = map (op ` conv_t) (map trans_of (fst N))"
    by (simp add: trans_of_def split: prod.split)

  lemma [simp]:
    "Product_TA_Defs.states (map conv_A (fst N)) = Product_TA_Defs.states (fst N)"
    unfolding Product_TA_Defs.states_def map_trans_of by simp

  lemma [simp]:
    "product.P = P"
    unfolding N_def by simp

  lemma start_pred':
    "\<forall> i < p. (pred ! i ! (init ! i)) s\<^sub>0"
    using start_pred unfolding init_def by auto

  lemma start_pred'':
    "\<forall> i < p. ((P ! i) (init ! i)) s\<^sub>0"
    using start_pred' process_length(3) unfolding P_def by auto

  sublocale product': Prod_TA "(map conv_A (fst N), snd N)" init s\<^sub>0
    by (standard; simp add: init_states start_pred'')
      *)

end (* End of locale *)

locale UPPAAL_Reachability_Problem_precompiled' =
  UPPAAL_Reachability_Problem_precompiled_start_state +
  UPPAAL_Reachability_Problem_precompiled_defs' +
  assumes action_set:
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, a, _) \<in> set xs. pred_act (\<lambda> a. a < na) a"
begin

  (* XXX Why are we re-doing this here? *)
  sublocale Reachability_Problem_Impl_Defs A "(init, s\<^sub>0)" "PR_CONST (\<lambda> (l, s). F l s)" m
    by standard

  definition
    "states' = {(L, s). L \<in> equiv.defs.states' s \<and> check_pred L s}"

  lemma in_trans_in_mapI:
    assumes
      "q < p" "l < length (trans ! q)" "i < length (trans ! q ! l)"
      "(g1, In a, r1) = trans ! q ! l ! i"
    shows "(g1, a, r1) \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
    using assms process_length(2) unfolding trans_in_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, In a, r1)"])

  lemma in_trans_out_mapI:
    assumes
      "q < p" "l < length (trans ! q)" "i < length (trans ! q ! l)"
      "(g1, Out a, r1) = trans ! q ! l ! i"
    shows "(g1, a, r1) \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
    using assms process_length(2) unfolding trans_out_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, Out a, r1)"])

  lemma in_trans_in_mapD:
    assumes
      "(g1, a, r1) \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
      "q < p" "l < length (trans ! q)"
    obtains i where
      "i < length (trans ! q ! l) \<and> trans ! q ! l ! i = (g1, In a, r1)"
    using assms process_length(2) unfolding trans_in_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  (* XXX Remove duplication *)
  lemma in_trans_out_mapD:
    assumes
      "(g1, a, r1) \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
      "q < p" "l < length (trans ! q)"
    obtains i where
      "i < length (trans ! q ! l) \<and> trans ! q ! l ! i = (g1, Out a, r1)"
    using assms process_length(2) unfolding trans_out_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  lemma in_actions_by_stateI:
    assumes
      "(g1, a, r1) \<in> set xs" "a < length acc"
    shows
      "(q, g1, a, r1) \<in> set (actions_by_state q xs acc ! a)
      \<and> a < length (actions_by_state q xs acc)"
    using assms unfolding actions_by_state_def
    apply (induction xs arbitrary: acc)
     apply (simp; fail)
    apply simp
    apply (erule disjE)
     apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto

  lemma in_actions_by_state_preserv:
    assumes
      "(q, g1, a, r1) \<in> set (acc ! a)" "a < length acc"
    shows
      "(q, g1, a, r1) \<in> set (actions_by_state y xs acc ! a)
      \<and> a < length (actions_by_state y xs acc)"
    using assms unfolding actions_by_state_def
    apply -
    apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
    apply (subst list_update_nth_split; auto)
    by auto

  lemma length_actions_by_state_preserv[simp]:
    shows "length (actions_by_state y xs acc) = length acc"
    unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

  lemma in_all_actions_by_stateI:
    assumes
      "a < na" "q < p" "(g1, a, r1) \<in> set (M !! q !! (L ! q))"
    shows
      "(q, g1, a, r1) \<in> set (all_actions_by_state M L ! a)"
    unfolding all_actions_by_state_def
    apply (rule fold_acc_ev_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
          THEN conjunct1]
        )
        apply (rule in_actions_by_state_preserv[THEN conjunct1])
    using assms by (auto intro: in_actions_by_stateI[THEN conjunct1])

  lemma actions_by_state_inj:
    assumes "j < length acc"
    shows "\<forall> (q, a) \<in> set (actions_by_state i xs acc ! j). (q, a) \<notin> set (acc ! j) \<longrightarrow> i = q"
    unfolding actions_by_state_def
    apply (rule fold_acc_preserv
        [where P =
          "\<lambda> acc'. (\<forall> (q, a) \<in> set (acc' ! j). (q, a) \<notin> set (acc ! j) \<longrightarrow> i = q) \<and> j < length acc'",
          THEN conjunct1])
    subgoal for x acc
      by (cases "fst (snd x) = j"; simp)
    using assms by auto

  lemma actions_by_state_inj':
    assumes "j < length acc" "(q, a) \<notin> set (acc ! j)" "(q, a) \<in> set (actions_by_state i xs acc ! j)"
    shows "i = q"
    using actions_by_state_inj[OF assms(1)] assms(2-) by fast

  lemma in_actions_by_stateD:
    assumes
      "(q, g, a, t) \<in> set (actions_by_state i xs acc ! j)" "(q, g, a, t) \<notin> set (acc ! j)"
      "j < length acc"
    shows
      "(g, a, t) \<in> set xs \<and> j = a"
    using assms unfolding actions_by_state_def
    apply -
    apply (drule fold_evD
        [where y = "(g, a, t)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, a', t). a' = j"]
        )
         apply assumption
      (* XXX Define asm split rule *)
        apply (subst (asm) list_update_nth_split[of j]; force)
       apply simp+
     apply (subst (asm) list_update_nth_split[of j]; force)
    by auto

  lemma in_all_actions_by_stateD:
    assumes
      "(q, g1, a, r1) \<in> set (all_actions_by_state M L ! a')" "a' < na"
    shows
      "(g1, a, r1) \<in> set (M !! q !! (L ! q)) \<and> q < p \<and> a' = a"
    using assms
    unfolding all_actions_by_state_def
    apply -
    apply (drule fold_evD''[where y = q and Q = "\<lambda> acc. length acc = na"])
        apply (simp; fail)
       apply (drule actions_by_state_inj'[rotated])
         apply (simp; fail)+
    apply safe
      apply (drule in_actions_by_stateD)
        apply assumption
       apply (rule fold_acc_preserv)
        apply (simp; fail)+
    subgoal premises prems
    proof -
      from prems(2) have "q \<in> set [0..<p]" by auto
      then show ?thesis by simp
    qed
    by (auto intro: fold_acc_preserv dest!: in_actions_by_stateD)

  lemma length_all_actions_by_state_preserv:
      "length (all_actions_by_state M L) = na"
    unfolding all_actions_by_state_def by (auto intro: fold_acc_preserv)

  lemma less_naI:
    assumes
      "q < p"
      "(g1, a, r1) = trans ! q ! l ! j"
      "l < length (trans ! q)"
      "j < length (trans ! q ! l)"
    shows "pred_act (\<lambda>a. a < na) a"
    using action_set assms process_length(2) by (force dest!: nth_mem)

  lemma in_actions_trans_in_mapI:
    assumes
      "pa < p"
      "(g1, In a, r1) = trans ! pa ! (L ! pa) ! j"
      "L ! pa < length (trans ! pa)"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, a, r1) \<in> set (all_actions_by_state (IArray (map IArray trans_in_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_in_mapI)+

  lemma in_actions_trans_out_mapI:
    assumes
      "pa < p"
      "(g1, Out a, r1) = trans ! pa ! (L ! pa) ! j"
      "L ! pa < length (trans ! pa)"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, a, r1) \<in> set (all_actions_by_state (IArray (map IArray trans_out_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_out_mapI)+

  lemma in_pairs_by_actionD2:
    assumes
      "(g, a, r, L', s') \<in> set (pairs_by_action (L, s) xs ys)"
      "\<forall> (q, g, a'', m, l) \<in> set xs. a'' = a'"
      "\<forall> (q, g, a'', m, l) \<in> set ys. a'' = a'"
    shows "check_pred L' s'"
    using assms(1) unfolding pairs_by_action_def using assms(2,3)
    by (clarsimp split: option.split_asm simp: set_map_filter) (clarsimp split: if_split_asm)

  lemma in_pairs_by_actionD1:
    assumes
      "(g, a, r, L', s') \<in> set (pairs_by_action (L, s) xs ys)"
      "\<forall> (q, g, a'', m, l) \<in> set xs. a'' = a'"
      "\<forall> (q, g, a'', m, l) \<in> set ys. a'' = a'"
    obtains
      pa q pc_g1 pc_g2 g1 g2 r1 r2 pc_u1 pc_u2 l1' l2' s1
      x1 x2 x3 x4 x5 y1 y2 y3 y4
    where
      "pa \<noteq> q"
      "(pa, pc_g1, a, pc_u1, l1') \<in> set ys"
      "(q, pc_g2, a, pc_u2, l2') \<in> set xs"
      "L' = L[pa := l1', q := l2']"
      "runf pc_u1 s1 = Some ((x1, x2, s', x3, x4), x5)"
      "runf pc_u2 s = Some ((y1, y2, s1, y3, r2), y4)"
      "check_g pc_g1 s = Some g1" "check_g pc_g2 s = Some g2"
      "r1 = make_reset pc_u1 s"
      "g = g1 @ g2" "r = r1 @ r2"
  proof -
    obtain
      pa q pc_g1 pc_g2 g1 g2 r1 r2 pc_u1 pc_u2 l1' l2' s1
      x1 x2 x3 x4 x5 y1 y2 y3 y4
      where
      "(q, pc_g1, a, pc_u1, l1') \<in> set ys" "(pa, pc_g2, a, pc_u2, l2') \<in> set xs" "q \<noteq> pa"
      "check_g pc_g1 s = Some g1" "check_g pc_g2 s = Some g2"
      "runf pc_u1 s1 = Some ((x1, x2, s', x3, x4), x5)"
      "runf pc_u2 s = Some ((y1, y2, s1, y3, r2), y4)"
      "r1 = make_reset pc_u1 s"
      "Some (g1 @ g2, a, r1 @ r2, L[q := l1', pa := l2'], s') = Some (g, a, r, L', s')"
    proof -
      from assms(1) show ?thesis
      unfolding pairs_by_action_def using assms(2,3)
      apply clarsimp
      unfolding set_map_filter
      apply clarsimp
      apply (clarsimp split: option.split_asm if_split_asm)
      by (force intro!: that)
    qed
    then show ?thesis by (fast intro: that)
  qed

  lemma in_pairs_by_actionD:
    assumes
      "(g, a, r, L', s') \<in> set (pairs_by_action (L, s) xs ys)"
      "\<forall> (q, g, a'', m, l) \<in> set xs. a'' = a'"
      "\<forall> (q, g, a'', m, l) \<in> set ys. a'' = a'"
    obtains
        pa q pc_g1 pc_g2 p1 p2 g1 g2 r1 r2 pc_u1 pc_u2 l1' l2' s1
      x1 x2 x3 x4 x5 y1 y2 y3 y4
    where
      "pa \<noteq> q"
      "(pa, pc_g1, a, pc_u1, l1') \<in> set ys"
      "(q, pc_g2, a, pc_u2, l2') \<in> set xs"
      "L' = L[pa := l1', q := l2']"
      (*"s' = m1 (m2 s)"*)
      "runf pc_u1 s1 = Some ((x1, x2, s', x3, x4), x5)"
      "runf pc_u2 s = Some ((y1, y2, s1, y3, r2), y4)"
      "check_g pc_g1 s = Some g1" "check_g pc_g2 s = Some g2"
      "r1 = make_reset pc_u1 s"
      "g = g1 @ g2" "r = r1 @ r2"
      (* "\<forall> q' < p. (P ! q') (L' ! q') s'" *)
      "check_pred L' s'"
      (* Some ((_, _, s1, _, r2), _) *)
    using in_pairs_by_actionD1[OF assms] in_pairs_by_actionD2[OF assms] by metis

  lemma in_trans_funD:
    assumes "y \<in> set (trans_fun L)"
    shows "y \<in> set (trans_s_fun L) \<or> y \<in> set (trans_i_fun L)"
      using assms unfolding trans_fun_def by auto

  lemma states'_states'[intro]:
    "L \<in> equiv.defs.states' s" if "(L, s) \<in> states'"
    using that unfolding states'_def by auto

  lemma P_unfold:
    "(\<forall>q<p. (equiv.defs.P ! q) (L ! q) s) \<longleftrightarrow> (check_pred L s)"
    unfolding equiv.state_ta_def equiv.state_pred_def check_pred_def using process_length(3)
    apply simp
    unfolding list_all_iff
    unfolding N_def
    unfolding runf_def P_def
      apply safe
     apply (auto split: option.split; auto split: option.split_asm; fail)
    by (force split: option.splits)

  lemma [simp]:
    "equiv.PT = PT"
    unfolding striptp_def N_def by simp

  lemmas [simp] = equiv_P_simp

  lemma transD:
    assumes
      "(pc_g, a, pc_u, l') = trans ! q ! (L ! q) ! j"
      "L ! q < length (trans ! q)" "j < length (trans ! q ! (L ! q))"
      "q < p"
    shows "(L ! q, pc_g, a, pc_u, l') \<in> fst (equiv.N ! q)"
    using assms unfolding N_def T_def by simp solve_ex_triv

  lemma trans_ND:
    assumes
      "(L ! q, pc_g, a, pc_u, l') \<in> fst (equiv.N ! q)"
      "q < p"
    shows
      "equiv.defs.N_s s ! q \<turnstile> L ! q
        \<longrightarrow>\<^bsup>equiv.make_g pc_g s,(a, equiv.make_c pc_g, equiv.make_mf pc_u),equiv.make_f pc_u s\<^esup> l'"
    using assms
    unfolding equiv.defs.N_s_def trans_of_def equiv.defs.T_s_def
    unfolding equiv.state_ta_def equiv.state_trans_t_def
    by clarsimp solve_ex_triv+

  lemma make_f_unfold:
    "equiv.make_f pc s = make_reset pc s"
    unfolding make_reset_def equiv.make_f_def runf_def by simp

  lemma make_g_simp:
    assumes "check_g pc_g s = Some g1"
    shows "g1 = equiv.make_g pc_g s"
    using assms unfolding check_g_def equiv.make_g_def runt_def
    by (clarsimp split: option.splits bool.splits simp: make_cconstr_def)

  lemma make_c_simp:
    assumes "check_g pc_g s = Some g1"
    shows "equiv.make_c pc_g s"
    using assms unfolding check_g_def equiv.make_c_def runt_def
    by (clarsimp split: option.splits bool.splits simp: make_cconstr_def)

  lemma make_reset_simp:
    assumes "runf pc_u s = Some ((y1, y2, s1, y3, r2), y4)"
    shows "make_reset pc_u s = r2"
    using assms unfolding runf_def make_reset_def by (auto split: option.splits)

  lemma make_mf_simp:
    assumes "runf pc_u s = Some ((y1, y2, s1, y3, r2), y4)"
    shows "equiv.make_mf pc_u s = Some s1"
    using assms unfolding runf_def equiv.make_mf_def by (auto split: option.splits)

  lemma trans_fun_trans_of':
    "(trans_fun, trans_of A) \<in> transition_rel states'"
    unfolding transition_rel_def T_def
    apply simp
    unfolding trans_of_def
    apply safe
    subgoal for L s g a r L' s'
      unfolding equiv.defs.prod_ta_def equiv.defs.prod_trans_def
      apply simp
      apply safe
      subgoal
        apply (rule trans_i_fun_trans_fun)
        unfolding equiv.defs.prod_trans_i_alt_def
        apply safe
          unfolding trans_fun_def trans_i_from_def trans_i_fun_def
          unfolding Product_TA_Defs.product_trans_i_def
          apply clarsimp
          subgoal premises prems for c m p' l'
          proof -
            from prems have "L ! p' < length (trans ! p')" by auto
            from prems obtain pc_g pc_u where
              "(L ! p', pc_g, Sil a, pc_u, l') \<in> T p'"
              "g = equiv.make_g pc_g s" "r = equiv.make_f pc_u s"
              "c = equiv.make_c pc_g" "m = equiv.make_mf pc_u"
              unfolding equiv.defs.N_s_def trans_of_def equiv.defs.T_s_def
              unfolding equiv.state_ta_def equiv.state_trans_t_def
              apply clarsimp
              unfolding N_def T_def by clarsimp
            from this(1) have "(pc_g, Sil a, pc_u, l') \<in> set (trans ! p' ! (L ! p'))"
              unfolding T_def by auto
            moreover have "check_g pc_g s = Some g"
              using \<open>g = _\<close> \<open>c = _\<close> \<open>c s\<close>
                unfolding check_g_def equiv.make_g_def equiv.make_c_def
                by (auto split: option.splits simp: runt_def make_cconstr_def)
            moreover obtain x1 x2 x3 pcs where "runf pc_u s = Some ((x1, x2, s', x3, r), pcs)"
              using \<open>r = _\<close> \<open>m = _\<close> prems(5)
              unfolding equiv.make_f_def equiv.make_mf_def runf_def trans_of_def
              by (auto split: option.splits)
            moreover have "check_pred (L[p' := l']) s'"
              using prems(3) unfolding P_unfold .
            ultimately show ?thesis using process_length(2) \<open>p' < _\<close> \<open>L ! p' < _\<close>
              by (force simp: set_map_filter trans_i_map_def)
          qed
          done
        subgoal
          apply (rule trans_s_fun_trans_fun)
            unfolding equiv.defs.prod_trans_s_alt_def
            apply safe
          unfolding trans_fun_def trans_s_fun_def
          unfolding Product_TA_Defs.product_trans_s_def
          apply clarsimp
          subgoal premises prems for ci co mi mo s1 q1 q2 g1 g2 r1 r2 l1' l2'
          proof -
            from prems have "L ! q1 < length (trans ! q1)" "L ! q2 < length (trans ! q2)" by auto
            from prems obtain pc_g1 pc_u1 where
              "(L ! q1, pc_g1, In a, pc_u1, l1') \<in> T q1"
              "g1 = equiv.make_g pc_g1 s" "r1 = equiv.make_f pc_u1 s"
              "ci = equiv.make_c pc_g1" "mi = equiv.make_mf pc_u1"
              unfolding equiv.defs.N_s_def trans_of_def equiv.defs.T_s_def
              unfolding equiv.state_ta_def equiv.state_trans_t_def
              apply clarsimp
              unfolding N_def T_def by clarsimp
            from prems obtain pc_g2 pc_u2 where
              "(L ! q2, pc_g2, Out a, pc_u2, l2') \<in> T q2"
              "g2 = equiv.make_g pc_g2 s" "r2 = equiv.make_f pc_u2 s"
              "co = equiv.make_c pc_g2" "mo = equiv.make_mf pc_u2"
              unfolding equiv.defs.N_s_def trans_of_def equiv.defs.T_s_def
              unfolding equiv.state_ta_def equiv.state_trans_t_def
              apply clarsimp
              unfolding N_def T_def by clarsimp
            from \<open>_ \<in> T q1\<close> have "(pc_g1, In a, pc_u1, l1') \<in> set (trans ! q1 ! (L ! q1))"
              unfolding T_def by auto
            from \<open>_ \<in> T q2\<close> have "(pc_g2, Out a, pc_u2, l2') \<in> set (trans ! q2 ! (L ! q2))"
              unfolding T_def by auto
            moreover have "check_g pc_g1 s = Some g1" "check_g pc_g2 s = Some g2"
              using \<open>g1 = _\<close> \<open>ci = _\<close> \<open>ci s\<close> \<open>g2 = _\<close> \<open>co = _\<close> \<open>co s\<close>
                unfolding check_g_def equiv.make_g_def equiv.make_c_def
                by (auto split: option.splits simp: runt_def make_cconstr_def)
            moreover obtain x1 x2 x3 pcs where "runf pc_u2 s = Some ((x1, x2, s1, x3, r2), pcs)"
              using \<open>r2 = _\<close> \<open>mo = _\<close> \<open>Some s1 = _\<close>
              unfolding equiv.make_f_def equiv.make_mf_def runf_def trans_of_def
              by (auto split: option.splits)
            moreover obtain x1 x2 x3 x4 pcs where "runf pc_u1 s1 = Some ((x1, x2, s', x3, x4), pcs)"
              using \<open>r1 = _\<close> \<open>mi = _\<close> \<open>Some s' = _\<close>
              unfolding equiv.make_f_def equiv.make_mf_def runf_def trans_of_def
              by (auto split: option.splits)
             moreover have "r1 = make_reset pc_u1 s"
              using \<open>r1 = _\<close> unfolding make_reset_def equiv.make_f_def runf_def by auto
            moreover have "check_pred (L[q1 := l1', q2 := l2']) s'"
              using prems(5) unfolding P_unfold .
            moreover have "a < na"
                using action_set \<open>_ \<in> set (trans ! q1 ! (L ! q1))\<close> \<open>q1 < _\<close> \<open>L ! q1 < _\<close>
                      process_length(2)
                by (fastforce dest!: nth_mem)
              moreover have
                "(q1, pc_g1, a, pc_u1, l1')
                \<in> set (all_actions_by_state (nested_list_to_iarray trans_in_map) L ! a)"
              using \<open>L ! q1 < _\<close> \<open>_ \<in> set (trans ! q1 ! (L ! q1))\<close> \<open>q1 < p\<close>
              by (force intro: in_actions_trans_in_mapI dest: mem_nth)
            moreover have
              "(q2, pc_g2, a, pc_u2, l2')
              \<in> set (all_actions_by_state (nested_list_to_iarray trans_out_map) L ! a)"
              using \<open>L ! q2 < _\<close> \<open>_ \<in> set (trans ! q2 ! (L ! q2))\<close> \<open>q2 < p\<close>
              by (force intro: in_actions_trans_out_mapI dest: mem_nth)
            ultimately show ?thesis
              using process_length(2) \<open>q1 < _\<close> \<open>L ! q1 < _\<close> \<open>q2 < _\<close> \<open>L ! q2 < _\<close> \<open>_ \<noteq> _\<close>
              unfolding pairs_by_action_def
                apply -
                apply (rule bexI[where x = a])
                by auto(force simp: set_map_filter)
          qed
          done
        done
      subgoal for L s g a r L' s'
      apply (drule in_trans_funD)
      apply (erule disjE)
      unfolding equiv.defs.prod_ta_def equiv.defs.prod_trans_def
       apply simp
       apply (rule disjI2)
      subgoal
        unfolding equiv.defs.prod_trans_s_alt_def
        apply safe
        unfolding trans_s_fun_def
        apply clarsimp
          subgoal for x
        apply (erule in_pairs_by_actionD[where a' = x])
        apply (auto dest: in_all_actions_by_stateD; fail)
             apply (auto dest: in_all_actions_by_stateD; fail)
              apply (drule in_all_actions_by_stateD, assumption)
          apply (drule in_all_actions_by_stateD, assumption)
            apply safe
          apply (erule in_trans_in_mapD)
              apply (simp; fail)
             apply blast
              apply (erule in_trans_out_mapD)
            apply blast
             apply blast
            apply (simp only: ex_simps[symmetric])
            unfolding states'_def
            apply (clarsimp)
            unfolding P_unfold
            apply simp thm transD[rotated 2]
            apply (drule transD[rotated 2], solve_triv+, blast)
            apply (drule transD[rotated 2], solve_triv+, blast) thm trans_ND
            apply (drule_tac s = s in trans_ND, assumption)
            apply (drule_tac s = s in trans_ND, assumption)
            unfolding Product_TA_Defs.product_trans_s_def
            apply clarsimp
            unfolding trans_of_def
            subgoal
              apply (simp only: ex_simps[symmetric])
              apply defer_ex
              apply defer_ex
              apply solve_ex_triv
              apply solve_ex_triv
              apply solve_ex_triv
              unfolding make_f_unfold
              by (auto simp add: make_c_simp make_mf_simp make_reset_simp make_g_simp[symmetric])
            done
          done
      subgoal
        apply simp
        apply (rule disjI1)
        using process_length(2)
        unfolding equiv.defs.prod_trans_i_alt_def
        apply simp
        unfolding P_unfold
        unfolding trans_i_fun_def trans_i_from_def states'_def
        apply simp
        apply (erule bexE)

        unfolding set_map_filter thm set_map_filter
        apply simp
        subgoal premises prems for q
        proof -
          from prems have len: "q < length trans" "L ! q < length (trans ! q)" by auto
          from prems(4) obtain pc_g pc_u l' x1 x2 x3 x4 where
            "(pc_g, a, pc_u, l') \<in> set (IArray.list_of (map IArray trans_i_map ! q) ! (L ! q))"
            "check_g pc_g s = Some g"
            "r = make_reset pc_u s"
            "runf pc_u s = Some ((x1, x2, s', x3, r), x4)"
            "check_pred (L[q := l']) s'"
            "L' = L[q := l']"
            apply atomize_elim
              unfolding make_reset_def
              by (force split: option.splits if_split_asm)
          moreover then have
              "(L, g, (a, Act (equiv.make_c pc_g, equiv.make_mf pc_u)), r, L')
              \<in> Product_TA_Defs.product_trans_i (equiv.defs.N_s s)"
          unfolding Product_TA_Defs.product_trans_i_def
          apply clarsimp
          apply solve_ex_triv
          apply safe
          using prems apply simp
          unfolding trans_i_map_def
          using len \<open>q < p\<close> apply (clarsimp simp: set_map_filter)
            apply (clarsimp split: act.split_asm)
           apply (frule make_c_simp)
           apply (drule mem_nth)
           apply safe
           apply (drule transD[rotated], solve_triv+)
           apply (drule trans_ND)
            apply solve_triv
             apply (subst make_g_simp)
          using \<open>q < p\<close> prems(1) by (auto simp add: make_f_unfold)
        ultimately show ?thesis
          by (force simp: make_mf_simp dest: make_c_simp)
      qed
      done
    done
  done

  (* XXX Unused *)
  lemma transition_rel_mono:
    "(a, b) \<in> transition_rel B" if "(a, b) \<in> transition_rel C" "B \<subseteq> C"
    using that unfolding transition_rel_def b_rel_def fun_rel_def by auto

end

context
  Equiv_TA_Defs
begin

  lemma state_set_subs: (* XXX Clean *)
    "state_set (trans_of (defs.product s''))
  \<subseteq> {L. length L = defs.p \<and> (\<forall>q<defs.p. L ! q \<in> State_Networks.state_set (fst (defs.N ! q)))}"
    unfolding defs.states'_alt_def[symmetric]
    unfolding defs.N_s_def
    unfolding state_set_def Product_TA_Defs.states_def
    unfolding trans_of_def
    unfolding Product_TA_Defs.product_ta_def Product_TA_Defs.product_trans_def
    unfolding Product_TA_Defs.product_trans_i_def Product_TA_Defs.product_trans_s_def
    unfolding defs.T_s_def
      unfolding Product_TA_Defs.states_def trans_of_def
      apply simp
      apply safe
              apply (simp; fail)
      using [[goals_limit = 1]]
             apply force
            apply force
           apply (force simp: image_iff)
          apply force
         apply (case_tac "pa = q")
          apply (force simp: image_iff)
         apply (force simp: image_iff)
        apply force
       apply (case_tac "qa = q")
        apply force
      apply (case_tac "qa = pa")
        by (force simp: image_iff)+

end

context UPPAAL_Reachability_Problem_precompiled_defs
begin

  lemma N_s_state_indep:
    assumes "(L ! q, g, a, r, l') \<in> map trans_of (equiv.defs.N_s s) ! q" "q < p"
    obtains g r where "(L ! q, g, a, r, l') \<in> map trans_of (equiv.defs.N_s s') ! q"
    using assms unfolding trans_of_def equiv.defs.N_s_def equiv.defs.T_s_def by force

  lemma fst_product_state_indep:
    "fst ` fst (equiv.defs.product s) = fst ` fst (equiv.defs.product s')"
    unfolding Product_TA_Defs.product_ta_def Product_TA_Defs.product_trans_def
    unfolding Product_TA_Defs.product_trans_s_def Product_TA_Defs.product_trans_i_def
    apply simp
    unfolding equiv.defs.states'_alt_def
    apply clarsimp
    apply rule
    subgoal
      apply rule
      apply clarsimp
      apply (erule disjE)
       apply (erule conjE exE)+
       apply (erule N_s_state_indep)
        apply (simp; fail)
       apply (rule img_fst)
       apply (rule Set.UnI1)
       apply (subst mem_Collect_eq)
       apply solve_ex_triv+
      apply (erule conjE exE)+
      apply (erule N_s_state_indep, (simp; fail))
      apply (erule N_s_state_indep, (simp; fail))
      apply (rule img_fst)
      apply (rule Set.UnI2)
      apply (subst mem_Collect_eq)
      apply (rule exI)+
      apply (rule conjI)
       defer
      by solve_ex_triv+
    subgoal
      apply rule
      apply clarsimp
      apply (erule disjE)
       apply (erule conjE exE)+
       apply (erule N_s_state_indep)
        apply (simp; fail)
       apply (rule img_fst)
       apply (rule Set.UnI1)
       apply (subst mem_Collect_eq)
       apply solve_ex_triv+
      apply (erule conjE exE)+
      apply (erule N_s_state_indep, (simp; fail))
      apply (erule N_s_state_indep, (simp; fail))
      apply (rule img_fst)
      apply (rule Set.UnI2)
      apply (subst mem_Collect_eq)
      apply (rule exI)+
      apply (rule conjI)
       defer
      by solve_ex_triv+
    done

  lemma last_product_state_indep:
    "(snd o snd o snd o snd) ` fst (equiv.defs.product s)
   = (snd o snd o snd o snd) ` fst (equiv.defs.product s')"
    unfolding Product_TA_Defs.product_ta_def Product_TA_Defs.product_trans_def
    unfolding Product_TA_Defs.product_trans_s_def Product_TA_Defs.product_trans_i_def
    apply simp
    unfolding equiv.defs.states'_alt_def
    apply clarsimp
    apply rule
    subgoal
      apply rule
      apply clarsimp
      apply (erule disjE)
       apply (erule conjE exE)+
       apply (erule N_s_state_indep)
        apply (simp; fail)
       apply (rule )
        prefer 2
        apply (rule Set.UnI1)
        apply (subst mem_Collect_eq)
        apply solve_ex_triv+
      apply (erule conjE exE)+
      apply (erule N_s_state_indep, (simp; fail))
      apply (erule N_s_state_indep, (simp; fail))
      apply (rule )
       defer
       apply (rule Set.UnI2)
       apply (subst mem_Collect_eq)
       apply (rule exI)+
       apply (rule conjI)
        defer
        apply solve_ex_triv+
       defer
       apply (rule HOL.refl)
      by simp
    subgoal
      apply rule
      apply clarsimp
      apply (erule disjE)
      apply (erule conjE exE)+
      apply (erule N_s_state_indep)
      apply (simp; fail)
      apply (rule )
      prefer 2
      apply (rule Set.UnI1)
      apply (subst mem_Collect_eq)
      apply solve_ex_triv+
      apply (erule conjE exE)+
      apply (erule N_s_state_indep, (simp; fail))
      apply (erule N_s_state_indep, (simp; fail))
      apply (rule )
      defer
      apply (rule Set.UnI2)
      apply (subst mem_Collect_eq)
      apply (rule exI)+
      apply (rule conjI)
      defer
      apply solve_ex_triv+
      defer
      apply (rule HOL.refl)
      by simp
    done

  lemma state_set_T':
    "state_set (equiv.defs.T' s'') \<supseteq> fst ` state_set (trans_of A)"
    unfolding trans_of_def
    unfolding state_set_def
    unfolding Prod_TA_Defs.prod_ta_def equiv.defs.prod_trans_def
    apply simp
    unfolding equiv.defs.prod_trans_i_def equiv.defs.prod_trans_s_def
    unfolding trans_of_def
    apply safe
       apply (subst fst_product_state_indep; force)
      apply (subst fst_product_state_indep; force)
     apply (subst (asm) last_product_state_indep; force)
    by (subst (asm) last_product_state_indep; force)

  lemma state_set_T'2[simplified]:
    "length L = equiv.defs.p"
    "\<forall>q<equiv.defs.p. L ! q \<in> State_Networks.state_set (fst (equiv.defs.N ! q))"
    if "(L, s) \<in> state_set (trans_of A)"
    using subset_trans [OF state_set_T' equiv.state_set_subs] that by blast+

  lemma state_set_states':
    "L \<in> equiv.defs.states' s" if "(L, s) \<in> state_set (trans_of A)"
    using state_set_T'2[OF that] unfolding equiv.defs.states'_alt_def by simp

  lemma state_set_pred:
    "\<forall>q<p. (equiv.defs.P ! q) (L ! q) s" if "(L, s) \<in> state_set (trans_of A)"
    using that
    unfolding Normalized_Zone_Semantics_Impl_Refine.state_set_def
    unfolding trans_of_def Prod_TA_Defs.prod_ta_def Prod_TA_Defs.prod_trans_def
    unfolding Prod_TA_Defs.prod_trans_i_def Prod_TA_Defs.prod_trans_s_def
    by force

end

lemma (in UPPAAL_Reachability_Problem_precompiled') state_set_states:
  "state_set (trans_of A) \<subseteq> states'"
  using state_set_states' state_set_pred unfolding states'_def P_unfold by auto

context UPPAAL_Reachability_Problem_precompiled'
begin

  lemma p_p_2[simp]:
  "defs'.defs.p = p"
  unfolding defs'.p_p p_p ..

  lemma len_product'_N[simp]:
    "length defs'.defs.N = p"
    unfolding defs'.defs.p_def[symmetric] by (rule p_p_2)

  lemma len_equiv_N:
    "length equiv.defs.N = p"
    unfolding equiv.defs.p_def[symmetric] by simp

  lemma
    "defs'.p = p"
    unfolding defs'.p_def by simp

  lemma equiv_p_p: "equiv.p = p"
    by simp

      (* R *)
  lemma init_states:
    "init \<in> equiv.defs.states' s\<^sub>0"
    using processes_have_trans start_has_trans
    unfolding equiv_states'_alt_def
    unfolding init_def N_def T_def by force

  lemma start_pred':
    "check_pred init s\<^sub>0"
    using start_pred bounded unfolding check_pred_def runf_def list_all_iff
    by (fastforce split: option.split)

  lemma start_states':
    "(init, s\<^sub>0) \<in> states'"
    using start_pred' init_states unfolding states'_def by auto

  lemma trans_fun_trans_of[intro, simp]:
    "(trans_fun, trans_of A) \<in> transition_rel states"
    using trans_fun_trans_of' state_set_states start_states' unfolding transition_rel_def by blast

  definition
    "inv_fun \<equiv> \<lambda> (L, _). concat (map (\<lambda> i. IArray (map IArray inv) !! i !! (L ! i)) [0..<p])"

  lemma states_states':
    "states \<subseteq> states'"
    using state_set_states start_states' by auto

  lemma [simp]:
    "length L = p" if "(L, s) \<in> states'"
    using that  unfolding states'_def by auto

  lemma inv_simp:
    "I q (L ! q) = inv ! q ! (L ! q)" if "q < p" "(L, s) \<in> states'"
    unfolding I_def using that states'_states'[OF that(2)] lengths by (auto dest!: states_len)

  lemma inv_fun_inv_of':
    "(inv_fun, inv_of A) \<in> inv_rel states'"
    unfolding inv_rel_def
    apply (clarsimp simp: equiv.defs.inv_of_simp Product_TA_Defs.inv_of_product)
    using process_length(1)
    unfolding inv_fun_def Product_TA_Defs.product_invariant_def init_def
    unfolding equiv.defs.N_s_def
    apply simp
    apply (rule arg_cong[where f = concat])
    unfolding inv_of_def Equiv_TA_Defs.state_ta_def apply simp
    unfolding equiv.state_inv_def N_def Equiv_TA_Defs.state_inv_def
    by (auto simp: inv_simp)

  lemma inv_rel_mono:
    "(a, b) \<in> inv_rel B" if "(a, b) \<in> inv_rel C" "B \<subseteq> C"
    using that unfolding inv_rel_def b_rel_def fun_rel_def by auto

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel states"
    using inv_fun_inv_of' states_states' by (rule inv_rel_mono)

  definition "final_fun \<equiv> \<lambda> (L, s). check_bexp formula L s"

  lemma final_fun_final':
    "(final_fun, (\<lambda> (l, s). F l s)) \<in> inv_rel states'"
    unfolding F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
     by (force dest!: states'_states')

  lemma final_fun_final[intro, simp]:
    "(final_fun, (\<lambda> (l, s). F l s)) \<in> inv_rel states"
    using final_fun_final' states_states' by (rule inv_rel_mono)

  lemma fst_clkp_setD:
    assumes "(c, d) \<in> clkp_set A"
    shows "c > 0" "c \<le> m" "d \<in> range int"
    using assms clock_set consts_nats clkp_set'_subs unfolding Nats_def clk_set'_def by force+

  lemma
    "\<forall>i<Suc m. k ! i = k_fun i"
    unfolding k_fun_def by simp

  lemma k_k'[intro]:
    "map int k = k'"
    apply (rule nth_equalityI)
     using k_length length_k' apply (auto; fail)
     unfolding k'_def apply (simp add: k_length del: upt_Suc)
     unfolding k_fun_def by simp

  lemma iarray_k'[intro]:
    "(uncurry0 (return (IArray (map int k))), uncurry0 (Refine_Basic.RETURN k'))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
    unfolding br_def by sepref_to_hoare sep_auto

  lemma init_has_trans:
    "(init, s\<^sub>0) \<in> fst ` (trans_of A) \<longleftrightarrow> trans_fun (init, s\<^sub>0) \<noteq> []"
    apply standard
    using trans_fun_trans_of unfolding transition_rel_def apply force
    using trans_fun_trans_of' start_states' unfolding transition_rel_def by fast

end (* End of context *)

ML \<open>
    fun pull_let u t =
      let
        val t1 = abstract_over (u, t);
        val r1 = Const (@{const_name "HOL.Let"}, dummyT) $ u $ Abs ("I", dummyT, t1);
        val ct1 = Syntax.check_term @{context} r1;
        val g1 =
          Goal.prove @{context} [] [] (Logic.mk_equals (t, ct1))
          (fn {context, ...} => EqSubst.eqsubst_tac context [0] [@{thm Let_def}] 1
          THEN resolve_tac context [@{thm Pure.reflexive}] 1)
      in g1 end;

    fun get_rhs thm =
      let
        val Const ("Pure.eq", _) $ _ $ r = Thm.full_prop_of thm
      in r end;

    fun get_lhs thm =
      let
        val Const ("Pure.imp", _) $ (Const ("Pure.eq", _) $ l $ _) $ _ = Thm.full_prop_of thm
      in l end;

    fun pull_tac' u ctxt thm =
      let
        val l = get_lhs thm;
        val rewr = pull_let u l;
      in Local_Defs.unfold_tac ctxt [rewr] thm end;

    fun pull_tac u ctxt = SELECT_GOAL (pull_tac' u ctxt) 1;
  \<close>

context UPPAAL_Reachability_Problem_precompiled'
begin

  sublocale impl:
    Reachability_Problem_Impl
      trans_fun inv_fun final_fun "IArray (map int k)" A "(init, s\<^sub>0)"
      "PR_CONST ((\<lambda> (l, s). F l s))" m k_fun
    unfolding PR_CONST_def by (standard; rule)

  (* XXX Unused *)
  lemma length_reachable:
  "length L' = p" if "E\<^sup>*\<^sup>* a\<^sub>0 ((L', s), u)"
    using states_states' impl.reachable_states[unfolded reachable_def, OF that]
    unfolding reachable_def by (force simp: init_def)

  lemma length_steps:
  "length L' = p" if "conv_A A \<turnstile> \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>" "\<forall>c\<in>{1..m}. u c = 0"
    using that reachable_decides_emptiness'[of "(L', s')"] by (auto intro: length_reachable)

  lemma F_reachable_correct':
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv_A A \<turnstile> \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s'
      )"
    unfolding F_reachable_def reachable_def using reachability_check unfolding F_def by auto

  lemma F_reachable_correct'':
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv_A A \<turnstile> \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s'
      )"
    unfolding F_reachable_correct' using length_steps by metis

  lemma PT_PT:
    "defs'.PT = equiv.PT"
    apply simp
    unfolding striptp_def
    apply (rule ext)
    apply clarsimp
    subgoal for x
      apply (cases "PROG x")
       apply simp
      subgoal for a
        by (cases a) auto
      done
    done

  lemma P_P[simp]:
    "defs'.defs.P = equiv.defs.P"
    unfolding Equiv_TA_Defs.state_ta_def
    unfolding Equiv_TA_Defs.p_def
    unfolding Equiv_TA_Defs.state_pred_def
    using PF_PF by (auto split: option.split)

  lemma map_map_filter:
    "map f (List.map_filter g xs) = List.map_filter (map_option f o g) xs"
    by (induction xs; simp add: List.map_filter_simps split: option.split)


  lemma make_g_conv:
    "defs'.make_g = conv_cc oo equiv.make_g"
    unfolding Equiv_TA_Defs.make_g_def PT_PT PF_PF apply simp
    apply (rule ext)
    apply (rule ext)
    apply simp
    apply (auto split: option.splits simp: map_map_filter)
    apply (rule arg_cong2[where f = List.map_filter])
    by (auto split: option.split instrc.split)

  lemma make_c_conv:
    "defs'.make_c = equiv.make_c"
    unfolding Equiv_TA_Defs.make_c_def PT_PT by simp

  lemma make_f_conv:
    "defs'.make_f = equiv.make_f"
    unfolding Equiv_TA_Defs.make_f_def PF_PF by simp

  lemma make_mf_conv:
    "defs'.make_mf = equiv.make_mf"
    unfolding Equiv_TA_Defs.make_mf_def PF_PF by simp

  lemmas make_convs = make_g_conv make_c_conv make_f_conv make_mf_conv

  lemma state_trans_conv:
    "Equiv_TA_Defs.state_trans_t (conv N) max_steps q
    = (\<lambda> (a, b, c). (a, \<lambda> x. conv_cc (b x), c)) ` equiv.state_trans q" if \<open>q < p\<close>
    unfolding Equiv_TA_Defs.state_trans_t_def image_Collect
    using \<open>q < _\<close> make_convs by (force split: prod.splits)+

  lemma map_conv_t:
    "map trans_of (defs'.defs.N_s s) ! q = conv_t ` (map trans_of (equiv.defs.N_s s) ! q)"
    if \<open>q < p\<close>
    using \<open>q < p\<close>
    apply (subst nth_map)
    unfolding defs'.defs.N_s_length p_p_2
     apply assumption
    apply (subst nth_map)
    unfolding equiv.defs.N_s_length
     apply simp
    unfolding trans_of_def Prod_TA_Defs.N_s_def
    unfolding len_equiv_N len_product'_N
    apply simp
    unfolding Prod_TA_Defs.T_s_def
    unfolding image_Collect
    unfolding Equiv_TA_Defs.state_ta_def Equiv_TA_Defs.p_def
    apply simp
    using state_trans_conv[of q]
    apply simp
    apply auto
     apply force
    apply solve_ex_triv+
    unfolding image_iff by force (* XXX Slow *)

  lemma product_trans_t_conv:
    "Product_TA_Defs.product_trans_s (defs'.defs.N_s s)
     = conv_t ` Product_TA_Defs.product_trans_s (equiv.defs.N_s s)"
    unfolding Product_TA_Defs.product_trans_s_def
    apply (simp only: states'_conv)
      apply safe
     apply (simp only: equiv.states'_len_simp equiv_p_p map_conv_t)
      unfolding image_Collect
      apply (simp split: prod.split)
       apply safe
      subgoal
        by defer_ex solve_ex_triv+
      subgoal
        by solve_ex_triv+ (force simp only: equiv.states'_len_simp equiv_p_p map_conv_t)
      done

  lemma product_trans_t_conv':
    "Product_TA_Defs.product_trans_i (defs'.defs.N_s s)
     = conv_t ` Product_TA_Defs.product_trans_i (equiv.defs.N_s s)"
    unfolding Product_TA_Defs.product_trans_i_def
    apply (simp only: states'_conv)
      apply safe
     apply (simp only: equiv.states'_len_simp equiv_p_p map_conv_t)
      unfolding image_Collect
      apply (simp split: prod.split)
       apply safe
      subgoal
        by defer_ex solve_ex_triv+
      subgoal
        by solve_ex_triv+ (force simp only: equiv.states'_len_simp equiv_p_p map_conv_t)
      done

  lemma prod_trans_s_conv:
    "defs'.defs.prod_trans_s = conv_t ` equiv.defs.prod_trans_s"
    unfolding defs'.defs.prod_trans_s_alt_def
    unfolding equiv.defs.prod_trans_s_alt_def
    unfolding product_trans_t_conv
    unfolding p_p_2 P_P
    apply simp
    apply safe
    unfolding p_p P_P
     apply (simp add: image_Collect)
     apply solve_ex_triv
    subgoal
      apply defer_ex
      apply defer_ex
      by solve_ex_triv+
    subgoal
      apply defer_ex
      apply defer_ex
      by solve_ex_triv+
    done

  lemma prod_trans_i_conv:
      "defs'.defs.prod_trans_i = conv_t ` equiv.defs.prod_trans_i"
      unfolding defs'.defs.prod_trans_i_alt_def
      unfolding equiv.defs.prod_trans_i_alt_def
      unfolding product_trans_t_conv'
      unfolding p_p_2 P_P
      apply simp
      apply safe
      unfolding p_p P_P
       apply (simp add: image_Collect)
       apply solve_ex_triv
      subgoal
        apply defer_ex
        apply defer_ex
        by solve_ex_triv+
      subgoal
        apply defer_ex
        apply defer_ex
        by solve_ex_triv+
      done

  lemma prod_trans_conv:
    "defs'.defs.prod_trans = conv_t ` equiv.defs.prod_trans"
    unfolding defs'.defs.prod_trans_def
    unfolding equiv.defs.prod_trans_def
    unfolding prod_trans_s_conv
    unfolding prod_trans_i_conv image_Un ..

  lemma prod_invariant_conv:
    "defs'.defs.prod_invariant = (map conv_ac \<circ>\<circ> Prod_TA_Defs.prod_invariant) EA"
    apply (rule ext)
    apply safe
    unfolding defs'.defs.prod_invariant_def equiv.defs.prod_invariant_def
    unfolding Product_TA_Defs.product_ta_def inv_of_def
    apply simp
    unfolding Product_TA_Defs.product_invariant_def List.map_concat
    apply (simp add: Prod_TA_Defs.N_s_length)
    unfolding Equiv_TA_Defs.p_p Equiv_TA_Defs.p_def apply simp
    apply (rule cong[where f = concat])
     apply (rule HOL.refl)
    unfolding Prod_TA_Defs.N_s_def inv_of_def Equiv_TA_Defs.state_ta_def
    unfolding Equiv_TA_Defs.p_def unfolding Equiv_TA_Defs.state_inv_def
    by (simp split: prod.split)

  lemma prod_conv: "defs'.defs.prod_ta = conv_A A"
    unfolding defs'.defs.prod_ta_def
    unfolding equiv.defs.prod_ta_def
    by (simp add: prod_invariant_conv[symmetric] prod_trans_conv[symmetric])

  lemma F_reachable_correct:
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s'
      )"
      unfolding F_reachable_correct''
      apply (subst product'.prod_correct[symmetric])
      using prod_conv p_p p_gt_0 by auto

  definition
    "reachability_checker
    \<equiv> worklist_algo2 impl.subsumes_impl impl.a\<^sub>0_impl impl.F_impl impl.succs_impl"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
      uncurry0 (
        Refine_Basic.RETURN (\<exists> L' s' u u'.
        conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s')
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using impl.hnr_F_reachable unfolding reachability_checker_def F_reachable_correct .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> L' s' u u'.
        conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s')
       )
    >\<^sub>t"
   apply (rule cons_post_rule)
   using reachability_check[to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  subsubsection \<open>Post-processing\<close>

  schematic_goal succs_impl_alt_def:
    "impl.succs_impl \<equiv> ?impl"
  unfolding impl.succs_impl_def
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def] trans_s_fun_def trans_i_fun_def trans_i_from_def
   apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
  by (rule Pure.reflexive)

  lemma reachability_checker_alt_def':
    "reachability_checker \<equiv>
      let
        sub = impl.subsumes_impl;
        start = impl.a\<^sub>0_impl;
        final = impl.F_impl;
        succs =  impl.succs_impl
      in worklist_algo2 sub start final succs"
    unfolding reachability_checker_def by simp

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
    unfolding reachability_checker_alt_def' impl.succs_impl_def
    (*apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>) *)
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
    apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
    unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def trans_i_from_def
   apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
   unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
   unfolding impl.F_impl_def
   unfolding final_fun_def[abs_def]
   unfolding impl.subsumes_impl_def
  by (rule Pure.reflexive)

end (* End of locale *)

(*
context State_Network_Reachability_Problem_precompiled_int_vars
begin

  sublocale State_Network_Reachability_Problem_precompiled' p m k inv trans' final pred' s\<^sub>0
    by (standard; rule init_pred actions_bounded)

  schematic_goal reachability_checker_alt_def:
      "reachability_checker \<equiv> ?impl"
    unfolding reachability_checker_alt_def .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> L' s' u u'.
        (map conv_A (fst N), snd N) \<turnstile> \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i)))
       )
    >\<^sub>t"
   by (rule reachability_checker_hoare)

end
*)

subsection \<open>Check preconditions\<close>

context UPPAAL_Reachability_Problem_precompiled_defs
begin

  definition
    "collect_cexp = {ac. Some (CEXP ac) \<in> set prog}"

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

  abbreviation
    "check_nat_subs \<equiv> \<forall> (_, d) \<in> clkp_set'. d \<ge> 0"

  lemma check_nat_subs:
    "check_nat_subs \<longleftrightarrow> snd ` clkp_set' \<subseteq> \<nat>"
  unfolding Nats_def apply safe
  subgoal for _ _ b using rangeI[of int "nat b"] by auto
  by auto

  definition
    "check_resets \<equiv> \<forall> x c. Some (INSTR (STOREC c x)) \<in> set prog \<longrightarrow> x = 0"

  lemma check_resets_alt_def:
    "check_resets =
      (\<forall> (c, x) \<in> collect_store. x = 0)"
    unfolding check_resets_def collect_store_def by auto

  definition
    "check_pre \<equiv>
      length inv = p \<and> length trans = p \<and> length pred = p
      \<and> (\<forall> i < p. length (pred ! i) = length (trans ! i) \<and> length (inv ! i) = length (trans ! i))
      \<and> (\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, l) \<in> set xs. l < length T)
      \<and> length k = m + 1 \<and> p > 0 \<and> m > 0
      \<and> (\<forall> i < p. trans ! i \<noteq> []) \<and> (\<forall> q < p. trans ! q ! 0 \<noteq> [])
      \<and> k ! 0 = 0 \<and> check_nat_subs \<and> clk_set' = {1..m}
      \<and> check_resets
      "

  definition
    "check_ceiling \<equiv> \<forall> (c, d) \<in> clkp_set'. k ! c \<ge> d"

  lemma finite_clkp_set'[intro, simp]:
    "finite clkp_set'"
    unfolding clkp_set'_def
    using [[simproc add: finite_Collect]]
    by (auto intro!: finite_vimageI finite_imageI simp: inj_on_def)

  lemma check_axioms:
    "UPPAAL_Reachability_Problem_precompiled p m k inv pred trans prog
    \<longleftrightarrow> check_pre \<and> check_ceiling"
    unfolding
      UPPAAL_Reachability_Problem_precompiled_def
      check_ceiling_def check_pre_def check_nat_subs check_resets_def
    by auto

end

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.collect_cexp_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.collect_store_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.check_resets_alt_def

export_code UPPAAL_Reachability_Problem_precompiled_defs.collect_cexp in SML module_name Test

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.check_axioms
  UPPAAL_Reachability_Problem_precompiled_defs.clkp_set'_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.clk_set'_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.check_pre_def
  UPPAAL_Reachability_Problem_precompiled_defs.check_ceiling_def
  UPPAAL_Reachability_Problem_precompiled_defs.init_def

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs'.trans_out_map_def
  UPPAAL_Reachability_Problem_precompiled_defs'.trans_in_map_def
  UPPAAL_Reachability_Problem_precompiled_defs'.trans_i_map_def
  UPPAAL_Reachability_Problem_precompiled_defs'.all_actions_by_state_def
  UPPAAL_Reachability_Problem_precompiled_defs'.actions_by_state_def
  UPPAAL_Reachability_Problem_precompiled_defs'.pairs_by_action_def

code_pred clock_val_a .

concrete_definition reachability_checker_impl
  uses UPPAAL_Reachability_Problem_precompiled'.reachability_checker_alt_def

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs'.make_cconstr_def
  UPPAAL_Reachability_Problem_precompiled_defs'.make_reset_def
  UPPAAL_Reachability_Problem_precompiled_defs'.check_pred_def
  UPPAAL_Reachability_Problem_precompiled_defs'.check_g_def
  UPPAAL_Reachability_Problem_precompiled_defs'.runf_def
  UPPAAL_Reachability_Problem_precompiled_defs'.runt_def
  UPPAAL_Reachability_Problem_precompiled_defs.PROG_def

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.P_def

lemma exec_code[code]:
  "exec prog n (pc, st, m, f, rs) pcs =
  (case n of 0 \<Rightarrow> None
   | Suc n \<Rightarrow>
    (case prog pc of None \<Rightarrow> None
     | Some instr \<Rightarrow>
         if instr = HALT
         then Some ((pc, st, m, f, rs), pc # pcs)
         else case UPPAAL_Asm.step instr
                    (pc, st, m, f, rs) of
              None \<Rightarrow> None
              | Some s \<Rightarrow> exec prog n s (pc # pcs)))"
  by (cases n) auto

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled'_axioms_def
  UPPAAL_Reachability_Problem_precompiled'_def
  pred_act_def

definition
  "init_pred_check \<equiv> \<lambda> p prog max_steps pred s\<^sub>0.
    (\<forall> q < p.
       case (exec
        (stripfp (UPPAAL_Reachability_Problem_precompiled_defs.PROG prog))
          max_steps
          ((pred ! q ! (UPPAAL_Reachability_Problem_precompiled_defs.init p ! q)), [], s\<^sub>0, True, [])
          [])
      of Some ((pc, st, s', True, rs), pcs) \<Rightarrow> True | _ \<Rightarrow> False)
  "

definition
  "time_indep_check1 \<equiv> \<lambda> pred prog max_steps.
   (\<forall>x\<in>set pred. \<forall>pc\<in>set x. time_indep_check prog pc max_steps)
  "

definition
  "time_indep_check2 \<equiv> \<lambda> trans prog max_steps.
  (\<forall>T\<in>set trans. \<forall>xs\<in>set T. \<forall>(_, _, pc_u, _)\<in>set xs. time_indep_check prog pc_u max_steps)
  "

definition
  "conjunction_check2 \<equiv> \<lambda> trans prog max_steps.
  (\<forall>T\<in>set trans. \<forall>xs\<in>set T. \<forall>(pc_g, _, _, _)\<in>set xs. conjunction_check prog pc_g max_steps)
  "

lemma start_pred[code]:
  "UPPAAL_Reachability_Problem_precompiled_start_state_axioms = (\<lambda> p max_steps trans prog bounds pred s\<^sub>0.
    init_pred_check p prog max_steps pred s\<^sub>0
  \<and> bounded bounds s\<^sub>0
  \<and> time_indep_check1 pred prog max_steps
  \<and> time_indep_check2 trans prog max_steps
  \<and> conjunction_check2 trans prog max_steps
  )"
  unfolding UPPAAL_Reachability_Problem_precompiled_start_state_axioms_def
  unfolding init_pred_check_def bounded_def time_indep_check1_def time_indep_check2_def
    conjunction_check2_def
  apply (rule ext)+
  apply safe
   apply (fastforce split: option.split_asm bool.split_asm)
  subgoal premises prems
    using prems(1,7) by (fastforce split: option.split_asm bool.split_asm)
  done

export_code UPPAAL_Reachability_Problem_precompiled_start_state_axioms

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.PROG_def
  UPPAAL_Reachability_Problem_precompiled_defs.init_def
  UPPAAL_Reachability_Problem_precompiled_start_state_def
  (*
  UPPAAL_Reachability_Problem_precompiled''_def
  UPPAAL_Reachability_Problem_precompiled''_axioms_def
  *)
  UPPAAL_Reachability_Problem_precompiled_defs.N_def

lemmas [code] =
  Equiv_TA_Defs.state_ta_def Prod_TA_Defs.N_s_def Product_TA_Defs.states_def

export_code UPPAAL_Reachability_Problem_precompiled'_axioms in SML module_name Test

export_code UPPAAL_Reachability_Problem_precompiled' in SML module_name Test

export_code reachability_checker_impl in SML_imp module_name TA

thm reachability_checker_impl_def reachability_checker_impl.refine

hide_const check_and_verify

definition [code]:
  "check_and_verify p m k max_steps I T prog final bounds P s\<^sub>0 na \<equiv>
    if UPPAAL_Reachability_Problem_precompiled' p m k max_steps I T prog bounds P s\<^sub>0 na
    then
      reachability_checker_impl p m k max_steps I T prog bounds P s\<^sub>0 na final
      \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] =
  UPPAAL_Reachability_Problem_precompiled'.reachability_checker_hoare

abbreviation "N \<equiv> UPPAAL_Reachability_Problem_precompiled_defs.N"

theorem reachability_check:
  "(uncurry0 (check_and_verify p m k max_steps I T prog formula bounds P s\<^sub>0 na),
    uncurry0 (
       Refine_Basic.RETURN (
        if UPPAAL_Reachability_Problem_precompiled' p m k max_steps I T prog bounds P s\<^sub>0 na
        then Some (
          \<exists> L' s' u u'.
            conv (N p I P T prog bounds) \<turnstile>\<^sub>max_steps
              \<langle>repeat 0 p, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
            \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s'
          )
        else None
       )
    )
   )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  apply sepref_to_hoare
   apply (sep_auto simp: reachability_checker_impl.refine[symmetric] check_and_verify_def)
  by (sep_auto simp:
      check_and_verify_def UPPAAL_Reachability_Problem_precompiled_defs.init_def
     )+

export_code open
  check_and_verify init_pred_check time_indep_check1 time_indep_check1 conjunction_check2
  checking SML_imp

end (* End of theory *)