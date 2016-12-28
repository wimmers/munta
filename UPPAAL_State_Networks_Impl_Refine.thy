theory UPPAAL_State_Networks_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl_Refine UPPAAL_State_Networks_Impl Networks_Impl_Refine
    "~/Isabelle/Util/ML_Util"
begin

context Prod_TA
begin

  thm inv_of_product
  end

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

term "trans_of A"
term trans

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

context UPPAAL_Reachability_Problem_precompiled_defs
begin
  lemma state_set_T':
    "L \<in> state_set product.T'" if "(L, s) \<in> state_set (trans_of A)"
    using that
    unfolding
      trans_of_def product.prod_ta_def product.prod_trans_def
      product.prod_trans_i_def product.prod_trans_s_def state_set_def
    by safe force+ (* XXX Slow *)

  lemma state_set_states:
      "fst ` state_set (trans_of A) \<subseteq> Product_TA_Defs.states (fst N)"
      apply (rule subset_trans[rotated])
       apply (rule Product_TA_Defs.state_set_states)
      unfolding state_set_def[symmetric]
      apply safe
      using state_set_T' unfolding state_set_def by simp
end

lemma (in UPPAAL_Reachability_Problem_precompiled) state_set_pred:
  "(\<forall>i<p. (pred ! i ! (L ! i)) s)" if "(L, s) \<in> state_set (trans_of A)" for s
  using that process_length(3)
  unfolding
    trans_of_def state_set_def N_def P_def
    Prod_TA_Defs.prod_ta_def Prod_TA_Defs.p_def
    Prod_TA_Defs.prod_trans_def Prod_TA_Defs.prod_trans_i_def Prod_TA_Defs.prod_trans_s_def
  by auto

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

locale UPPAAL_Reachability_Problem_precompiled' =
  UPPAAL_Reachability_Problem_precompiled_start_state +
  UPPAAL_Reachability_Problem_precompiled_defs' +
  assumes action_set:
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, a, _) \<in> set xs. pred_act (\<lambda> a. a < na) a"
begin

  thm equiv.defs.prod_trans_i_alt_def

  sublocale Reachability_Problem_Impl_Defs A "(init, s\<^sub>0)" "PR_CONST (\<lambda> (l, s). F l)" m
    by standard

  term A term N term "Product_TA_Defs.states (fst N)" term "state_set (trans_of A)"

  term P

  (*
  definition
    "states' =
    {(L, s). L \<in> equiv.defs.states' s \<and>
      (\<forall> q < p.
        case runf (pred ! q ! (L ! q)) s of
          Some ((_, _, _, True, _), _) \<Rightarrow> True
        | _ \<Rightarrow> False)}"
*)

  definition
    "states' = {(L, s). L \<in> equiv.defs.states' s \<and> check_pred L s}"

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

lemma equiv_states'_alt_def:
  "equiv.defs.states' s =
    {L. length L = p \<and>
      (\<forall> q < p. L ! q \<in> fst ` fst (equiv.N ! q)
              \<or> L ! q \<in> (snd o snd o snd o snd) ` fst (equiv.N ! q))}"
  unfolding Product_TA_Defs.states_def
  unfolding equiv.defs.N_s_def trans_of_def
  by (simp add: T_s_unfold_1 T_s_unfold_2)

lemma
  "length L = q" if "L \<in> equiv.defs.states' s" for L
  using that
  unfolding Product_TA_Defs.states_def
    apply simp
  unfolding equiv.defs.N_s_def trans_of_def
  apply simp
  unfolding equiv.defs.T_s_def
  apply simp
  unfolding Equiv_TA_Defs.state_ta_def Equiv_TA_Defs.state_trans_t_def
  apply simp
  apply clarify
    oops

  lemma state_set_states:
    "state_set (trans_of A) \<subseteq> states'"
    using state_set_states state_set_pred unfolding states'_def by auto

  lemma T_T:
    "product.T = map T [0..<p]"
    unfolding T_def trans_of_def N_def by auto

  lemma states_length_p:
    assumes "l \<in> product.states"
    shows "length l = p"
      using assms length_N product.states_length by simp

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

  thm pairs_by_action_def

  (* XXX Scratch *)
  lemma
    "card (C :: 'a1 set) \<le> card (B :: 'a2 set)" if "inj_on f C" "finite C" "finite B" for f :: "('a1 \<Rightarrow> 'a2)"
      using that oops

      thm pairs_by_action_def

  lemma in_pairs_by_actionI:
    assumes
      "pa \<noteq> q"
      "(pa, g1, a, m1, l1') \<in> set ys"
      "(q, g2, a, m2, l2') \<in> set xs"
      "\<forall> q' < p. (P ! q') (L[pa := l1', q := l2'] ! q') (m1 (m2 s))"
    shows "(g1 @ g2, a, r1 @ r2, L[pa := l1', q := l2'], m1 (m2 s)) \<in> set (pairs_by_action (L, s) xs ys)"
    using assms
    unfolding pairs_by_action_def
    apply clarsimp
    apply (rule bexI[rotated], assumption)
    apply (simp add: set_map_filter)
    by blast

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

  lemma states'_states'[intro]:
    "L \<in> equiv.defs.states' s" if "(L, s) \<in> states'"
    using that unfolding states'_def by auto

  lemma states_states[intro]:
    "L \<in> product.states" if "(L, s) \<in> states'"
    using that unfolding states'_def by simp

  term "\<forall>q<p. (equiv.defs.P ! q) (L ! q) s" term "P ! q"
    term "check_pred L s"

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

  lemma [simp]:
    "equiv.PF = PF"
    unfolding striptp_def N_def by simp

  lemma [simp]:
    "equiv.P = PROG"
    unfolding N_def by simp

  lemma I_simp[simp]:
    "(equiv.I ! q) l = pred ! q ! l" if "q < p"
    unfolding N_def P_def using \<open>q < p\<close> process_length(3) by simp

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

locale UPPAAL_Reachability_Problem_precompiled'' =
  UPPAAL_Reachability_Problem_precompiled' +
  assumes bounded: "bounded bounds s\<^sub>0"
begin

  lemma init_states:
    "init \<in> equiv.defs.states' s\<^sub>0"
    using processes_have_trans start_has_trans
    unfolding equiv_states'_alt_def
    unfolding init_def N_def T_def by force

  lemma start_pred':
    "(\<forall> i < p. (pred ! i ! (init ! i)) s\<^sub>0)"
    using start_pred unfolding init_def by auto

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

  lemma I_I:
    "product.I = map I [0..<p]"
    unfolding I_def inv_of_def N_def by auto

  lemma states_states':
    "states \<subseteq> states'"
    using state_set_states start_states' by auto

lemma [simp]:
  "length L = p" if "(L, s) \<in> states'"
  using that  unfolding states'_def by auto

lemma
  "product'.defs.I' s L \<equiv> conv_cc (concat (map (\<lambda> q. I q (L ! q)) [0..<p]))"
  using [[show_abbrevs = false]]
  unfolding Product_TA_Defs.product_ta_def inv_of_def Product_TA_Defs.product_invariant_def
  apply simp
    using [[show_abbrevs]]
    using product'.prod.inv_of_product
      apply (simp add: Prod_TA_Defs.N_s_length Prod_TA_Defs.p_def)
  unfolding I' oops

term "product'.defs.I'" term I

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

  definition "final_fun \<equiv> \<lambda> (L, s). list_ex (\<lambda> i. List.member (final ! i) (L ! i)) [0..<p]"

  term list_ex term List.member

  term local.F

  lemma final_fun_final':
    "(final_fun, (\<lambda> (l, s). F l)) \<in> inv_rel states'"
    unfolding F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
     by (force dest!: states'_states')

  lemma final_fun_final[intro, simp]:
    "(final_fun, (\<lambda> (l, s). F l)) \<in> inv_rel states"
    using final_fun_final' states_states' by (rule inv_rel_mono)

  lemma fst_clkp_setD:
    assumes "(c, d) \<in> clkp_set A"
    shows "c > 0" "c \<le> m" "d \<in> range int"
    using assms clock_set consts_nats clkp_set'_subs unfolding Nats_def clk_set'_def by force+

  (*
  lemma fst_clkp_set'D:
    assumes "(c, d) \<in> clkp_set'"
    shows "c > 0" "c \<le> m" "d \<in> range int"
    using assms clock_set consts_nats clkp_set'_subs unfolding Nats_def clk_set'_def apply auto
     apply force
*)


  lemma k_ceiling':
    "\<forall>c\<in>{1..m}. k ! c = nat (Max ({d. (c, d) \<in> clkp_set'} \<union> {0}))"
    using k_ceiling oops (* XXX *)

  lemma
    "\<forall>i<Suc m. k ! i = k_fun i"
    unfolding k_fun_def by simp

  lemma k_k'[intro]:
    "map int k = k'"
    apply (rule nth_equalityI)
     using k_length length_k' apply (auto; fail)
     unfolding k'_def apply (simp add: k_length del: upt_Suc)
     unfolding k_fun_def by simp

       term k'

  lemma iarray_k'[intro]:
    "(uncurry0 (return (IArray (map int k))), uncurry0 (Refine_Basic.RETURN k')) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
    unfolding br_def by sepref_to_hoare sep_auto

  lemma init_has_trans:
    "(init, s\<^sub>0) \<in> fst ` (trans_of A) \<longleftrightarrow> trans_fun (init, s\<^sub>0) \<noteq> []"
    apply standard
    using trans_fun_trans_of unfolding transition_rel_def apply force
    using trans_fun_trans_of' start_states' unfolding transition_rel_def by fast

  lemma
    assumes "(init, s\<^sub>0) \<in> fst ` (trans_of A)"
      shows "(init, s\<^sub>0) \<in> state_set (trans_of A)"
  using assms oops

end (* End of locale assuming specific format for actions *)

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

context UPPAAL_Reachability_Problem_precompiled''
begin

  sublocale impl:
    Reachability_Problem_Impl
      trans_fun inv_fun final_fun "IArray (map int k)" A "(init, s\<^sub>0)"
      "PR_CONST ((\<lambda> (l, s). F l))" m k_fun
    unfolding PR_CONST_def by (standard; rule)

  thm states_states'

  (* XXX Unused *)
  lemma length_reachable:
  "length L' = p" if "E\<^sup>*\<^sup>* a\<^sub>0 ((L', s), u)"
    using states_states' impl.reachable_states[unfolded reachable_def, OF that]
    unfolding reachable_def by (force simp: init_def)

  lemma length_steps:
  "length L' = p" if "conv_A A \<turnstile> \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>" "\<forall>c\<in>{1..m}. u c = 0"
    using that reachable_decides_emptiness'[of "(L', s')"] by (auto intro: length_reachable)

  term F_reachable

  lemma F_reachable_correct':
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv_A A \<turnstile> \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < length L'. L' ! i \<in> set (final ! i))
      )"
    unfolding F_reachable_def reachable_def using reachability_check unfolding F_def by auto

  lemma F_reachable_correct'':
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv_A A \<turnstile> \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i))
      )"
    unfolding F_reachable_correct' using length_steps by metis

end

context Equiv_TA_Defs
begin

term defs.p

lemma p_p:
  "defs.p = p"
  by simp

end

thm Equiv_TA_Defs.p_p

lemma p_p:
  "Prod_TA_Defs.p (Equiv_TA_Defs.state_ta N max_steps) = Equiv_TA_Defs.p N"
  unfolding Prod_TA_Defs.p_def equiv.p_def oops
    thm p_p

      context UPPAAL_Reachability_Problem_precompiled''
  begin

   lemma product_invariant_conv:
    "product'.product_invariant = conv_cc o product.defs.product_invariant"
    unfolding product'.product_invariant_def product.product_invariant_def
    apply clarsimp
    apply (rule ext)
    apply (simp add: map_concat)
    apply(tactic \<open>Cong_Tac.cong_tac @{context} @{thm cong} 1\<close>)
     apply simp
    by (simp add: inv_of_def split: prod.split)

  lemma product_invariant_conv:
    "product'.product_invariant = conv_cc o product.product_invariant"
    unfolding product'.product_invariant_def product.product_invariant_def
    apply clarsimp
    apply (rule ext)
    apply (simp add: map_concat)
    apply(tactic \<open>Cong_Tac.cong_tac @{context} @{thm cong} 1\<close>)
     apply simp
    by (simp add: inv_of_def split: prod.split)

  lemma prod_invariant_conv:
    "product'.prod_invariant = conv_cc o product.prod_invariant"
    unfolding product'.prod_invariant_def product.prod_invariant_def product_invariant_conv by auto

  lemma product_trans_i_conv:
    "product'.product_trans_i = conv_t ` product.product_trans_i"
    unfolding product'.product_trans_i_def product.product_trans_i_def
    by (simp; force simp add: T_T states_length_p trans_of_def image_Collect N_def)

  lemma p_p[simp]:
    "product'.p = p"
    unfolding product'.p_def by simp

  lemma prod_trans_i_conv:
    "product'.prod_trans_i = conv_t ` product.prod_trans_i"
    unfolding
      product'.prod_trans_i_alt_def product.prod_trans_i_alt_def product_trans_i_conv
      p_p P_P
    apply (simp add: image_Collect)
    apply (rule Collect_cong)
    apply safe
     apply metis
    by ((rule exI)+; force)
  term "product'.defs.states'"

lemma T_s_unfold_1':
  "fst ` product'.defs.T_s q s = fst ` fst (product'.N ! q)" if "q < p"
  using \<open>q < p\<close>
  unfolding product'.defs.T_s_def
  unfolding product'.state_ta_def
  unfolding product'.state_trans_t_def p_p
  by force

lemma T_s_unfold_2':
  "(snd o snd o snd o snd) ` product'.defs.T_s q s = (snd o snd o snd o snd) ` fst (product'.N ! q)"
  if "q < p"
  using \<open>q < p\<close>
  unfolding product'.defs.T_s_def
  unfolding product'.state_ta_def
  unfolding product'.state_trans_t_def p_p
  by force

lemma product_states'_alt_def:
  "product'.defs.states' s =
    {L. length L = p \<and>
      (\<forall> q < p. L ! q \<in> fst ` fst (product'.N ! q)
              \<or> L ! q \<in> (snd o snd o snd o snd) ` fst (product'.N ! q))}"
  unfolding Product_TA_Defs.states_def
  unfolding product'.defs.N_s_def trans_of_def
  unfolding product'.defs.p_def[symmetric] product'.p_p p_p
  using T_s_unfold_1' T_s_unfold_2'
  by force

lemma states'_conv[simp]:
  "product'.defs.states' s = equiv.defs.states' s"
  unfolding product_states'_alt_def equiv_states'_alt_def
  unfolding N_def T_def by simp

lemma p_p_2[simp]:
  "product'.defs.p = p"
  unfolding product'.p_p p_p ..

lemma len_product'_N[simp]:
  "length product'.defs.N = p"
  unfolding product'.defs.p_def[symmetric] by (rule p_p_2)

lemma len_equiv_N:
  "length equiv.defs.N = p"
  unfolding equiv.defs.p_def[symmetric] by simp
term "equiv.state_trans q"

term "(\<lambda> (a, b, c). (a, \<lambda> x. conv_cc (b x), c)) ` equiv.state_trans q"

  term "Equiv_TA_Defs.state_trans_t (conv N)" term "(conv N)"
  term "equiv.make_g"

lemma PF_PF:
  "product'.PF = equiv.PF"
  apply simp
  unfolding stripfp_def
  apply (rule ext)
  apply clarsimp
  subgoal for x
    apply (cases "PROG x")
     apply simp
    subgoal for a
      by (cases a) auto
    done
  done

lemma PT_PT:
  "product'.PT = equiv.PT"
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

lemma
  "product'.p = p"
  unfolding product'.p_def by simp

lemma P_P[simp]:
  "product'.defs.P = equiv.defs.P"
  unfolding Equiv_TA_Defs.state_ta_def
  unfolding Equiv_TA_Defs.p_def
  unfolding Equiv_TA_Defs.state_pred_def
  using PF_PF by (auto split: option.split)

lemma map_map_filter:
  "map f (List.map_filter g xs) = List.map_filter (map_option f o g) xs"
  by (induction xs; simp add: List.map_filter_simps split: option.split)


lemma make_g_conv:
  "product'.make_g = conv_cc oo equiv.make_g"
  unfolding Equiv_TA_Defs.make_g_def PT_PT PF_PF apply simp
  apply (rule ext)
  apply (rule ext)
  apply simp
  apply (auto split: option.splits simp: map_map_filter)
  apply (rule arg_cong2[where f = List.map_filter])
  by (auto split: option.split instrc.split)

lemma make_c_conv:
  "product'.make_c = equiv.make_c"
  unfolding Equiv_TA_Defs.make_c_def PT_PT by simp

lemma make_f_conv:
  "product'.make_f = equiv.make_f"
  unfolding Equiv_TA_Defs.make_f_def PF_PF by simp

lemma make_mf_conv:
  "product'.make_mf = equiv.make_mf"
  unfolding Equiv_TA_Defs.make_mf_def PF_PF by simp

lemmas make_convs = make_g_conv make_c_conv make_f_conv make_mf_conv

lemma state_trans_conv:
  "Equiv_TA_Defs.state_trans_t (conv N) max_steps q
  = (\<lambda> (a, b, c). (a, \<lambda> x. conv_cc (b x), c)) ` equiv.state_trans q" if \<open>q < p\<close>
  unfolding Equiv_TA_Defs.state_trans_t_def image_Collect
  using \<open>q < _\<close> make_convs by (force split: prod.splits)+

lemma map_conv_t:
  "map trans_of (product'.defs.N_s s) ! q = conv_t ` (map trans_of (equiv.defs.N_s s) ! q)"
  if \<open>q < p\<close>
  using \<open>q < p\<close>
  apply (subst nth_map)
  unfolding product'.defs.N_s_length p_p_2
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

lemma equiv_p_p: "equiv.p = p"
  by simp


  lemma product_trans_t_conv:
    "Product_TA_Defs.product_trans_s (product'.defs.N_s s)
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
    "Product_TA_Defs.product_trans_i (product'.defs.N_s s)
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
    "product'.defs.prod_trans_s = conv_t ` equiv.defs.prod_trans_s"
    unfolding product'.defs.prod_trans_s_alt_def
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
    "product'.defs.prod_trans_i = conv_t ` equiv.defs.prod_trans_i"
    unfolding product'.defs.prod_trans_i_alt_def
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
    "product'.defs.prod_trans = conv_t ` equiv.defs.prod_trans"
    unfolding product'.defs.prod_trans_def
    unfolding equiv.defs.prod_trans_def
    unfolding prod_trans_s_conv
    unfolding prod_trans_i_conv image_Un ..

lemma prod_invariant_conv:
  "product'.defs.prod_invariant = (map conv_ac \<circ>\<circ> Prod_TA_Defs.prod_invariant) EA"
  apply (rule ext)
  apply safe
  unfolding product'.defs.prod_invariant_def equiv.defs.prod_invariant_def
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

  lemma prod_conv: "product'.defs.prod_ta = conv_A A"
    unfolding product'.defs.prod_ta_def
    unfolding equiv.defs.prod_ta_def
    by (simp add: prod_invariant_conv[symmetric] prod_trans_conv[symmetric])

  thm F_reachable_correct'' product'.prod_correct[symmetric] prod_conv

  term "Equiv_TA (conv N) max_steps init s\<^sub>0" term "(conv N) \<turnstile>\<^sub>n \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>"
  typ "('a, 't :: time, 's) unta" term "conv N"
    lemma F_reachable_correct:
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i))
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
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i)))
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using impl.hnr_F_reachable unfolding reachability_checker_def F_reachable_correct .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> L' s' u u'.
        conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i)))
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

thm trans_s_fun_def

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

(* XXX Move *)
lemma bex_n_simp:
  "(\<exists> x \<in> set [0..<n]. P x) \<longleftrightarrow> (\<exists> x < n. P x)"
  by auto

(* XXX Move *)
lemma ball_n_simp:
  "(\<forall> x \<in> set [0..<n]. P x) \<longleftrightarrow> (\<forall> x < n. P x)"
  by auto

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

term
  "length inv = p \<and> length trans = p \<and> length pred = p
      \<and> (\<forall> i < p. length (pred ! i) = length (trans ! i) \<and> length (inv ! i) = length (trans ! i))
      \<and> (\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, l) \<in> set xs. l < length T)
      \<and> length k = m + 1 \<and> p > 0 \<and> m > 0
      \<and> (\<forall> i < p. trans ! i \<noteq> []) \<and> (\<forall> q < p. trans ! q ! 0 \<noteq> [])
      \<and> k ! 0 = 0 \<and> check_nat_subs \<and> clk_set' = {1..m}"

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

(*
lemmas [code] =
  State_Network_Reachability_Problem_precompiled_int_vars_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.pred'_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.trans'_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.checkb_def
  State_Network_Reachability_Problem_precompiled_int_vars_axioms_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.s\<^sub>0_def
*)

code_pred clock_val_a .

(* export_code State_Network_Reachability_Problem_precompiled_int_vars in SML module_name Test *)

concrete_definition reachability_checker_impl
  uses UPPAAL_Reachability_Problem_precompiled''.reachability_checker_alt_def

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

  thm UPPAAL_Reachability_Problem_precompiled_start_state_axioms_def

lemma start_pred[code]:
    "UPPAAL_Reachability_Problem_precompiled_start_state_axioms = (\<lambda> p max_steps prog pred s\<^sub>0.
  (\<forall> q < p.
       case (exec
        (stripfp (UPPAAL_Reachability_Problem_precompiled_defs.PROG prog))
          max_steps
          ((pred ! q ! (UPPAAL_Reachability_Problem_precompiled_defs.init p ! q)), [], s\<^sub>0, True, [])
          [])
      of Some ((pc, st, s', True, rs), pcs) \<Rightarrow> True | _ \<Rightarrow> False))"
  unfolding UPPAAL_Reachability_Problem_precompiled_start_state_axioms_def
  by (rule ext)+ (fastforce split: option.splits bool.split_asm)+

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.PROG_def
  UPPAAL_Reachability_Problem_precompiled_defs.init_def
  UPPAAL_Reachability_Problem_precompiled_start_state_def
  UPPAAL_Reachability_Problem_precompiled''_def
  UPPAAL_Reachability_Problem_precompiled''_axioms_def
  UPPAAL_Reachability_Problem_precompiled_defs.N_def

lemmas [code] =
  Equiv_TA_Defs.state_ta_def Prod_TA_Defs.N_s_def Product_TA_Defs.states_def

export_code UPPAAL_Reachability_Problem_precompiled''_axioms in SML module_name Test

export_code UPPAAL_Reachability_Problem_precompiled'' in SML module_name Test

export_code reachability_checker_impl in SML_imp module_name TA

thm reachability_checker_impl_def reachability_checker_impl.refine

hide_const check_and_verify

definition [code]:
  "check_and_verify p m k max_steps I T prog final bounds P s\<^sub>0 na \<equiv>
    if UPPAAL_Reachability_Problem_precompiled'' p m k max_steps I T prog bounds P s\<^sub>0 na
    then
      reachability_checker_impl p m k max_steps I T prog bounds P s\<^sub>0 na final
      \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] =
  UPPAAL_Reachability_Problem_precompiled''.reachability_checker_hoare

term UPPAAL_Reachability_Problem_precompiled_defs.N

  abbreviation "N \<equiv> UPPAAL_Reachability_Problem_precompiled_defs.N"

  (*
abbreviation "N p I P T prog bounds max_steps \<equiv>
  UPPAAL_Reachability_Problem_precompiled_defs.N p I
    (UPPAAL_Reachability_Problem_precompiled_defs.pred' P r bounds)
    (State_Network_Reachability_Problem_precompiled_int_vars_defs.trans' T)"
*)

  term "conv (N p I P T prog bounds) \<turnstile>\<^sub>max_steps
              \<langle>repeat 0 p, repeat 0 r, u\<rangle> \<rightarrow>* \<langle>l', s', u'\<rangle>"

theorem reachability_check:
  "(uncurry0 (check_and_verify p m k max_steps I T prog final bounds P s\<^sub>0 na),
    uncurry0 (
       Refine_Basic.RETURN (
        if UPPAAL_Reachability_Problem_precompiled'' p m k max_steps I T prog bounds P s\<^sub>0 na
        then Some (
          \<exists> l' s' u u'.
            conv (N p I P T prog bounds) \<turnstile>\<^sub>max_steps
              \<langle>repeat 0 p, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', s', u'\<rangle>
            \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> q < p. l' ! q \<in> set (final ! q))
          )
        else None
       )
    )
   )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  apply sepref_to_hoare
   apply  (sep_auto simp: reachability_checker_impl.refine[symmetric] check_and_verify_def)
  by (sep_auto simp:
      check_and_verify_def UPPAAL_Reachability_Problem_precompiled_defs.init_def
     )+

export_code open check_and_verify checking SML_imp

end (* End of theory *)