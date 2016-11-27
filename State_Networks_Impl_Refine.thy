theory State_Networks_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl_Refine State_Networks_Impl Networks_Impl_Refine
    "~/Isabelle/Util/ML_Util"
begin

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

locale State_Network_Reachability_Problem_precompiled_defs' =
  State_Network_Reachability_Problem_precompiled_defs +
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
        (\<lambda> (g, p, a, r, m, l'). case a of Sil a \<Rightarrow> Some (g, p, a, r, m, l') | _ \<Rightarrow> None)
      )) trans"

  definition
    "trans_in_map \<equiv>
      map (map (map
        (\<lambda> (g, p, a, r, m, l'). case a of In a \<Rightarrow> (g, p, a, r, m, l')) o filter (\<lambda> (g, p, a, r, m, l').
          case a of In a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  definition
    "trans_out_map \<equiv>
      map (map (map
        (\<lambda> (g, p, a, r, m, l'). case a of Out a \<Rightarrow> (g, p, a, r, m, l')) o filter (\<lambda> (g, p, a, r, m, l').
          case a of Out a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  abbreviation
    "nested_list_to_iarray xs \<equiv> IArray (map IArray xs)"

  (* XXX Optimize by using a better data structure? *)
  definition
    "actions_by_state i \<equiv> fold (\<lambda> t acc. acc[fst (snd (snd t)) := (i, t) # (acc ! fst (snd (snd t)))])"

  definition
    "all_actions_by_state t L \<equiv>
      fold (\<lambda> i. actions_by_state i (t !! i !! (L ! i))) [0..<p] (repeat [] na)"

  definition
    "pairs_by_action \<equiv> \<lambda> (L, s) OUT. concat o
      map (\<lambda> (i, g1, p1, a, r1, m1, l1). List.map_filter
      (\<lambda> (j, g2, p2, a, r2, m2, l2).
        if i \<noteq> j \<and> p1 s \<and> p2 s \<and> (\<forall> q < p. (P ! q) (L[i := l1, j := l2] ! q) (m1 (m2 s)))
        then Some (g1 @ g2, a, r1 @ r2, (L[i := l1, j := l2], m1 (m2 s)))
        else None)
      OUT)"

  definition
    "trans_s_fun \<equiv> \<lambda> (L, s).
      let
        In = all_actions_by_state (nested_list_to_iarray trans_in_map) L;
        Out = all_actions_by_state (nested_list_to_iarray trans_out_map) L
      in
        concat (map (\<lambda> a. pairs_by_action (L, s) (Out ! a) (In ! a)) [0..<na])
    "

  definition
    "trans_i_from \<equiv> \<lambda> (L, s) i.
    List.map_filter (\<lambda> (g, c, a, r, m, l').
      if c s \<and> (\<forall> q < p. (P ! q) (L[i := l'] ! q) (m s))
      then Some (g, a, r, (L[i := l'], m s)) else None)
      ((IArray (map IArray trans_i_map)) !! i !! (L ! i))"

  definition
    "trans_i_fun L \<equiv> concat (map (trans_i_from L) [0..<p])"

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

context State_Network_Reachability_Problem_precompiled_defs
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

lemma (in State_Network_Reachability_Problem_precompiled) state_set_pred:
  "(\<forall>i<p. (pred ! i ! (L ! i)) s)" if "(L, s) \<in> state_set (trans_of A)"
  using that process_length(3)
  unfolding
    trans_of_def state_set_def N_def P_def
    Prod_TA_Defs.prod_ta_def Prod_TA_Defs.p_def
    Prod_TA_Defs.prod_trans_def Prod_TA_Defs.prod_trans_i_def Prod_TA_Defs.prod_trans_s_def
  by auto

context Prod_TA_Defs
begin

  lemma prod_trans_i_alt_def:
    "prod_trans_i =
      {((L, s), g, a, r, (L', m s)) | L s g c a r m L'.
       (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) (m s))
       \<and> (L, g, (a, Act (c, m)), r, L') \<in> product_trans_i \<and> c s}"
  unfolding
    prod_trans_i_def trans_of_def product_ta_def product_trans_i_def
    product_trans_s_def product_trans_def
  by simp

lemma prod_trans_s_alt_def:
  "prod_trans_s =
    {((L, s), g, a, r, (L', s')) | L s g ci co a r mi mo L' s'.
      ci s \<and> co s
      \<and> (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) s')
      \<and> (L, g, (a, Syn (ci, mi) (co, mo)), r, L') \<in> product_trans_s
      \<and> s' = mi (mo s)
    }"
  unfolding
    prod_trans_s_def trans_of_def product_ta_def product_trans_i_def
    product_trans_s_def product_trans_def
  by simp

end

locale State_Network_Reachability_Problem_precompiled' =
  State_Network_Reachability_Problem_precompiled_start_state +
  State_Network_Reachability_Problem_precompiled_defs' +
  assumes action_set:
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, a, _) \<in> set xs. pred_act (\<lambda> a. a < na) a"
begin

  sublocale Reachability_Problem_Impl_Defs A "(init, s\<^sub>0)" "PR_CONST (\<lambda> (l, s). F l)" m
    by standard

  term A term N term "Product_TA_Defs.states (fst N)" term "state_set (trans_of A)"

  definition
    "states' = {(L, s). L \<in> product.states \<and> (\<forall> i < p. (pred ! i ! (L ! i)) s)}"

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
      "(g1, c1, In a, r1) = trans ! q ! l ! i"
    shows "(g1, c1, a, r1) \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
    using assms process_length(2) unfolding trans_in_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, c1, In a, r1)"])

  lemma in_trans_out_mapI:
    assumes
      "q < p" "l < length (trans ! q)" "i < length (trans ! q ! l)"
      "(g1, c1, Out a, r1) = trans ! q ! l ! i"
    shows "(g1, c1, a, r1) \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
    using assms process_length(2) unfolding trans_out_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, c1, Out a, r1)"])

  lemma in_trans_in_mapD:
    assumes
      "(g1, c1, a, r1) \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
      "q < p" "l < length (trans ! q)"
    obtains i where
      "i < length (trans ! q ! l) \<and> trans ! q ! l ! i = (g1, c1, In a, r1)"
    using assms process_length(2) unfolding trans_in_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  (* XXX Remove duplication *)
  lemma in_trans_out_mapD:
    assumes
      "(g1, c1, a, r1) \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
      "q < p" "l < length (trans ! q)"
    obtains i where
      "i < length (trans ! q ! l) \<and> trans ! q ! l ! i = (g1, c1, Out a, r1)"
    using assms process_length(2) unfolding trans_out_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  lemma in_actions_by_stateI:
    assumes
      "(g1, p1, a, r1) \<in> set xs" "a < length acc"
    shows
      "(q, g1, p1, a, r1) \<in> set (actions_by_state q xs acc ! a)
      \<and> a < length (actions_by_state q xs acc)"
    using assms unfolding actions_by_state_def
    apply (induction xs arbitrary: acc)
     apply (simp; fail)
    apply simp
    apply (erule disjE)
     apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, p1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto

  lemma in_actions_by_state_preserv:
    assumes
      "(q, g1, p1, a, r1) \<in> set (acc ! a)" "a < length acc"
    shows
      "(q, g1, p1, a, r1) \<in> set (actions_by_state y xs acc ! a)
      \<and> a < length (actions_by_state y xs acc)"
    using assms unfolding actions_by_state_def
    apply -
    apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, p1, a, r1) \<in> set (acc ! a) \<and> a < length acc"]
        )
    apply (subst list_update_nth_split; auto)
    by auto

  lemma length_actions_by_state_preserv[simp]:
    shows "length (actions_by_state y xs acc) = length acc"
    unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

  lemma in_all_actions_by_stateI:
    assumes
      "a < na" "q < p" "L ! q < n" "(g1, p1, a, r1) \<in> set (M !! q !! (L ! q))"
    shows
      "(q, g1, p1, a, r1) \<in> set (all_actions_by_state M L ! a)"
    unfolding all_actions_by_state_def
    apply (rule fold_acc_ev_preserv
        [where P = "\<lambda> acc. (q, g1, p1, a, r1) \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
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
      by (cases "fst (snd (snd x)) = j"; simp)
    using assms by auto

  lemma actions_by_state_inj':
    assumes "j < length acc" "(q, a) \<notin> set (acc ! j)" "(q, a) \<in> set (actions_by_state i xs acc ! j)"
    shows "i = q"
    using actions_by_state_inj[OF assms(1)] assms(2-) by fast

  lemma in_actions_by_stateD:
    assumes
      "(q, g, p1, a, t) \<in> set (actions_by_state i xs acc ! j)" "(q, g, p1, a, t) \<notin> set (acc ! j)"
      "j < length acc"
    shows
      "(g, p1, a, t) \<in> set xs \<and> j = a"
    using assms unfolding actions_by_state_def
    apply -
    apply (drule fold_evD
        [where y = "(g, p1, a, t)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, _, a', t). a' = j"]
        )
         apply assumption
      (* XXX Define asm split rule *)
        apply (subst (asm) list_update_nth_split[of j]; force)
       apply simp+
     apply (subst (asm) list_update_nth_split[of j]; force)
    by auto
  thm fold_evD''

  lemma in_all_actions_by_stateD:
    assumes
      "(q, g1, p1, a, r1) \<in> set (all_actions_by_state M L ! a')" "a' < na"
    shows
      "(g1, p1, a, r1) \<in> set (M !! q !! (L ! q)) \<and> q < p \<and> a' = a"
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
      "(g1, p1, a, r1) = trans ! q ! l ! j"
      "l < length (trans ! q)"
      "j < length (trans ! q ! l)"
    shows "pred_act (\<lambda>a. a < na) a"
    using action_set assms process_length(2) by (force dest!: nth_mem)

  lemma in_actions_trans_in_mapI:
    assumes
      "pa < p"
      "(g1, p1, In a, r1) = trans ! pa ! (L ! pa) ! j"
      "L ! pa < length (trans ! pa)"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, p1, a, r1) \<in> set (all_actions_by_state (IArray (map IArray trans_in_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_in_mapI)+

  lemma in_actions_trans_out_mapI:
    assumes
      "pa < p"
      "(g1, p1, Out a, r1) = trans ! pa ! (L ! pa) ! j"
      "L ! pa < length (trans ! pa)"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, p1, a, r1) \<in> set (all_actions_by_state (IArray (map IArray trans_out_map)) L ! a)"
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
      "(pa, g1, p1, a, r1, m1, l1') \<in> set ys"
      "(q, g2, p2, a, r2, m2, l2') \<in> set xs"
      "p1 s" "p2 s"
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
      "\<forall> (q, g, p, a'', r, m, l) \<in> set xs. a'' = a'"
      "\<forall> (q, g, p, a'', r, m, l) \<in> set ys. a'' = a'"
    shows "\<forall> q' < p. (P ! q') (L' ! q') s'"
      using assms(1) unfolding pairs_by_action_def using assms(2,3)
      by (force split: if_split_asm simp: set_map_filter)

  lemma in_pairs_by_actionD1:
    assumes
      "(g, a, r, L', s') \<in> set (pairs_by_action (L, s) xs ys)"
      "\<forall> (q, g, p, a'', r, m, l) \<in> set xs. a'' = a'"
      "\<forall> (q, g, p, a'', r, m, l) \<in> set ys. a'' = a'"
    obtains pa q g1 g2 p1 p2 r1 r2 m1 m2 l1' l2' where
      "pa \<noteq> q"
      "(pa, g1, p1, a, r1, m1, l1') \<in> set ys"
      "(q, g2, p2, a, r2, m2, l2') \<in> set xs"
      "L' = L[pa := l1', q := l2']"
      "s' = m1 (m2 s)"
      "g = g1 @ g2" "r = r1 @ r2"
      "p1 s" "p2 s" (* XXX If we put these as the second and third goals, fastforce loops below *)
  proof -
    from assms(1) obtain pa q g1 g2 p1 p2 r1 r2 m1 m2 l1' l2' where
      "(q, g1, p1, a, r1, m1, l1') \<in> set ys" "(pa, g2, p2, a, r2, m2, l2') \<in> set xs" "q \<noteq> pa"
      "p1 s" "p2 s"
      "Some (g1 @ g2, a, r1 @ r2, L[q := l1', pa := l2'], m1 (m2 s)) = Some (g, a, r, L', s')"
    unfolding pairs_by_action_def using assms(2,3) by (force split: if_split_asm simp: set_map_filter)
    then show ?thesis by (fastforce intro: that)
  qed

  lemma in_pairs_by_actionD:
    assumes
      "(g, a, r, L', s') \<in> set (pairs_by_action (L, s) xs ys)"
      "\<forall> (q, g, p, a'', r, m, l) \<in> set xs. a'' = a'"
      "\<forall> (q, g, p, a'', r, m, l) \<in> set ys. a'' = a'"
    obtains pa q g1 g2 p1 p2 r1 r2 m1 m2 l1' l2' where
      "pa \<noteq> q"
      "(pa, g1, p1, a, r1, m1, l1') \<in> set ys"
      "(q, g2, p2, a, r2, m2, l2') \<in> set xs"
      "L' = L[pa := l1', q := l2']"
      "s' = m1 (m2 s)"
      "g = g1 @ g2" "r = r1 @ r2"
      "p1 s" "p2 s" (* XXX If we put these as the second and third goals, fastforce loops below *)
      "\<forall> q' < p. (P ! q') (L' ! q') s'"
    using in_pairs_by_actionD1[OF assms] in_pairs_by_actionD2[OF assms] by metis

  lemma in_trans_funD:
    assumes "y \<in> set (trans_fun L)"
    shows "y \<in> set (trans_s_fun L) \<or> y \<in> set (trans_i_fun L)"
      using assms unfolding trans_fun_def by auto

  lemma states_len[intro]:
    assumes
      "q < p" "L \<in> product.states"
    shows
      "L ! q < length (trans ! q)"
    using assms unfolding product.states_def
    unfolding T_T T_def make_trans_def apply simp
    apply (erule conjE)
    apply (drule bspec)
     apply simp
    apply (erule disjE)
     apply force
    unfolding process_length(2)[symmetric]
    using state_set
    by (clarsimp dest!: nth_mem; force)

  lemma states_states[intro]:
    "L \<in> product.states" if "(L, s) \<in> states'"
    using that unfolding states'_def by simp

  lemma P_unfold:
    "(\<forall>q<p. (P ! q) (L ! q) g) \<longleftrightarrow> (\<forall>q<p. (pred ! q ! (L ! q)) g)"
    unfolding P_def using process_length(3) by simp

  lemma trans_fun_trans_of':
    "(trans_fun, trans_of A) \<in> transition_rel states'"
    unfolding transition_rel_def T_def
    apply simp
    unfolding trans_of_def
    apply safe
    subgoal for L s g a r L' s'
      unfolding product.prod_ta_def product.prod_trans_def
      apply simp
      apply safe
      subgoal
        apply (rule trans_i_fun_trans_fun)
        unfolding product.prod_trans_i_alt_def product.product_trans_i_def
        apply safe
        unfolding T_T T_def states_length_p product.product_trans_def
          (* Could be a lemma from here *)
        unfolding trans_fun_def trans_i_fun_def trans_i_from_def trans_i_map_def make_trans_def
        apply clarsimp
        apply (rule bexI)
         prefer 2
         apply simp
        using process_length(2)
        apply simp
        apply (drule nth_mem)+
        subgoal premises prems for pa c m l' j
        proof -
          have "(g, c, Sil a, r, m, l') \<in> set (trans ! pa ! (L ! pa))"
            using prems by (auto split: prod.split_asm)
          with prems show ?thesis
            using [[simproc add: ex_reorder]]
            apply (simp add: set_map_filter)
            by (solve_ex_triv; fastforce intro!: exI)+
        qed
        done
      subgoal
        apply (rule trans_s_fun_trans_fun)
        unfolding product.prod_trans_s_alt_def product.product_trans_s_def
        apply safe
        unfolding T_T T_def states_length_p
        apply clarsimp
          (* Could be a lemma from here *)
        unfolding trans_s_fun_def
        apply clarsimp
        apply (subgoal_tac "a < na") (* XXX *)
        unfolding make_trans_def
        apply (rule bexI)
         prefer 2
        apply simp
         apply (fo_rule in_pairs_by_actionI, (force split: prod.split_asm intro!: in_actions_trans_in_mapI in_actions_trans_out_mapI)+; fail)
        apply (frule less_naI)
        by (auto split: prod.split_asm)
      done
    subgoal for L g a b r L'
      apply (drule in_trans_funD)
      apply (erule disjE)
      unfolding product.prod_ta_def product.prod_trans_def
       apply simp
       apply (rule disjI2)
      subgoal
        unfolding product.prod_trans_s_alt_def product.product_trans_s_def
        apply safe
        unfolding T_T T_def states_length_p
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
            apply simp
           apply blast
          apply (erule in_trans_out_mapD)
            apply blast
           apply blast
          apply (simp only: ex_simps[symmetric])
          unfolding states'_def
          subgoal
            apply (defer_existential, mini_existential)
            apply (defer_existential, mini_existential)
            apply mini_ex
            unfolding P_unfold
            apply simp
            apply defer_ex
            apply (mini_existential, simp)+
            apply (simp add: states_length_p)
            apply solve_ex_triv
            apply defer_ex'
            apply defer_existential
            apply ((rule exI)+, rule conjI, simp)+
             apply (rule conjI)
              apply solve_ex_triv
            unfolding make_trans_def
              apply clarsimp
              apply safe
            apply defer_ex'
            apply (rule conjI, (rule; assumption))
            apply mini_ex
            apply defer_ex'
            apply (rule conjI, (rule; assumption))
            apply (mini_existential, simp)+
            apply defer_ex
            apply mini_ex
            apply solve_ex_triv
            apply simp
            apply solve_ex_triv
            apply mini_ex
            by (solve_ex_triv; simp)
          done
        done
      subgoal
        apply simp
        apply (rule disjI1)
        using process_length(2) states_len
        unfolding product.prod_trans_i_alt_def product.product_trans_i_def
        unfolding T_T T_def trans_i_fun_def trans_i_from_def trans_i_map_def states'_def
        unfolding P_unfold make_trans_def
        apply (clarsimp simp: set_map_filter states_length_p)
        apply (clarsimp split: if_split_asm act.split_asm)
        unfolding P_unfold[unfolded process_length(2)[symmetric]] thm P_unfold[unfolded process_length(2)[symmetric]]
        subgoal
          apply solve_ex_triv
          apply simp
          apply (rule conjI)
           apply solve_ex_triv
          by (force dest!: mem_nth)
        done
      done
    done

  (* XXX Unused *)
  lemma transition_rel_mono:
    "(a, b) \<in> transition_rel B" if "(a, b) \<in> transition_rel C" "B \<subseteq> C"
    using that unfolding transition_rel_def b_rel_def fun_rel_def by auto

end

context State_Network_Reachability_Problem_precompiled'
begin

  lemma start_pred':
    "(\<forall> i < p. (pred ! i ! (init ! i)) s\<^sub>0)"
    using start_pred unfolding init_def by auto

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

  lemma inv_fun_inv_of':
    "(inv_fun, inv_of A) \<in> inv_rel states'"
    unfolding inv_rel_def state_set_def
    apply (clarsimp simp add: product.inv_of_simp)
    using state_set_states process_length(1) processes_have_trans
    unfolding inv_fun_def product.product_invariant_def I_I init_def
    apply simp
    apply (rule arg_cong[where f = concat])
    using lengths states_states by (auto simp add: states_length_p I_def)

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
     by (force dest!: states_states simp: states_length_p)

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

  lemma iarray_k'[intro]:
    "(uncurry0 (return (IArray (map int k))), uncurry0 (RETURN k')) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
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

context State_Network_Reachability_Problem_precompiled'
begin

  sublocale impl:
    Reachability_Problem_Impl
      trans_fun inv_fun final_fun "IArray (map int k)" A "(init, s\<^sub>0)"
      "PR_CONST ((\<lambda> (l, s). F l))" m k_fun
    unfolding PR_CONST_def by (standard; rule)

  lemma length_states[intro, simp]:
    "length L' = p" if "(L', u) \<in> states'"
    using that state_set_states init_states states_length_p unfolding state_set_def by auto

  thm a\<^sub>0_def

  term a\<^sub>0

  term E

  thm states_length_p states_states states_states'

  (* XXX Unused *)
  lemma length_reachable:
  "length L' = p" if "E\<^sup>*\<^sup>* a\<^sub>0 ((L', s), u)"
    using that impl.reachable_states states_length_p states_states states_states'
    unfolding reachable_def by blast

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

  lemma P_P[simp]:
    "product'.P = P"
    by simp

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

  lemma product_trans_t_conv:
    "product'.product_trans_s = conv_t ` product.product_trans_s"
    unfolding product'.product_trans_s_def product.product_trans_s_def
    apply safe
    unfolding T_T
    subgoal
      apply (simp add: image_Collect)
      apply (clarsimp simp add: states_length_p trans_of_def N_def image_iff)
      subgoal
        apply defer_ex
        by solve_ex_triv+
      done
    by (solve_ex_triv+; force simp: states_length_p image_Collect N_def trans_of_def)

  lemma prod_trans_s_conv:
    "product'.prod_trans_s = conv_t ` product.prod_trans_s"
    unfolding product'.prod_trans_s_alt_def product.prod_trans_s_alt_def product_trans_t_conv p_p P_P
    apply (simp add: image_Collect)
    apply (rule Collect_cong)
    apply safe
     subgoal
      by solve_ex_triv+
    subgoal
      by solve_ex_triv+
    done

  lemma prod_trans_conv:
    "product'.prod_trans = conv_t ` product.prod_trans"
    unfolding product'.prod_trans_def product.prod_trans_def
    unfolding prod_trans_s_conv prod_trans_i_conv image_Un ..

  lemma prod_conv: "product'.prod_ta = conv_A A"
    unfolding product'.prod_ta_def product'.product_ta_def product.prod_ta_def
    unfolding prod_trans_conv prod_invariant_conv
    by simp

  thm F_reachable_correct'' product'.prod_correct[symmetric] prod_conv

  lemma F_reachable_correct:
    "F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        (map conv_A (fst N), snd N) \<turnstile> \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i))
      )"
    unfolding F_reachable_correct'' product'.prod_correct[symmetric] prod_conv ..

  definition
    "reachability_checker
    \<equiv> worklist_algo2 impl.subsumes_impl impl.a\<^sub>0_impl impl.F_impl impl.succs_impl"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
      uncurry0 (
        RETURN (\<exists> L' s' u u'.
        (map conv_A (fst N), snd N) \<turnstile> \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i)))
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using impl.hnr_F_reachable unfolding reachability_checker_def F_reachable_correct .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> L' s' u u'.
        (map conv_A (fst N), snd N) \<turnstile> \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
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

(* XXX Move *)
lemma bex_n_simp:
  "(\<exists> x \<in> set [0..<n]. P x) \<longleftrightarrow> (\<exists> x < n. P x)"
  by auto

(* XXX Move *)
lemma ball_n_simp:
  "(\<forall> x \<in> set [0..<n]. P x) \<longleftrightarrow> (\<forall> x < n. P x)"
  by auto

subsection \<open>Check preconditions\<close>

context State_Network_Reachability_Problem_precompiled_defs
begin

  abbreviation
    "check_nat_subs \<equiv> \<forall> (_, d) \<in> clkp_set'. d \<ge> 0"

  lemma check_nat_subs:
    "check_nat_subs \<longleftrightarrow> snd ` clkp_set' \<subseteq> \<nat>"
  unfolding Nats_def apply safe
  subgoal for _ _ b using rangeI[of int "nat b"] by auto
  by auto

  definition
    "check_pre \<equiv>
      length inv = p \<and> length trans = p \<and> length pred = p
      \<and> (\<forall> i < p. length (pred ! i) = length (trans ! i) \<and> length (inv ! i) = length (trans ! i))
      \<and> (\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, _, _, l) \<in> set xs. l < length T)
      \<and> length k = m + 1 \<and> p > 0 \<and> m > 0
      \<and> (\<forall> i < p. trans ! i \<noteq> []) \<and> (\<forall> q < p. trans ! q ! 0 \<noteq> [])
      \<and> k ! 0 = 0 \<and> check_nat_subs \<and> clk_set' = {1..m}"

  definition
    "check_ceiling \<equiv> \<forall> (c, d) \<in> clkp_set'. k ! c \<ge> d"

  lemma finite_clkp_set'[intro, simp]:
    "finite clkp_set'"
    unfolding clkp_set'_def by auto

  lemma check_axioms:
    "State_Network_Reachability_Problem_precompiled_raw p m k inv pred trans
    \<longleftrightarrow> check_pre \<and> check_ceiling"
    unfolding
      State_Network_Reachability_Problem_precompiled_raw_def
      check_ceiling_def check_pre_def check_nat_subs
    by auto
end

lemmas [code] =
  State_Network_Reachability_Problem_precompiled_defs.check_axioms
  State_Network_Reachability_Problem_precompiled_defs.clkp_set'_def
  State_Network_Reachability_Problem_precompiled_defs.clk_set'_def
  State_Network_Reachability_Problem_precompiled_defs.check_pre_def
  State_Network_Reachability_Problem_precompiled_defs.check_ceiling_def
  State_Network_Reachability_Problem_precompiled_defs.init_def

lemmas [code] =
  State_Network_Reachability_Problem_precompiled_defs'.trans_out_map_def
  State_Network_Reachability_Problem_precompiled_defs'.trans_in_map_def
  State_Network_Reachability_Problem_precompiled_defs'.trans_i_map_def
  State_Network_Reachability_Problem_precompiled_defs'.all_actions_by_state_def
  State_Network_Reachability_Problem_precompiled_defs'.actions_by_state_def
  State_Network_Reachability_Problem_precompiled_defs'.pairs_by_action_def

lemmas [code] =
  State_Network_Reachability_Problem_precompiled'_axioms_def
  State_Network_Reachability_Problem_precompiled'_def

export_code State_Network_Reachability_Problem_precompiled_raw in SML module_name Test

lemmas [code] =
  State_Network_Reachability_Problem_precompiled_int_vars_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.pred'_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.trans'_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.checkb_def
  State_Network_Reachability_Problem_precompiled_int_vars_axioms_def
  State_Network_Reachability_Problem_precompiled_int_vars_defs.s\<^sub>0_def

code_pred clock_val_a .

export_code State_Network_Reachability_Problem_precompiled_int_vars in SML module_name Test

concrete_definition reachability_checker_impl
  uses State_Network_Reachability_Problem_precompiled_int_vars.reachability_checker_alt_def

lemmas [code] =
  State_Network_Reachability_Problem_precompiled_defs.P_def

export_code reachability_checker_impl in SML_imp module_name TA

thm reachability_checker_impl_def reachability_checker_impl.refine

hide_const check_and_verify

definition [code]:
  "check_and_verify p m k I P T final r bounds na \<equiv>
    if State_Network_Reachability_Problem_precompiled_int_vars p m k I P T r bounds na
    then reachability_checker_impl p m k I P T r bounds na final \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] =
  State_Network_Reachability_Problem_precompiled_int_vars.reachability_checker_hoare

abbreviation "N p I P T r bounds \<equiv>
  State_Network_Reachability_Problem_precompiled_defs.N p I
    (State_Network_Reachability_Problem_precompiled_int_vars_defs.pred' P r bounds)
    (State_Network_Reachability_Problem_precompiled_int_vars_defs.trans' T)"

theorem reachability_check:
  "(uncurry0 (check_and_verify p m k I P T final r bounds na),
    uncurry0 (
       RETURN (
        if State_Network_Reachability_Problem_precompiled_int_vars p m k I P T r bounds na
        then Some (
          \<exists> l' s' u u'.
            (map conv_A (fst (N p I P T r bounds)), snd (N p I P T r bounds)) \<turnstile>
              \<langle>repeat 0 p, repeat 0 r, u\<rangle> \<rightarrow>* \<langle>l', s', u'\<rangle>
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
      check_and_verify_def State_Network_Reachability_Problem_precompiled_defs.init_def
      State_Network_Reachability_Problem_precompiled_int_vars_defs.s\<^sub>0_def
     )+

export_code open check_and_verify checking SML_imp

end (* End of theory *)