theory Networks_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl_Refine Networks_Impl
begin

(* XXX Move *)
subsection \<open>Invariants on folds\<close>

lemma fold_acc_preserv:
  assumes "\<And> x acc. P acc \<Longrightarrow> P (f x acc)" "P acc"
  shows "P (fold f xs acc)"
  using assms(2) by (induction xs arbitrary: acc) (auto intro: assms(1))

lemma fold_acc_ev_preserv':
  fixes x
  assumes
    "\<And> x acc. P acc \<Longrightarrow> P (f x acc)" "\<And> x acc. Q acc \<Longrightarrow> Q (f x acc)"
    "\<And> acc. Q acc \<Longrightarrow> P (f x acc)" "x \<in> set xs" "Q acc"
  shows "P (fold f xs acc) \<and> Q (fold f xs acc)"
  using assms(4,5) apply (induction xs arbitrary: acc)
  using assms(1,2,3) by (auto intro: fold_acc_preserv)

lemma fold_acc_ev_preserv:
  fixes x
  assumes
    "\<And> x acc. P acc \<Longrightarrow> Q acc \<Longrightarrow> P (f x acc)" "\<And> x acc. Q acc \<Longrightarrow> Q (f x acc)"
    "\<And> acc. Q acc \<Longrightarrow> P (f x acc)" "x \<in> set xs" "Q acc"
  shows "P (fold f xs acc) \<and> Q (fold f xs acc)"
  apply (rule fold_acc_ev_preserv'[where P = "\<lambda> acc. P acc \<and> Q acc" and Q = Q, THEN conjunct1])
  by (auto intro: assms)

lemmas fold_ev_preserv = fold_acc_ev_preserv[where Q = "\<lambda> _. True", simplified]

lemma fold_evD':
  assumes "\<not> P acc" "P (fold f xs acc)"
    shows "\<exists> x ys zs. xs = ys @ x # zs \<and> \<not> P (fold f ys acc) \<and> P (f x (fold f ys acc))"
  using assms
  apply (induction xs arbitrary: acc)
   apply (simp; fail)
  subgoal premises prems for x xs acc
    apply (cases "P (f x acc)")
     using prems(2-) apply fastforce
     apply (drule prems(1))
     using prems apply simp
     apply clarsimp
     subgoal for xa ys zs
       apply (rule exI[where x = xa])
       apply (rule exI[where x = "x # ys"])
       by fastforce
     done
   done

lemma fold_evD:
  assumes
    "P y (fold f xs acc)" "\<not> P y acc" "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> x = y"
    "Q acc" "\<And> acc x. Q acc \<Longrightarrow> Q (f x acc)" "\<And> acc x. \<not> P y acc \<Longrightarrow> Q acc \<Longrightarrow> P y (f x acc) \<Longrightarrow> R y"
  shows "\<exists> ys zs. xs = ys @ y # zs \<and> \<not> P y (fold f ys acc) \<and> P y (f y (fold f ys acc)) \<and> R y"
proof -
  from fold_evD'[OF assms(2,1)] obtain x ys zs where *:
    "xs = ys @ x # zs" "\<not> P y (fold f ys acc)" "P y (f x (fold f ys acc))"
    by auto
  moreover from assms(4-) have "Q (fold f ys acc)" by (auto intro: fold_acc_preserv)
  ultimately show ?thesis using assms(3,6) by auto
qed

lemmas fold_evD'' = fold_evD[where R = "\<lambda> _. True", simplified]

no_notation Ref.update ("_ := _" 62)

locale Networks_Reachability_Problem_precompiled' = Networks_Reachability_Problem_precompiled +
  fixes na :: nat
  assumes action_set:
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, a, _, _) \<in> set xs. pred_act (\<lambda> a. a < na) a"
begin

  lemma state_set_states:
    "state_set (trans_of A) \<subseteq> product.states"
    unfolding state_set_def trans_of_def product.product_trans_def product.states_def
      product.product_trans_def product.product_ta_def product.product_trans_i_def product.product_trans_s_def
    apply auto
       apply blast
      apply blast
     apply (subst list_update_nth_split)
      apply assumption
     apply (subst (asm) nth_map)
      apply (simp add: Network_Reachability_Problem_precompiled_defs.N_def)
     apply force
    apply (subst list_update_nth_split)
     apply (simp; fail)
    apply safe
     apply (subst (asm) (2) nth_map)
      apply (simp add: Network_Reachability_Problem_precompiled_defs.N_def)
     apply force
    apply (subst list_update_nth_split)
     apply assumption
    apply (subst (asm) nth_map)
     apply (simp add: Network_Reachability_Problem_precompiled_defs.N_def)
    apply force
    done

  lemma states_n:
    "product.states \<subseteq> {xs. length xs = p \<and> set xs \<subseteq> {0..<n}}"
    unfolding product.states_def
    apply simp
    unfolding N_def trans_of_def T_def
    using state_set trans_length apply safe
    apply (drule aux)
    apply safe
    using state_set
    apply clarsimp
    apply rotate_tac
    subgoal for x i
      apply (erule ballE[where x = i])
       apply auto
      unfolding process_length(2)[symmetric]
      by (force dest: nth_mem) (* XXX Slow *)
    done

  lemma state_set_n:
    "state_set (trans_of A) \<subseteq> {xs. length xs = p \<and> set xs \<subseteq> {0..<n}}"
    using states_n state_set_states by blast

  lemma T_T:
    "product.T = map T [0..<p]"
    unfolding T_def trans_of_def N_def by auto

  lemma states_length_p:
    assumes "l \<in> product.states"
    shows "length l = p"
      using assms length_N product.states_length by simp

  lemma trans_length_simp[simp]:
    assumes "i < p"
    shows "length (trans ! i) = n"
      using assms trans_length process_length by (auto dest: nth_mem)

  (* XXX Rename this way *)
  lemmas mem_nth = aux

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
        (\<lambda> (g, a, r, l'). case a of Sil a \<Rightarrow> Some (g, a, r, l') | _ \<Rightarrow> None)
      )) trans"

  definition
    "trans_in_map \<equiv>
      map (map (map
        (\<lambda> (g, a, r, l'). case a of In a \<Rightarrow> (g, a, r, l')) o filter (\<lambda> (g, a, r, l').
          case a of In a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  definition
    "trans_out_map \<equiv>
      map (map (map
        (\<lambda> (g, a, r, l'). case a of Out a \<Rightarrow> (g, a, r, l')) o filter (\<lambda> (g, a, r, l').
          case a of Out a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  abbreviation
    "nested_list_to_iarray xs \<equiv> IArray (map IArray xs)"

  definition
    "actions_by_state i \<equiv> fold (\<lambda> t acc. acc[fst (snd t) := (i, t) # (acc ! fst (snd t))])"

  definition
    "all_actions_by_state t L \<equiv>
      fold (\<lambda> i. actions_by_state i (t !! i !! (L ! i))) [0..<p] (repeat [] na)"

  definition
    "pairs_by_action L OUT \<equiv> concat o
      map (\<lambda> (i, g1, a, r1, l1). List.map_filter
      (\<lambda> (j, g2, _, r2, l2). if i \<noteq> j then Some (g1 @ g2, a, r1 @ r2, L[i := l1, j := l2]) else None)
      OUT)"

  definition
    "trans_s_fun L \<equiv>
      let
        In = all_actions_by_state (nested_list_to_iarray trans_in_map) L;
        Out = all_actions_by_state (nested_list_to_iarray trans_out_map) L
      in
        concat (map (\<lambda> a. pairs_by_action L (Out ! a) (In ! a)) [0..<na])
    "

  definition
    "trans_i_from L i \<equiv>
    map (\<lambda> (g, a, r, l'). (g, a, r, L[i := l'])) ((IArray (map IArray trans_i_map)) !! i !! (L ! i))"

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

  lemma in_trans_in_mapI:
    assumes
      "q < p" "l < n" "i < length (trans ! q ! l)"
      "(g1, In a, r1, l1') = trans ! q ! l ! i"
    shows "(g1, a, r1, l1') \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
    using assms process_length(2) trans_length unfolding trans_in_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, In a, r1, l1')"])

  lemma in_trans_out_mapI:
    assumes
      "q < p" "l < n" "i < length (trans ! q ! l)"
      "(g1, Out a, r1, l1') = trans ! q ! l ! i"
    shows "(g1, a, r1, l1') \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
    using assms process_length(2) trans_length unfolding trans_out_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, Out a, r1, l1')"])

  lemma in_trans_in_mapD:
    assumes
      "(g1, a, r1, l1') \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
      "q < p" "l < n"
    obtains i where
      "i < length (trans ! q ! l) \<and> (g1, In a, r1, l1') = trans ! q ! l ! i"
    using assms process_length(2) unfolding trans_in_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  (* XXX Remove duplication *)
  lemma in_trans_out_mapD:
    assumes
      "(g1, a, r1, l1') \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
      "q < p" "l < n"
    obtains i where
      "i < length (trans ! q ! l) \<and> (g1, Out a, r1, l1') = trans ! q ! l ! i"
    using assms process_length(2) unfolding trans_out_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  lemma in_actions_by_stateI:
    assumes
      "(g1, a, r1, l1') \<in> set xs" "a < length acc"
    shows "(q, g1, a, r1, l1') \<in> set (actions_by_state q xs acc ! a) \<and> a < length (actions_by_state q xs acc)"
    using assms unfolding actions_by_state_def
    apply (induction xs arbitrary: acc)
     apply (simp; fail)
    apply simp
    apply (erule disjE)
     apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1, l1') \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto

  lemma in_actions_by_state_preserv:
    assumes
      "(q, g1, a, r1, l1') \<in> set (acc ! a)" "a < length acc"
    shows "(q, g1, a, r1, l1') \<in> set (actions_by_state y xs acc ! a) \<and> a < length (actions_by_state y xs acc)"
    using assms unfolding actions_by_state_def
    apply -
    apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1, l1') \<in> set (acc ! a) \<and> a < length acc"]
        )
    apply (subst list_update_nth_split; auto)
    by auto

  lemma length_actions_by_state_preserv[simp]:
    shows "length (actions_by_state y xs acc) = length acc"
    unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

  lemma in_all_actions_by_stateI:
    assumes
      "a < na" "q < p" "L ! q < n" "(g1, a, r1, l1') \<in> set (M !! q !! (L ! q))"
    shows
      "(q, g1, a, r1, l1') \<in> set (all_actions_by_state M L ! a)"
    unfolding all_actions_by_state_def
    apply (rule fold_acc_ev_preserv
        [where P = "\<lambda> acc. (q, g1, a, r1, l1') \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
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
      "(q, g, a, t) \<in> set (actions_by_state i xs acc ! j)" "(q, g, a, t) \<notin> set (acc ! j)" "j < length acc"
    shows
      "(g, a, t) \<in> set xs \<and> j = a"
    using assms unfolding actions_by_state_def
    apply -
    apply (drule fold_evD
        [where y = "(g, a, t)" and Q = "\<lambda> acc'. length acc' = length acc" and R = "\<lambda> (_, a', t). a' = j"]
        )
         apply assumption
      (* XXX Define asm split rule *)
        apply (subst (asm) list_update_nth_split[of j]; force)
       apply simp+
     apply (subst (asm) list_update_nth_split[of j]; force)
    by auto

  lemma in_all_actions_by_stateD:
    assumes
      "(q, g1, a, r1, l1') \<in> set (all_actions_by_state M L ! a')" "a' < na"
    shows
      "(g1, a, r1, l1') \<in> set (M !! q !! (L ! q)) \<and> q < p \<and> a' = a"
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
    unfolding all_actions_by_state_def
    by (auto intro: fold_acc_preserv simp add: length_actions_by_state_preserv)

  lemma less_naI:
    assumes
      "q < p"
      "(g1, In a, r1, l1') = trans ! q ! l ! j"
      "l < n"
      "j < length (trans ! q ! l)"
    shows "a < na"
    using action_set assms process_length(2) trans_length by (force dest!: nth_mem)

  lemma in_actions_trans_in_mapI:
    assumes
      "pa < p"
      "(g1, In a, r1, l1') = trans ! pa ! (L ! pa) ! j"
      "L ! pa < n"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, a, r1, l1') \<in> set (all_actions_by_state (IArray (map IArray trans_in_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) trans_length apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_in_mapI)+

  lemma in_actions_trans_out_mapI:
    assumes
      "pa < p"
      "(g1, Out a, r1, l1') = trans ! pa ! (L ! pa) ! j"
      "L ! pa < n"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, a, r1, l1') \<in> set (all_actions_by_state (IArray (map IArray trans_out_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) trans_length apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_out_mapI)+

  lemma in_pairs_by_actionI:
    assumes
      "pa \<noteq> q"
      "(pa, g1, a, r1, l1') \<in> set ys"
      "(q, g2, a, r2, l2') \<in> set xs"
    shows "(g1 @ g2, a, r1 @ r2, L[pa := l1', q := l2']) \<in> set (pairs_by_action L xs ys)"
    using assms
    unfolding pairs_by_action_def
    apply clarsimp
    apply (rule bexI[rotated], assumption)
    by (force simp: set_map_filter)+

  lemma in_pairs_by_actionD:
    assumes
      "(g, a, r, L') \<in> set (pairs_by_action L xs ys)"
      "\<forall> (q, g, a'', r, L') \<in> set xs. a'' = a'"
      "\<forall> (q, g, a'', r, L') \<in> set ys. a'' = a'"
    obtains pa q g1 g2 r1 r2 l1' l2' where
      "pa \<noteq> q"
      "(pa, g1, a, r1, l1') \<in> set ys"
      "(q, g2, a, r2, l2') \<in> set xs"
      "L' = L[pa := l1', q := l2']"
      "g = g1 @ g2" "r = r1 @ r2"
  proof -
    from assms(1) obtain pa q g1 g2 r1 r2 l1' l2' where
      "(q, g1, a, r1, l1') \<in> set ys" "(pa, g2, a, r2, l2') \<in> set xs" "pa \<noteq> q"
      "Some (g1 @ g2, a, r1 @ r2, L[q := l1', pa := l2']) = Some (g, a, r, L')"
      unfolding pairs_by_action_def using assms(2,3) by (force split: if_split_asm simp: set_map_filter)
    then show ?thesis by - (rule that; auto)
  qed

  lemma in_trans_funD:
    assumes "y \<in> set (trans_fun L)"
    shows "y \<in> set (trans_s_fun L) \<or> y \<in> set (trans_i_fun L)"
      using assms unfolding trans_fun_def by auto

  lemma states_len[intro]:
    assumes
      "q < p" "L \<in> product.states"
    shows
      "L ! q < n"
    using assms states_n by (force dest: nth_mem)

  lemma trans_fun_trans_of':
    "(trans_fun, trans_of A) \<in> transition_rel (product.states)"
    unfolding transition_rel_def T_def
    apply simp
    apply rule
    unfolding trans_of_def
    apply safe
    subgoal for L g a r L'
      unfolding product.product_ta_def product.product_trans_def
      apply simp
      apply safe
      subgoal
        apply (rule trans_i_fun_trans_fun)
        unfolding product.product_trans_i_def
        apply safe
        unfolding T_T T_def states_length_p
        apply clarsimp
          (* Could be a lemma from here *)
        unfolding trans_fun_def trans_i_fun_def trans_i_from_def trans_i_map_def
        apply clarsimp
        apply (rule bexI)
         prefer 2
         apply simp
        using process_length(2)
        apply simp
        apply (drule nth_mem)
        subgoal premises prems for pa l' j
        proof -
          have "(g, Sil a, r, l') \<in> set (trans ! pa ! (L ! pa))" using prems by auto
          then show ?thesis by (force simp: set_map_filter)
        qed
        done
      subgoal
        apply (rule trans_s_fun_trans_fun)
        unfolding product.product_trans_s_def
        apply safe
        unfolding T_T T_def states_length_p
        apply clarsimp
          (* Could be a lemma from here *)
        unfolding trans_fun_def trans_s_fun_def
        by (fastforce intro: less_naI in_actions_trans_out_mapI in_actions_trans_in_mapI in_pairs_by_actionI)
      done
    subgoal for L g a r L'
      apply (drule in_trans_funD)
      apply (erule disjE)
      unfolding product.product_ta_def product.product_trans_def
       apply simp
       apply (rule disjI2)
      subgoal
        unfolding product.product_trans_s_def
        apply safe
        unfolding T_T T_def states_length_p
        apply simp
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
          by (fastforce simp: states_length_p)
        done
      subgoal
        apply simp
        apply (rule disjI1)
        unfolding product.product_trans_i_def
        unfolding T_T T_def trans_i_fun_def trans_i_from_def trans_i_map_def
        using trans_length process_length(2) states_len
        apply (clarsimp simp: set_map_filter states_length_p)
        by (force split: act.split_asm dest!: mem_nth) (* XXX Slow *)
      done
    done

  lemma trans_fun_trans_of[intro, simp]:
    "(trans_fun, trans_of A) \<in> transition_rel (state_set (trans_of A))"
    using trans_fun_trans_of' state_set_states unfolding transition_rel_def T_def by blast

  definition "inv_fun L \<equiv> concat (map (\<lambda> i. IArray (map IArray inv) !! i !! (L ! i)) [0..<p])"

  lemma I_I:
    "product.I = map I [0..<p]"
    unfolding I_def inv_of_def N_def by auto

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel (state_set (trans_of A))"
    unfolding inv_rel_def apply clarsimp
    using state_set_states process_length(1)
    unfolding inv_fun_def product.product_invariant_def I_I
    by - (rule arg_cong[where f = concat]; force simp add: states_length_p I_def)

  definition "final_fun L = list_ex (\<lambda> i. List.member (final ! i) (L ! i)) [0..<p]"

  term list_ex term List.member

  term local.F

  lemma final_fun_final[intro, simp]:
    "(final_fun, local.F) \<in> inv_rel (state_set (trans_of A))"
    using state_set_n unfolding F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
    by force

  lemma final_fun_final[intro, simp]:
    "(final_fun, F) \<in> inv_rel (state_set (trans_of A))"
    using state_set_n unfolding F_def final_fun_def inv_rel_def apply (auto simp: in_set_member)
    oops

  thm conj_ac(3)[symmetric]

  lemma start_states[intro, simp]:
    "init \<in> state_set (trans_of A)"
  proof -
    obtain g a r l' where *: "trans ! 0 ! 0 ! 0 = (g, a, r, l')" by (metis prod_cases3)
    then show ?thesis
    proof (cases a)
      case prems: (In a')
      from * n_gt_0 p_gt_0 start_has_trans have
        "(0, g, a, r, l') \<in> T 0"
        unfolding T_def by force
      moreover with prems trans_complete(1) n_gt_0 p_gt_0 start_has_trans obtain q l2 g2 r2 l2' where
        "q<p" "0 \<noteq> q" "(l2, g2, Out a', r2, l2') \<in> T q"
        apply safe
        apply (erule allE[where x = 0])
        by fastforce
      ultimately show ?thesis unfolding product.product_ta_def trans_of_def product.product_trans_def
        unfolding
        product.product_trans_s_alt_def T_T apply safe
        subgoal premises prems
          using prems(1-4) init_states states_length_p[of init] p_gt_0 apply auto
          apply rule
          apply (rule UnI2)
          apply rule
          apply (subst conj_commute)
          apply (subst conj_commute)
          apply (simp only: ex_simps(1,2)[symmetric])
          apply (rule exI[where x = init])
          apply (simp only: conj_ac(3))
          apply (subst ex_comm)
          apply (rule exI[where x = a'])
          apply (subst ex_comm)
          apply (subst (3) ex_comm)
          apply (subst (2) ex_comm)
          apply (subst ex_comm)
          apply (rule exI[where x = 0])
            apply (subst (3) ex_comm)
          apply (subst (2) ex_comm)
          apply (subst ex_comm)
          apply simp
          apply (rule exI)
          apply rule
           apply assumption
          apply rule
           apply assumption
          unfolding \<open>a = _\<close>
          apply auto
          oops

  lemma num_clocks[simp]:
    "Reachability_Problem.n A = m"
  unfolding n_def X_def using clock_set by auto

  lemma fst_clkp_set'D:
    assumes "(c, d) \<in> clkp_set'"
    shows "c > 0" "c \<le> m" "d \<in> range int"
  using assms clock_set consts_nats unfolding Nats_def clk_set'_def by force+

  lemma k_ceiling':
    "\<forall>c\<in>{1..m}. k ! c = nat (Max ({d. (c, d) \<in> clkp_set'} \<union> {0}))"
  using k_ceiling by auto (* XXX *)

  lemma k_k'[intro]:
    "map int k = k'"
    apply (rule nth_equalityI)
     using k_length length_k' apply (auto; fail)
    unfolding k'_def k_def apply (simp add: clkp_set'_eq k_length default_ceiling_def del: upt_Suc)
    using k_ceiling' k_ceiling(2) apply safe
     subgoal for i by (cases "i = 0") auto
    apply (frule fst_clkp_set'D(1))
    apply clarsimp
    apply (rule cong[of nat, OF HOL.refl])
    apply (subst Max_insert)
    using finite_clkp_set_A [[simproc add: finite_Collect]]
    apply (auto intro: finite_Image simp: clkp_set'_eq; fail)
    apply (auto; fail)
    subgoal for i
     using Max_in[of "{d. (i, d) \<in> clkp_set'}"] fst_clkp_set'D(3) finite_clkp_set_A
    by (force intro: finite_Image simp: clkp_set'_eq)
    done

  lemma iarray_k'[intro]:
    "(uncurry0 (return (IArray (map int k))), uncurry0 (RETURN k')) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
    unfolding br_def by sepref_to_hoare sep_auto

  lemma init_has_trans:
    "init \<in> fst ` (trans_of A) \<longleftrightarrow> trans_fun init \<noteq> []"
    apply standard
    using trans_fun_trans_of unfolding transition_rel_def apply force
    using trans_fun_trans_of' init_states unfolding transition_rel_def by fast

  lemma
    assumes "init \<in> fst ` (trans_of A)"
      shows "init \<in> state_set (trans_of A)"
  using assms by (rule UnI1)

end (* End of locale assuming specific format for actions *)

locale Networks_Reachability_Problem_precompiled'' = Networks_Reachability_Problem_precompiled' +
  assumes init_in_state_set:
      "init \<in> state_set (trans_of A)"
begin

  sublocale impl:
    Reachability_Problem_Impl A init "PR_CONST local.F" trans_fun inv_fun final_fun "IArray k"
    apply standard
    unfolding state_set_def
        apply rule
       apply rule
      apply (auto; fail)
     apply (rule init_in_state_set)
    by rule

  lemma
    "impl.F_reachable \<longleftrightarrow> F_reachable"
    unfolding F_reachable_def impl.F_reachable_def impl.F_rel_def F_rel_def
    oops

  lemma F_reachable_correct:
    "impl.F_reachable
    \<longleftrightarrow> (\<exists> L' u u'. conv_A A \<turnstile> \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < length L'. L' ! i \<in> set (final ! i)))"
    unfolding impl.F_reachable_def impl.reachable_def using impl.reachability_check unfolding F_def
    by auto

  definition
    "reachability_checker \<equiv> worklist_algo2 subsumes_impl a\<^sub>0_impl F_impl succs_impl"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
      uncurry0 (
        RETURN (\<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final)
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using hnr_F_reachable unfolding reachability_checker_def F_reachable_correct .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> l' u u'. conv_A A \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final))>\<^sub>t"
   apply (rule cons_post_rule)
   using reachability_check[to_hnr] apply (simp add: hn_refine_def)
  by (sep_auto simp: pure_def)

  subsubsection \<open>Post-processing\<close>

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

  ML \<open>
    val th = @{thm succs_impl_def}
    val r = get_rhs th;
    val u1 = @{term "IArray (map int k)"};
    val rewr1 = pull_let u1 r;
    val r2 = get_rhs rewr1;
    val u2 = @{term "inv_fun"};
    val rewr2 = pull_let u2 r2;
    val r3 = get_rhs rewr2;
    val u3 = @{term "trans_fun"};
    val rewr3 = pull_let u3 r3;
    val mytac = fn ctxt => SELECT_GOAL (Local_Defs.unfold_tac ctxt [rewr1, rewr2, rewr3]) 1;
  \<close>

  lemma inv_fun_alt_def:
    "inv_fun i \<equiv> let I = (IArray inv) in I !! i"
  unfolding inv_fun_def by simp

  lemma inv_fun_rewr:
    "(let I0 = trans_fun; I = inv_fun; I1 = y in xx I0 I I1) \<equiv>
     (let I0 = trans_fun; I = (IArray inv); I' = \<lambda> i. I !! i; I1 = y in xx I0 I' I1)"
  unfolding inv_fun_def[abs_def] by simp

  lemma inv_fun_rewr':
    "(let I = inv_fun in xx I) \<equiv>
     (let I = (IArray inv); I' = \<lambda> i. I !! i in xx I')"
  unfolding inv_fun_def[abs_def] by simp

  schematic_goal succs_impl_alt_def':
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
   apply (tactic \<open>mytac @{context}\<close>)
   unfolding inv_fun_rewr' trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  by (rule Pure.reflexive)

  schematic_goal succs_impl_alt_def:
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
  by (rule Pure.reflexive)

  lemma reachability_checker_alt_def':
    "reachability_checker \<equiv>
      let
        sub = subsumes_impl;
        start = a\<^sub>0_impl;
        final = F_impl;
        succs = succs_impl
      in worklist_algo2 sub start final succs"
  unfolding reachability_checker_def by simp

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
  unfolding reachability_checker_alt_def' succs_impl_def
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
   unfolding trans_map_def label_def
   unfolding init_dbm_impl_def a\<^sub>0_impl_def
   unfolding F_impl_def
   unfolding final_fun_def[abs_def]
   unfolding subsumes_impl_def
   unfolding num_clocks
  by (rule Pure.reflexive)

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
  unfolding succs_impl_def reachability_checker_def
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
   unfolding inv_fun_def[abs_def] trans_fun_def[abs_def]
   apply (tactic \<open>pull_tac @{term "IArray inv"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray trans_map"} @{context}\<close>)
   unfolding num_clocks
  oops

end (* End of locale *)

subsection \<open>Check preconditions\<close>
context Reachability_Problem_precompiled_defs
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
      length inv = n \<and> length trans = n \<and> length k = m + 1 \<and> m > 0 \<and> n > 0 \<and> trans ! 0 \<noteq> []
      \<and> k ! 0 = 0 \<and> check_nat_subs \<and> clk_set' = {1..m}
      \<and> (\<forall> xs \<in> set trans. \<forall> (_, _, l) \<in> set xs. l < n)"

  abbreviation
    "check_k_in c \<equiv> k ! c = 0 \<or> (c, k ! c) \<in> clkp_set'"

  definition
    "check_ceiling \<equiv>
      (\<forall> (c, d) \<in> clkp_set'. 0 < c \<and> c \<le> m \<longrightarrow> k ! c \<ge> d) \<and> (\<forall> c \<in> {1..m}. check_k_in c)"

  lemma finite_clkp_set'[intro, simp]:
    "finite clkp_set'"
  unfolding clkp_set'_def by auto

  lemma check_ceiling:
    "check_ceiling \<longleftrightarrow> (\<forall> c \<in> {1..m}. k ! c = Max ({d. (c, d) \<in> clkp_set'} \<union> {0 :: int}))"
  unfolding check_ceiling_def
  proof (safe, goal_cases)
    case prems: (1 c)
    then show ?case
     apply -
     apply (rule HOL.sym)
     apply (rule Max_eqI)
    using [[simproc add: finite_Collect]] by (auto intro: finite_Image)
  next
    case prems: (2 a b)
    then show ?case
      apply simp
      apply (rule Max_ge)
    using [[simproc add: finite_Collect]] by (auto intro: finite_Image)
  next
    case prems: (3 c)
    with Max_in[of "{d. (c, d) \<in> clkp_set'} \<union> {0}"] show ?case
    using [[simproc add: finite_Collect]] by (force intro: finite_Image)
  qed

  lemma check_axioms:
    "Reachability_Problem_precompiled n m k inv trans \<longleftrightarrow> check_pre \<and> check_ceiling"
  unfolding Reachability_Problem_precompiled_def check_ceiling check_pre_def check_nat_subs by auto

end

lemmas Reachability_Problem_precompiled_defs.check_axioms[code]

lemmas Reachability_Problem_precompiled_defs.clkp_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.clk_set'_def[code]

lemmas Reachability_Problem_precompiled_defs.check_pre_def[code]

lemmas Reachability_Problem_precompiled_defs.check_ceiling_def[code]

export_code Reachability_Problem_precompiled in SML module_name Test

concrete_definition succs_impl' uses Reachability_Problem_precompiled.succs_impl_alt_def

thm succs_impl'_def succs_impl'.refine

concrete_definition reachability_checker_impl
  uses Reachability_Problem_precompiled.reachability_checker_alt_def

export_code reachability_checker_impl in SML_imp module_name TA

thm reachability_checker_impl_def reachability_checker_impl.refine

term Reachability_Problem_precompiled.reachability_checker

definition [code]:
  "check_and_verify n m k I T final \<equiv>
    if Reachability_Problem_precompiled n m k I T
    then reachability_checker_impl m k I T final \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] = Reachability_Problem_precompiled.reachability_checker_hoare

theorem reachability_check:
  "(uncurry0 (check_and_verify n m k I T final),
    uncurry0 (
       RETURN (
        if (Reachability_Problem_precompiled n m k I T)
        then Some (
          \<exists> l' u u'.
            conv_A (Reachability_Problem_precompiled_defs.A n I T) \<turnstile> \<langle>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>
            \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> l' \<in> set final
          )
        else None

       )
    )
   )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
by sepref_to_hoare (sep_auto simp: reachability_checker_impl.refine[symmetric] check_and_verify_def)

export_code open check_and_verify checking SML_imp

end (* End of theory *)