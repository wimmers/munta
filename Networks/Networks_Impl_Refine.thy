theory Networks_Impl_Refine
  imports
    Normalized_Zone_Semantics_Impl_Refine Networks_Impl TA_Impl_Misc
begin

(* XXX Rename this way *)
lemmas mem_nth = aux

no_notation Ref.update ("_ := _" 62)

locale Network_Reachability_Problem_precompiled_defs' =
  Network_Reachability_Problem_precompiled_defs +
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
        (\<lambda> (g, (a, b), r, l'). case a of Sil a \<Rightarrow> Some (g, (a, b), r, l') | _ \<Rightarrow> None)
      )) trans"

  definition
    "trans_in_map \<equiv>
      map (map (map
        (\<lambda> (g, (a, b), r, l'). case a of In a \<Rightarrow> (g, (a, b), r, l')) o filter (\<lambda> (g, (a, b), r, l').
          case a of In a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  definition
    "trans_out_map \<equiv>
      map (map (map
        (\<lambda> (g, (a, b), r, l'). case a of Out a \<Rightarrow> (g, (a, b), r, l')) o filter (\<lambda> (g, (a, b), r, l').
          case a of Out a \<Rightarrow> True | _ \<Rightarrow> False))
          ) trans"

  abbreviation
    "nested_list_to_iarray xs \<equiv> IArray (map IArray xs)"

  (* XXX Optimize by using a better data structure? *)
  definition
    "actions_by_state i \<equiv> fold (\<lambda> t acc. acc[fst (fst (snd t)) := (i, t) # (acc ! fst (fst (snd t)))])"

  definition
    "all_actions_by_state t L \<equiv>
      fold (\<lambda> i. actions_by_state i (t !! i !! (L ! i))) [0..<p] (repeat [] na)"

  definition
    "pairs_by_action L OUT \<equiv> concat o
      map (\<lambda> (i, g1, (a, b1), r1, l1). List.map_filter
      (\<lambda> (j, g2, (_, b2), r2, l2).
        if i \<noteq> j then Some (g1 @ g2, (a, Syn b1 b2), r1 @ r2, L[i := l1, j := l2]) else None)
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
    map (\<lambda> (g, (a, b), r, l'). (g, (a, Act b), r, L[i := l']))
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

context Product_TA_Defs
begin

  lemma state_set_states:
    "state_set (trans_of product_ta) \<subseteq> states"
    unfolding state_set_def trans_of_def product_trans_def states_def
      product_trans_def product_ta_def product_trans_i_def product_trans_s_def
    apply auto
       apply blast
      apply blast
     apply (subst list_update_nth_split)
      apply simp
     apply force
    apply (subst list_update_nth_split)
     apply (simp; fail)
    apply safe
     apply (simp add: Network_Reachability_Problem_precompiled_defs.N_def)
     apply force
    apply (subst list_update_nth_split)
     apply (simp add: Network_Reachability_Problem_precompiled_defs.N_def)
    apply force
    done

end

locale Network_Reachability_Problem_precompiled' =
  Network_Reachability_Problem_precompiled +
  Network_Reachability_Problem_precompiled_defs' +
  assumes action_set:
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, (a, _), _, _) \<in> set xs. pred_act (\<lambda> a. a < na) a"
begin

  sublocale Defs: Reachability_Problem_Impl_Defs A init "PR_CONST F" m by standard

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
    using states_n product.state_set_states by blast

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

  lemma in_trans_in_mapI:
    assumes
      "q < p" "l < n" "i < length (trans ! q ! l)"
      "(g1, (In a, b), r1, l1') = trans ! q ! l ! i"
    shows "(g1, (a, b), r1, l1') \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
    using assms process_length(2) trans_length unfolding trans_in_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, (In a, b), r1, l1')"])

  lemma in_trans_out_mapI:
    assumes
      "q < p" "l < n" "i < length (trans ! q ! l)"
      "(g1, (Out a, b), r1, l1') = trans ! q ! l ! i"
    shows "(g1, (a, b), r1, l1') \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
    using assms process_length(2) trans_length unfolding trans_out_map_def
    by (force dest: nth_mem intro!: image_eqI[where x = "(g1, (Out a, b), r1, l1')"])

  lemma in_trans_in_mapD:
    assumes
      "(g1, (a, b), r1, l1') \<in> set (IArray (map IArray trans_in_map) !! q !! l)"
      "q < p" "l < n"
    obtains i where
      "i < length (trans ! q ! l) \<and> (g1, (In a, b), r1, l1') = trans ! q ! l ! i"
    using assms process_length(2) unfolding trans_in_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  (* XXX Remove duplication *)
  lemma in_trans_out_mapD:
    assumes
      "(g1, (a, b), r1, l1') \<in> set (IArray (map IArray trans_out_map) !! q !! l)"
      "q < p" "l < n"
    obtains i where
      "i < length (trans ! q ! l) \<and> (g1, (Out a, b), r1, l1') = trans ! q ! l ! i"
    using assms process_length(2) unfolding trans_out_map_def
    by (fastforce dest: mem_nth split: act.split_asm)

  lemma in_actions_by_stateI:
    assumes
      "(g1, (a, b), r1, l1') \<in> set xs" "a < length acc"
    shows
      "(q, g1, (a, b), r1, l1') \<in> set (actions_by_state q xs acc ! a)
      \<and> a < length (actions_by_state q xs acc)"
    using assms unfolding actions_by_state_def
    apply (induction xs arbitrary: acc)
     apply (simp; fail)
    apply simp
    apply (erule disjE)
     apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, (a, b), r1, l1') \<in> set (acc ! a) \<and> a < length acc"]
        )
      apply (subst list_update_nth_split; auto)
    by auto

  lemma in_actions_by_state_preserv:
    assumes
      "(q, g1, (a, b), r1, l1') \<in> set (acc ! a)" "a < length acc"
    shows
      "(q, g1, (a, b), r1, l1') \<in> set (actions_by_state y xs acc ! a)
      \<and> a < length (actions_by_state y xs acc)"
    using assms unfolding actions_by_state_def
    apply -
    apply (rule fold_acc_preserv
        [where P = "\<lambda> acc. (q, g1, (a, b), r1, l1') \<in> set (acc ! a) \<and> a < length acc"]
        )
    apply (subst list_update_nth_split; auto)
    by auto

  lemma length_actions_by_state_preserv[simp]:
    shows "length (actions_by_state y xs acc) = length acc"
    unfolding actions_by_state_def by (auto intro: fold_acc_preserv simp: list_update_nth_split)

  lemma in_all_actions_by_stateI:
    assumes
      "a < na" "q < p" "L ! q < n" "(g1, (a, b), r1, l1') \<in> set (M !! q !! (L ! q))"
    shows
      "(q, g1, (a, b), r1, l1') \<in> set (all_actions_by_state M L ! a)"
    unfolding all_actions_by_state_def
    apply (rule fold_acc_ev_preserv
        [where P = "\<lambda> acc. (q, g1, (a, b), r1, l1') \<in> set (acc ! a)" and Q = "\<lambda> acc. a < length acc",
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
      by (cases "fst (fst (snd x)) = j"; simp)
    using assms by auto

  lemma actions_by_state_inj':
    assumes "j < length acc" "(q, a) \<notin> set (acc ! j)" "(q, a) \<in> set (actions_by_state i xs acc ! j)"
    shows "i = q"
    using actions_by_state_inj[OF assms(1)] assms(2-) by fast

  lemma in_actions_by_stateD:
    assumes
      "(q, g, (a, b), t) \<in> set (actions_by_state i xs acc ! j)" "(q, g, (a, b), t) \<notin> set (acc ! j)"
      "j < length acc"
    shows
      "(g, (a, b), t) \<in> set xs \<and> j = a"
    using assms unfolding actions_by_state_def
    apply -
    apply (drule fold_evD
        [where y = "(g, (a, b), t)" and Q = "\<lambda> acc'. length acc' = length acc"
          and R = "\<lambda> (_, (a', _), t). a' = j"]
        )
         apply assumption
      (* XXX Define asm split rule *)
        apply (subst (asm) list_update_nth_split[of j]; force)
       apply simp+
     apply (subst (asm) list_update_nth_split[of j]; force)
    by auto

  lemma in_all_actions_by_stateD:
    assumes
      "(q, g1, (a, b), r1, l1') \<in> set (all_actions_by_state M L ! a')" "a' < na"
    shows
      "(g1, (a, b), r1, l1') \<in> set (M !! q !! (L ! q)) \<and> q < p \<and> a' = a"
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
      "(g1, (In a, b), r1, l1') = trans ! q ! l ! j"
      "l < n"
      "j < length (trans ! q ! l)"
    shows "a < na"
    using action_set assms process_length(2) trans_length by (force dest!: nth_mem)

  lemma in_actions_trans_in_mapI:
    assumes
      "pa < p"
      "(g1, (In a, b), r1, l1') = trans ! pa ! (L ! pa) ! j"
      "L ! pa < n"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, (a, b), r1, l1') \<in> set (all_actions_by_state (IArray (map IArray trans_in_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) trans_length apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_in_mapI)+

  lemma in_actions_trans_out_mapI:
    assumes
      "pa < p"
      "(g1, (Out a, b), r1, l1') = trans ! pa ! (L ! pa) ! j"
      "L ! pa < n"
      "j < length (trans ! pa ! (L ! pa))"
    shows "(pa, g1, (a, b), r1, l1') \<in> set (all_actions_by_state (IArray (map IArray trans_out_map)) L ! a)"
    apply (rule in_all_actions_by_stateI)
    using assms action_set process_length(2) trans_length apply (fastforce dest!: nth_mem)
    using assms by (fastforce intro: in_trans_out_mapI)+

  lemma in_pairs_by_actionI:
    assumes
      "pa \<noteq> q"
      "(pa, g1, (a, b1), r1, l1') \<in> set ys"
      "(q, g2, (a, b2), r2, l2') \<in> set xs"
    shows "(g1 @ g2, (a, Syn b1 b2), r1 @ r2, L[pa := l1', q := l2']) \<in> set (pairs_by_action L xs ys)"
    using assms
    unfolding pairs_by_action_def
    apply clarsimp
    apply (rule bexI[rotated], assumption)
    by (force simp: set_map_filter)+

  lemma in_pairs_by_actionD:
    assumes
      "(g, (a, b), r, L') \<in> set (pairs_by_action L xs ys)"
      "\<forall> (q, g, (a'', b), r, L') \<in> set xs. a'' = a'"
      "\<forall> (q, g, (a'', n), r, L') \<in> set ys. a'' = a'"
    obtains pa q g1 g2 b1 b2 r1 r2 l1' l2' where
      "pa \<noteq> q"
      "(pa, g1, (a, b1), r1, l1') \<in> set ys"
      "(q, g2, (a, b2), r2, l2') \<in> set xs"
      "L' = L[pa := l1', q := l2']"
      "g = g1 @ g2" "b = Syn b1 b2" "r = r1 @ r2"
  proof -
    from assms(1) obtain pa q g1 g2 b1 b2 r1 r2 l1' l2' where
      "(q, g1, (a, b1), r1, l1') \<in> set ys" "(pa, g2, (a, b2), r2, l2') \<in> set xs" "pa \<noteq> q"
      "Some (g1 @ g2, a, Syn b1 b2, r1 @ r2, L[q := l1', pa := l2']) = Some (g, a, b, r, L')"
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
    subgoal for L g a b r L'
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
        subgoal premises prems for pa b l' j
        proof -
          have "(g, (Sil a, b), r, l') \<in> set (trans ! pa ! (L ! pa))" using prems by auto
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
        unfolding trans_s_fun_def
        apply clarsimp
        by (fastforce intro: less_naI in_actions_trans_out_mapI in_actions_trans_in_mapI in_pairs_by_actionI)
      done
    subgoal for L g a b r L'
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
    "(trans_fun, trans_of A) \<in> transition_rel Defs.states"
    using trans_fun_trans_of' product.state_set_states init_states
    unfolding state_set_def transition_rel_def T_def by blast

  definition "inv_fun L \<equiv> concat (map (\<lambda> i. IArray (map IArray inv) !! i !! (L ! i)) [0..<p])"

  lemma I_I:
    "product.I = map I [0..<p]"
    unfolding I_def inv_of_def N_def by auto

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel Defs.states"
    unfolding inv_rel_def state_set_def apply clarsimp
    using product.state_set_states process_length(1) n_gt_0
    unfolding inv_fun_def product.product_invariant_def I_I init_def
    by - (rule arg_cong[where f = concat]; force simp add: states_length_p I_def)

  definition "final_fun L = list_ex (\<lambda> i. List.member (final ! i) (L ! i)) [0..<p]"

  term list_ex term List.member

  term local.F

  lemma final_fun_final[intro, simp]:
    "(final_fun, F) \<in> inv_rel Defs.states"
    using state_set_n
    unfolding state_set_def init_def F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
    by force

  thm conj_ac(3)[symmetric]

  lemma fst_clkp_set'D:
    assumes "(c, d) \<in> clkp_set'"
    shows "c > 0" "c \<le> m" "d \<in> range int"
  using assms clock_set consts_nats unfolding Nats_def clk_set'_def by force+

  lemma k_ceiling':
    "\<forall>c\<in>{1..m}. k ! c = nat (Max ({d. (c, d) \<in> clkp_set'} \<union> {0}))"
  using k_ceiling by auto (* XXX *)

  lemma k_k'[intro]:
    "map int k = default_ceiling.k'"
    apply (rule nth_equalityI)
     using k_length default_ceiling.length_k' apply (auto; fail)
    unfolding default_ceiling.k'_def apply (simp add: clkp_set'_eq k_length default_ceiling_def del: upt_Suc)
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
    "(uncurry0 (return (IArray (map int k))), uncurry0 (RETURN default_ceiling.k'))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a iarray_assn"
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

context Network_Reachability_Problem_precompiled'
begin

  sublocale
    Reachability_Problem_Impl
      trans_fun inv_fun final_fun "IArray k" A init "PR_CONST F" m "default_ceiling A"
    unfolding PR_CONST_def by (standard; rule)

  lemma length_states[intro, simp]:
    "length L' = p" if "L' \<in> states"
    using that product.state_set_states init_states states_length_p unfolding state_set_def by auto

  (* XXX Unused *)
  lemma length_reachable:
  "length L' = p" if "default_ceiling.E\<^sup>*\<^sup>* default_ceiling.a\<^sub>0 (L', u)"
    using that reachable_states unfolding default_ceiling.reachable_def by auto

  lemma length_steps:
  "length L' = p" if "conv_A A \<turnstile> \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>" "\<forall>c\<in>{1..m}. u c = 0"
    using that default_ceiling.reachable_decides_emptiness'[of L'] by (auto intro: length_reachable)

  lemma F_reachable_correct':
    "default_ceiling.F_reachable
    \<longleftrightarrow> (\<exists> L' u u'.
        conv_A A \<turnstile> \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < length L'. L' ! i \<in> set (final ! i))
      )"
    unfolding default_ceiling.F_reachable_def default_ceiling.reachable_def
    using default_ceiling.reachability_check unfolding F_def by auto

  lemma F_reachable_correct'':
    "default_ceiling.F_reachable
    \<longleftrightarrow> (\<exists> L' u u'.
        conv_A A \<turnstile> \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>
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

  lemma product_trans_i_conv:
    "product'.product_trans_i = conv_t ` product.product_trans_i"
    unfolding product'.product_trans_i_def product.product_trans_i_def
    apply clarsimp
    apply safe
    unfolding T_T
     apply (subst (asm) (2) N_def)
     apply (force simp add: states_length_p trans_of_def image_Collect)
    (* XXX Use tactic here *)
    by (force simp: trans_of_def N_def states_length_p)

  lemma product_trans_t_conv:
    "product'.product_trans_s = conv_t ` product.product_trans_s"
    unfolding product'.product_trans_s_def product.product_trans_s_def
    apply clarsimp
    apply safe
    unfolding T_T
     apply (subst (asm) (2) N_def)
     apply (subst (asm) (2) N_def)
     apply simp
     apply (simp add: states_length_p trans_of_def image_Collect)
     apply (simp only: ex_simps[symmetric])
     apply (tactic \<open>rotate_ex_tac @{context} 1\<close>)
     apply (fastforce simp add: states_length_p)
    apply (simp add: states_length_p trans_of_def image_Collect N_def del: ex_simps)
    apply (tactic \<open>rearrange_ex_tac @{context} 1\<close>)
    apply (simp only: ex_simps)
    apply (rule, rule, assumption)
    apply (simp only: ex_simps[symmetric])
    apply (tactic \<open>rearrange_ex_tac @{context} 1\<close>)
    apply simp
    apply (rule, rule, assumption, rule, assumption)
    apply (rule exI, rule exI, rule conjI, rule HOL.refl)+
    by force

  lemma product_trans_conv:
    "product'.product_trans = conv_t ` product.product_trans"
    unfolding product'.product_trans_def product.product_trans_def
    unfolding product_trans_t_conv product_trans_i_conv image_Un ..

  lemma product_conv: "product'.product_ta = conv_A A"
    unfolding product'.product_ta_def product.product_ta_def
    unfolding product_trans_conv product_invariant_conv
    by simp

  lemma F_reachable_correct:
    "default_ceiling.F_reachable
    \<longleftrightarrow> (\<exists> L' u u'.
        map conv_A N \<turnstile>\<^sub>N \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i))
      )"
    unfolding F_reachable_correct'' product'.product_correct[symmetric] product_conv ..

  definition
    "reachability_checker \<equiv> worklist_algo2 subsumes_impl a\<^sub>0_impl F_impl succs_impl"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
      uncurry0 (
        RETURN (\<exists> L' u u'.
        map conv_A N \<turnstile>\<^sub>N \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i)))
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  using hnr_F_reachable unfolding reachability_checker_def F_reachable_correct .

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r \<longleftrightarrow> (\<exists> L' u u'.
        map conv_A N \<turnstile>\<^sub>N \<langle>init, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> i < p. L' ! i \<in> set (final ! i)))
       )
    >\<^sub>t"
   apply (rule cons_post_rule)
   using reachability_check[to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  subsubsection \<open>Post-processing\<close>

  schematic_goal succs_impl_alt_def:
    "succs_impl \<equiv> ?impl"
  unfolding succs_impl_def
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
        sub = subsumes_impl;
        start = a\<^sub>0_impl;
        final = F_impl;
        succs = succs_impl
      in worklist_algo2 sub start final succs"
    unfolding reachability_checker_def by simp

  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
    unfolding reachability_checker_alt_def' succs_impl_def
    (*apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>) *)
   apply (tactic \<open>pull_tac @{term "IArray (map int k)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
    apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
    unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def trans_i_from_def
   apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
   apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
   unfolding init_dbm_impl_def a\<^sub>0_impl_def
   unfolding F_impl_def
   unfolding final_fun_def[abs_def]
   unfolding subsumes_impl_def
  by (rule Pure.reflexive)

end (* End of locale *)

(* XXX Move *)
lemma bex_n_simp:
  "(\<exists> x \<in> set [0..<n]. P x) \<longleftrightarrow> (\<exists> x < n. P x)"
  by auto

(* XXX Move *)
lemma ball_n_simp:
  "(\<forall> x \<in> set [0..<n]. P x) \<longleftrightarrow> (\<forall> x < n. P x)"
  by auto

subsection \<open>Check preconditions\<close>

context Network_Reachability_Problem_precompiled_defs
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
      length inv = p \<and> length trans = p
      \<and> (\<forall> I \<in> set inv. length I = n) \<and> (\<forall> T \<in> set trans. length T = n)
      \<and> length k = m + 1 \<and> p > 0 \<and> m > 0 \<and> n > 0
      \<and> (\<forall> q < p. trans ! q ! 0 \<noteq> [])
      \<and> k ! 0 = 0 \<and> check_nat_subs \<and> clk_set' = {1..m}
      \<and> (\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, _, _, l) \<in> set xs. l < n)"

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

  definition
    "check_trans_complete \<equiv>
      (\<forall> q1 < p. \<forall> t1 \<in> T q1. case t1 of (l1, g1, In a, r1, l1')
        \<Rightarrow> \<exists> q2 < p. \<exists> l2 g2 r2 l2'. q1 \<noteq> q2 \<and> (l2, g2, Out a, r2, l2') \<in> T q2 | _ \<Rightarrow> True)
      \<and> (\<forall> q1 < p. \<forall> t1 \<in> T q1. case t1 of (l1, g1, Out a, r1, l1')
        \<Rightarrow> \<exists> q2 < p. \<exists> l2 g2 r2 l2'. q1 \<noteq> q2 \<and> (l2, g2, In a, r2, l2') \<in> T q2 | _ \<Rightarrow> True)"

  (* XXX Simplify proofs further up with this? *)
  lemma T_alt_def:
    "T i = {(l, t) | l t. l < n \<and> t \<in> set (trans ! i ! l)}"
    unfolding T_def
    apply safe
     apply (force dest!: nth_mem)
    by (force dest!: mem_nth)

  lemma check_trans_1:
    "(\<forall> q1 < p. \<forall> t1 \<in> T q1. case t1 of (l1, g1, In a, r1, l1')
          \<Rightarrow> \<exists> q2 < p. \<exists> l2 g2 r2 l2'. q1 \<noteq> q2 \<and> (l2, g2, Out a, r2, l2') \<in> T q2 | _ \<Rightarrow> True)
    \<longleftrightarrow>
    list_all (\<lambda> q1. list_all (\<lambda> l. list_all (\<lambda> t1. case t1 of (g1, In a, r1, l1')
          \<Rightarrow> list_ex (\<lambda> q2. q1 \<noteq> q2 \<and>
              list_ex (\<lambda> l. list_ex (\<lambda> t. fst (snd t) = Out a) (trans ! q2 ! l)) [0..<n])
            [0..<p]
      | _ \<Rightarrow> True)
          (trans ! q1 ! l))
        [0..<n])
      [0..<p]"
    unfolding list_ex_iff list_all_iff T_alt_def bex_n_simp ball_n_simp
    by (force split: act.split) (* XXX Slow *)

  lemma check_trans_2:
    "(\<forall> q1 < p. \<forall> t1 \<in> T q1. case t1 of (l1, g1, Out a, r1, l1')
          \<Rightarrow> \<exists> q2 < p. \<exists> l2 g2 r2 l2'. q1 \<noteq> q2 \<and> (l2, g2, In a, r2, l2') \<in> T q2 | _ \<Rightarrow> True)
    \<longleftrightarrow>
    list_all (\<lambda> q1. list_all (\<lambda> l. list_all (\<lambda> t1. case t1 of (g1, Out a, r1, l1')
          \<Rightarrow> list_ex (\<lambda> q2. q1 \<noteq> q2 \<and>
              list_ex (\<lambda> l. list_ex (\<lambda> t. fst (snd t) = In a) (trans ! q2 ! l)) [0..<n])
            [0..<p]
      | _ \<Rightarrow> True)
          (trans ! q1 ! l))
        [0..<n])
      [0..<p]"
    unfolding list_ex_iff list_all_iff T_alt_def bex_n_simp ball_n_simp
    by (force split: act.split) (* XXX Slow *)

  lemma check_trans_complete_alt_def:
    "check_trans_complete \<longleftrightarrow>
      list_all (\<lambda> q1. list_all (\<lambda> l. list_all (\<lambda> t1. case t1 of (g1, In a, r1, l1')
        \<Rightarrow> list_ex (\<lambda> q2. q1 \<noteq> q2 \<and>
            list_ex (\<lambda> l. list_ex (\<lambda> t. fst (snd t) = Out a) (trans ! q2 ! l)) [0..<n])
          [0..<p]
    | _ \<Rightarrow> True)
        (trans ! q1 ! l))
      [0..<n])
    [0..<p]
   \<and> list_all (\<lambda> q1. list_all (\<lambda> l. list_all (\<lambda> t1. case t1 of (g1, Out a, r1, l1')
        \<Rightarrow> list_ex (\<lambda> q2. q1 \<noteq> q2 \<and>
            list_ex (\<lambda> l. list_ex (\<lambda> t. fst (snd t) = In a) (trans ! q2 ! l)) [0..<n])
          [0..<p]
    | _ \<Rightarrow> True)
        (trans ! q1 ! l))
      [0..<n])
    [0..<p]"
    unfolding check_trans_complete_def check_trans_1 check_trans_2 by (rule HOL.refl)

  lemma check_axioms:
    "Network_Reachability_Problem_precompiled p n m k inv trans
    \<longleftrightarrow> check_pre \<and> check_ceiling \<and> check_trans_complete"
    unfolding
      Network_Reachability_Problem_precompiled_def check_ceiling check_pre_def
      check_trans_complete_def check_nat_subs
    by auto

end

lemmas Network_Reachability_Problem_precompiled_defs.check_axioms[code]

lemmas Network_Reachability_Problem_precompiled_defs.clkp_set'_def[code]

lemmas Network_Reachability_Problem_precompiled_defs.clk_set'_def[code]

lemmas Network_Reachability_Problem_precompiled_defs.check_pre_def[code]

lemmas Network_Reachability_Problem_precompiled_defs.check_ceiling_def[code]

lemmas Network_Reachability_Problem_precompiled_defs.check_trans_complete_alt_def[code]

lemmas Network_Reachability_Problem_precompiled_defs.init_def[code]

lemmas [code] =
  Network_Reachability_Problem_precompiled_defs'.trans_out_map_def
  Network_Reachability_Problem_precompiled_defs'.trans_in_map_def
  Network_Reachability_Problem_precompiled_defs'.trans_i_map_def
  Network_Reachability_Problem_precompiled_defs'.all_actions_by_state_def
  Network_Reachability_Problem_precompiled_defs'.actions_by_state_def
  Network_Reachability_Problem_precompiled_defs'.pairs_by_action_def

lemmas [code] =
  Network_Reachability_Problem_precompiled'_axioms_def
  Network_Reachability_Problem_precompiled'_def
  pred_act_def

export_code Network_Reachability_Problem_precompiled in SML module_name Test

export_code Network_Reachability_Problem_precompiled' in SML module_name Test

concrete_definition succs_impl' uses Network_Reachability_Problem_precompiled'.succs_impl_alt_def

thm succs_impl'_def succs_impl'.refine

concrete_definition reachability_checker_impl
  uses Network_Reachability_Problem_precompiled'.reachability_checker_alt_def

export_code reachability_checker_impl in SML_imp module_name TA

thm reachability_checker_impl_def reachability_checker_impl.refine

hide_const check_and_verify

definition [code]:
  "check_and_verify p n m k I T na final \<equiv>
    if Network_Reachability_Problem_precompiled' p n m k I T na
    then reachability_checker_impl p m k I T na final \<bind> (\<lambda> x. return (Some x))
    else return None"

lemmas [sep_heap_rules] = Network_Reachability_Problem_precompiled'.reachability_checker_hoare

theorem reachability_check:
  "(uncurry0 (check_and_verify p n m k I T na final),
    uncurry0 (
       RETURN (
        if (Network_Reachability_Problem_precompiled' p n m k I T na)
        then Some (
          \<exists> l' u u'.
            map conv_A (Network_Reachability_Problem_precompiled_defs.N p n I T) \<turnstile>\<^sub>N \<langle>repeat 0 p, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>
            \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> (\<exists> q < p. l' ! q \<in> set (final ! q))
          )
        else None
       )
    )
   )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
  by sepref_to_hoare
    (sep_auto simp: reachability_checker_impl.refine[symmetric] check_and_verify_def
     Network_Reachability_Problem_precompiled_defs.init_def)

export_code open check_and_verify checking SML_imp

end (* End of theory *)
