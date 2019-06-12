theory UPPAAL_State_Networks_Impl_Refine
  imports
    Program_Analysis
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    TA_Impl.TA_Impl_Misc
begin

chapter \<open>Imperative Implementation of UPPAAL Style Networks\<close>

(* XXX Rename this way *)
lemmas mem_nth = aux

subsection \<open>Executable successor computation\<close>

no_notation Ref.update ("_ := _" 62)
no_notation Bits.test_bit (infixl "!!" 100)
no_notation Stream.snth (infixl "!!" 100)

lemma exec_state_length:
  assumes "exec prog n (pc, st, s, f, rs) pcs = Some ((pc', st', s', f', rs'), pcs')"
  shows "length s = length s'"
  using assms
proof (induction prog n "(pc, st, s, f, rs)" pcs arbitrary: pc st s f rs pcs rule: exec.induct)
  case 1
  then show ?case by simp
next
  case prems: (2 prog n pc st m f rs pcs)
  from prems(2) show ?case
    apply (clarsimp split: option.split_asm if_split_asm)
    apply (drule prems(1), assumption+)
    by (erule step.elims; simp split: if_split_asm)
qed

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

  definition "PROG' pc \<equiv> (if pc < length prog then (IArray prog) !! pc else None)"
  abbreviation "PF \<equiv> stripfp PROG'"
  abbreviation "PT \<equiv> striptp PROG'"
  definition "runf pc s \<equiv> exec PF max_steps (pc, [], s, True, []) []"
  definition "runt pc s \<equiv> exec PT max_steps (pc, [], s, True, []) []"

  lemma PROG'_PROG [simp]:
    "PROG' = PROG"
    unfolding PROG'_def PROG_def by (rule ext) simp

  definition "bounded' s \<equiv>
    (\<forall>i<length s. fst (IArray bounds !! i) < s ! i \<and> s ! i < snd (IArray bounds !! i))"

  definition
    "check_pred L s \<equiv>
      list_all
        (\<lambda> q.
          case runf (pred ! q ! (L ! q)) s of
            Some ((_, _, _, f, _), _) \<Rightarrow> f \<and> bounded' s
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
       (L, g, (a, Networks.label.Act (c, m)), r, L') \<in> Product_TA_Defs.product_trans_i (N_s s) \<and>
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
        \<and> (L, g, (a, Networks.label.Syn (ci, mi) (co, mo)), r, L')
          \<in> Product_TA_Defs.product_trans_s (N_s s)
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


context UPPAAL_Reachability_Problem_precompiled
begin

(* XXX Clean *)
(* XXX Is this already somewhere else? *)
lemma PF_unfold:
  "equiv.PF = stripfp (conv_prog PROG)"
  using [[show_abbrevs=false]]
  unfolding N_def
  apply auto
  unfolding stripfp_def
  apply (rule ext)
  apply auto
  subgoal for x
    apply (cases "PROG x")
     apply auto
    subgoal for a
      by (cases a) auto
    done
  done

(* XXX Clean *)
(* XXX Is this already somewhere else? *)
lemma PT_unfold:
  "equiv.PT = striptp (conv_prog PROG)"
  using [[show_abbrevs=false]]
  unfolding N_def
  apply auto
  unfolding striptp_def
  apply (rule ext)
  apply auto
  subgoal for x
    apply (cases "PROG x")
     apply auto
    subgoal for a
      by (cases a) auto
    done
  done

lemma states'I:
  "l \<in> equiv.defs.states' s" if "A \<turnstile> (l, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (l', s')"
  using equiv.defs.prod_ta_cases[OF that]
  unfolding equiv.defs.prod_trans_i_alt_def equiv.defs.prod_trans_s_alt_def
  unfolding Product_TA_Defs.product_trans_def
  unfolding Product_TA_Defs.product_trans_i_def Product_TA_Defs.product_trans_s_def
  by fastforce

lemma A_lengthD:
  "length l = p" if "A \<turnstile> (l, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (l', s')"
  using that by (auto dest: states'I)

lemma N_s_state_trans:
  assumes "equiv.defs.N_s s ! q \<turnstile> l ! q \<longrightarrow>\<^bsup>g,(a, c, m'),r\<^esup> l'" "q < p"
  obtains f' g' where
    "(l ! q, g', (a, c, m'), f', l') \<in> equiv.state_trans q" "g = g' s" "r = f' s"
  using assms
  unfolding equiv.defs.N_s_def trans_of_def equiv.defs.T_s_def
  unfolding equiv.state_ta_def by auto

lemma make_f_collect_store:
  assumes "(l, pc_g, a, pc_u, l') \<in> fst (equiv.N ! q)" "c \<in> set (equiv.make_f pc_u s)" "q < p"
  shows "c \<in> fst ` collect_store' pc_u"
proof -
  from assms(1) \<open>q < p\<close> have "(pc_g, a, pc_u, l') \<in> set (trans ! q ! l)"
    unfolding N_def T_def by (auto dest!: nth_mem)
  from assms obtain pc x2 x3 x4 pcs r where exec:
    "exec equiv.PF max_steps (pc_u, [], s, True, []) [] = Some ((pc, x2, x3, x4, r), pcs)"
    unfolding equiv.make_f_def by (auto split: option.split_asm) metis
  with assms have "c \<in> set r" unfolding equiv.make_f_def by auto
  with exec_reset'[OF exec] obtain pc' d where "Some (STOREC c d) = equiv.PF pc'" "pc' \<in> set pcs"
    by force
  with exec obtain y2 y3 y4 y5 where steps:
    "steps equiv.PF max_steps (pc_u, [], s, True, []) (pc', y2, y3, y4, y5)"
    by (auto intro: exec_steps')
  from \<open>_ = equiv.PF pc'\<close> have "pc' < length prog"
    unfolding N_def PROG_def stripfp_def by (simp split: if_split_asm)
  from steps have "pc' \<in> steps_approx max_steps prog pc_u"
    unfolding PF_unfold
    unfolding stripfp_def
    by (auto simp: PROG_def intro: steps_steps_approx[of stripf, OF _ _ _ \<open>pc' < length prog\<close>])
  with \<open>_ = equiv.PF pc'\<close> \<open>_ \<in> set (trans ! q ! l)\<close> show ?thesis
    unfolding collect_store'_def stripfp_def N_def PROG_def apply (auto split: if_split_asm)
    apply (cases "prog ! pc'")
     apply (simp; fail)
    subgoal for x
      by (cases x; force)
    done
qed

lemma resets_approx:
  "set r \<subseteq>
  \<Union> {fst ` collect_store' r | i g a r. (g, a, r, (l' ! i)) \<in> set (trans ! i ! (l ! i))}"
  if "A \<turnstile> (l, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (l', s')"
proof -
  from that have [simp]: "length l = p" by (auto dest: A_lengthD)
  show ?thesis using that
    apply clarsimp
    apply (drule equiv.defs.prod_ta_cases)
    apply safe
    subgoal for x
      unfolding equiv.defs.prod_trans_i_alt_def
      apply simp
      unfolding Product_TA_Defs.product_trans_def
      apply safe
      unfolding Product_TA_Defs.product_trans_i_def
      apply clarsimp
      apply (erule N_s_state_trans, assumption)
      unfolding equiv.state_trans_t_def
      apply clarsimp
      subgoal for q l'' pc_g pc_u
        apply (frule make_f_collect_store, assumption+)
        unfolding N_def T_def
        apply (clarsimp dest!: nth_mem)
        subgoal premises prems for b j
        proof -
          from prems(6,8,11-) have
            "(pc_g, Sil a, pc_u, l[q := l''] ! q) \<in> set (trans ! q ! (l ! q))"
            by simp
          with prems(6,8,11-) show ?thesis by blast
        qed
        done
      done
    subgoal for x
      unfolding equiv.defs.prod_trans_s_alt_def
      apply simp
      unfolding Product_TA_Defs.product_trans_def
      apply safe
      unfolding Product_TA_Defs.product_trans_s_def
      apply clarsimp
      apply (erule N_s_state_trans, assumption)
      apply (erule N_s_state_trans, assumption)
      unfolding equiv.state_trans_t_def
      apply clarsimp
      apply (erule disjE)
      subgoal for s1 p' q l'' l'aa pc_g pc_ga pc_u pc_ua
        apply (frule make_f_collect_store, assumption+)
        unfolding N_def T_def
        apply (clarsimp dest!: nth_mem)
        subgoal premises prems for b j j'
        proof -
          from prems(9-) have
            "(pc_g, In a, pc_u, l[p' := l'', q := l'aa] ! p') \<in> set (trans ! p' ! (l ! p'))"
            by simp
          with prems(9-) show ?thesis by blast
        qed
        done
      subgoal for s1 q p' l'aa l'' pc_ga pc_g pc_ua pc_u
        apply (frule make_f_collect_store, assumption+)
        unfolding N_def T_def
        apply (clarsimp dest!: nth_mem)
        subgoal premises prems for b j j'
        proof -
          from prems(9-) have
            "(pc_g, Out a, pc_u, l[q := l'aa, p' := l''] ! p') \<in> set (trans ! p' ! (l ! p'))"
            by simp
          with prems(9-) show ?thesis by blast
        qed
        done
      done
    done
qed

(* XXX Remove
lemma resets_approx':
  assumes "A \<turnstile> (l, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (l', s')"
  obtains pc_u pc_g a' i where
    "fst ` collect_store' pc_u \<subseteq> set r" "i < length l"
    "(pc_g, a', pc_u, (l' ! i)) \<in> set (trans ! i ! (l ! i))"
    apply atomize_elim
*)

lemma make_g_clkp_set'':
  fixes x
  assumes
    "(l, pc_g, a, pc_u, l') \<in> fst (equiv.N ! q)" "x \<in> collect_clock_pairs (equiv.make_g pc_g s)"
    "q < p"
  shows "x \<in> clkp_set'' q l"
proof -
  from assms(1) \<open>q < p\<close> have "(pc_g, a, pc_u, l') \<in> set (trans ! q ! l)"
    unfolding N_def T_def by (auto dest!: nth_mem)
  from assms obtain pc x2 x3 x4 r pcs where exec:
    "exec equiv.PT max_steps (pc_g, [], s, True, []) [] = Some ((pc, x2, x3, x4, r), pcs)"
    unfolding equiv.make_g_def by (auto split: option.split_asm)
  with assms have "x \<in> collect_clock_pairs (List.map_filter (\<lambda> pc.
        case equiv.P pc of
          Some (CEXP ac) \<Rightarrow> Some ac
        | _ \<Rightarrow> None
          )
        pcs)"
    unfolding equiv.make_g_def by auto
  then obtain pc' ac where
    "equiv.P pc' = Some (CEXP ac)" "x = constraint_pair ac" "pc' \<in> set pcs"
    unfolding equiv.make_g_def collect_clock_pairs_def set_map_filter
    by (auto split: option.split_asm; auto split: instrc.split_asm)
  with exec obtain y2 y3 y4 y5 where steps:
    "steps equiv.PT max_steps (pc_g, [], s, True, []) (pc', y2, y3, y4, y5)"
    by (auto intro: exec_steps')
  from \<open>equiv.P pc' = _\<close> have "pc' < length prog"
    unfolding N_def PROG_def by (simp split: if_split_asm)
  from steps have "pc' \<in> steps_approx max_steps prog pc_g"
    unfolding PT_unfold
    unfolding striptp_def
    by (auto simp: PROG_def intro: steps_steps_approx[of stript, OF _ _ _ \<open>pc' < length prog\<close>])
  with \<open>equiv.P pc' = _\<close> \<open>_ \<in> set (trans ! q ! l)\<close> \<open>x = _\<close> show ?thesis
    unfolding clkp_set''_def collect_cexp'_def N_def PROG_def by (force split: if_split_asm)
qed

lemma guard_approx:
  "collect_clock_pairs g \<subseteq>
  \<Union> {clkp_set'' i (l ! i) | i g a r.
      (g, a, r, (l' ! i)) \<in> set (trans ! i ! (l ! i)) \<and> l \<in> equiv.defs.states' s \<and> i < p
    }"
  if "A \<turnstile> (l, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (l', s')"
proof -
  from that have [simp]: "length l = p" by (auto dest: A_lengthD)
  show ?thesis using that
    apply clarsimp
    apply (drule equiv.defs.prod_ta_cases)
    apply safe
    subgoal for x b
      unfolding equiv.defs.prod_trans_i_alt_def
      apply simp
      unfolding Product_TA_Defs.product_trans_def
      apply safe
      unfolding Product_TA_Defs.product_trans_i_def
      apply clarsimp
      apply (erule N_s_state_trans, assumption)
      unfolding equiv.state_trans_t_def
      apply clarsimp
      subgoal for q l'' pc_g pc_u
        apply (frule make_g_clkp_set'', assumption+)
        unfolding N_def T_def
        apply (clarsimp dest!: nth_mem)
        subgoal premises prems for j
        proof -
          from prems(6,8,11-) have
            "(pc_g, Sil a, pc_u, l[q := l''] ! q) \<in> set (trans ! q ! (l ! q))"
            by simp
          with prems(6,8,11-) prems show ?thesis by blast
        qed
        done
      done
    subgoal for x b
      unfolding equiv.defs.prod_trans_s_alt_def
      apply simp
      unfolding Product_TA_Defs.product_trans_def
      apply safe
      unfolding Product_TA_Defs.product_trans_s_def
      apply clarsimp
      apply (erule N_s_state_trans, assumption)
      apply (erule N_s_state_trans, assumption)
      unfolding equiv.state_trans_t_def
      apply clarsimp
      apply (drule collect_clock_pairs_append_cases)
      apply (erule disjE)
      subgoal for s1 p' q l'' l'aa pc_g pc_ga pc_u pc_ua
        unfolding equiv.make_c_def
          apply (clarsimp split: option.split_asm)
        apply (frule make_g_clkp_set'', assumption+)
        unfolding N_def T_def
        apply (clarsimp dest!: nth_mem)
        subgoal premises prems for j j'
        proof -
          from prems(9-) have
            "(pc_g, In a, pc_u, l[p' := l'', q := l'aa] ! p') \<in> set (trans ! p' ! (l ! p'))"
            by simp
          with prems(9-) show ?thesis by blast
        qed
        done
      subgoal for s1 q p' l'aa l'' pc_ga pc_g pc_ua pc_u
        apply (frule make_g_clkp_set'', assumption+)
        unfolding N_def T_def
        apply (clarsimp dest!: nth_mem)
        subgoal premises prems for j j'
        proof -
          from prems(9-) have
            "(pc_g, Out a, pc_u, l[q := l'aa, p' := l''] ! p') \<in> set (trans ! p' ! (l ! p'))"
            by simp
          with prems(9-) show ?thesis by blast
        qed
        done
      done
    done
qed

end (* End of context for pre-compiled reachability problem *)


abbreviation "conv B \<equiv> (conv_prog (fst B), (map conv_A' (fst (snd B))), snd (snd B))"

context UPPAAL_Reachability_Problem_precompiled
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
    using T_s_unfold_1 T_s_unfold_2 by simp

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
    apply (simp add: T_s_unfold_1[simplified] T_s_unfold_2[simplified])
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

end (* End of context for precompiled reachability problem *)


locale UPPAAL_Reachability_Problem_precompiled_ceiling =
  UPPAAL_Reachability_Problem_precompiled +
  fixes k :: "nat list list list"
  assumes k_ceiling:
    "\<forall> i < p. \<forall> l < length (trans ! i). \<forall> (x, m) \<in> clkp_set'' i l. m \<le> k ! i ! l ! x"
    "\<forall> i < p. \<forall> l < length (trans ! i). \<forall> (x, m) \<in> collect_clock_pairs (inv ! i ! l).
      m \<le> k ! i ! l ! x"
  and k_resets:
    "\<forall> i < p. \<forall> l < length (trans ! i). \<forall> (g, a, r, l') \<in> set (trans ! i ! l).
     \<forall> c \<in> {0..<m+1} - fst ` collect_store'' r. k ! i ! l' ! c \<le> k ! i ! l ! c"
  and k_length:
    "length k = p" "\<forall> i < p. length (k ! i) = length (trans ! i)"
    "\<forall> xs \<in> set k. \<forall> xxs \<in> set xs. length xxs = m + 1"
  and k_0:
    "\<forall> i < p. \<forall> l < length (trans ! i). k ! i ! l ! 0 = 0"
  and guaranteed_resets:
    "\<forall> i < p. \<forall> l < length (trans ! i). \<forall> (g, a, r, l') \<in> set (trans ! i ! l).
      guaranteed_execution_cond prog r max_steps
     "
begin

definition "k_fun l c \<equiv> if c > 0 \<and> c \<le> m then Max {k ! i ! (fst l ! i) ! c | i . i < p} else 0"


lemma p_p':
  "equiv.p = p"
  by simp

lemma clkp_set_clk_set_subs:
  "fst ` clkp_set A (l, s) \<subseteq> clk_set A"
  unfolding TA_clkp_set_unfold by auto

lemma k_ceiling_1:
  "\<forall> l. \<forall>(x,m) \<in> clkp_set A l. m \<le> k_fun l x"

  apply safe
  subgoal premises prems for l s x d (* XXX Do many of these unfolds automatically? *)
  proof -
    from \<open>(x, d) \<in> _\<close> have "0 < x" "x \<le> m"
      using clkp_set_clk_set_subs[of l s] clk_set by force+
    from prems show ?thesis
      unfolding clkp_set_def
      apply safe
      subgoal
        unfolding collect_clki_def
        unfolding inv_of_def
        unfolding equiv.defs.prod_ta_def
        unfolding equiv.defs.prod_invariant_def
        unfolding inv_of_def
          Product_TA_Defs.product_ta_def
          Product_TA_Defs.product_invariant_def
          equiv.defs.N_s_def
        unfolding length_N
        unfolding equiv.state_ta_def
        unfolding p_p'
        unfolding equiv.state_inv_def
        unfolding N_def
        unfolding collect_clock_pairs_def
        apply (clarsimp cong: if_cong simp: I_def)
        subgoal premises prems for l' i
          (* XXX Automate this single forward reasoning step away *)
        proof -
          have "nat d \<le> k ! i ! (l ! i) ! x"
            using prems lengths k_ceiling(2)
            unfolding collect_clock_pairs_def
            by (auto 4 4)
          also from \<open>_ < p\<close> have "\<dots> \<le> Max {k ! i ! (l ! i) ! x |i. i < p}"
            by (auto intro: Max_ge)
          finally show ?thesis
            unfolding k_fun_def using \<open>0 < x\<close> \<open>x \<le> m\<close> by auto
        qed
        done
      subgoal
        unfolding collect_clkt_def
        apply clarsimp
        subgoal premises prems for g a r l' s'
        proof -
          from guard_approx[OF prems(2)] prems(1) obtain i g a r where *:
            "(x, d) \<in> clkp_set'' i (l ! i)" "(g, a, r, l' ! i) \<in> set (trans ! i ! (l ! i))"
            "l \<in> equiv.defs.states' s" "i < p"
            by auto
          from \<open>i < p\<close> \<open>l \<in> _\<close> have "l ! i < length (trans ! i)"
            by auto
          with k_ceiling(1) * have "nat d \<le> k ! i ! (l ! i) ! x"
            by force
          also from \<open>_ < p\<close> have "\<dots> \<le> Max {k ! i ! (l ! i) ! x |i. i < p}"
            by (auto intro: Max_ge)
          finally show ?thesis
            unfolding k_fun_def using \<open>0 < x\<close> \<open>x \<le> m\<close> by auto
        qed
        done
      done
  qed
done

lemma k_ceiling_2:
    "\<forall> l g a r l' c. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> c \<notin> set r \<longrightarrow> k_fun l' c \<le> k_fun l c"
  unfolding trans_of_def equiv.defs.prod_ta_def equiv.defs.prod_trans_def
  apply clarsimp
  apply safe
  subgoal premises prems for l s g a r l' s' c
  proof -
    from prems obtain p' l'' pc_g pc_u where *:
      "p' < p" "l' = l[p' := l'']"
      "r = equiv.make_f pc_u s" "Some s' = equiv.make_mf pc_u s"
      "(l ! p', pc_g, Sil a, pc_u, l'') \<in> fst (equiv.N ! p')"
      "l \<in> equiv.defs.states' s"
      apply atomize_elim
      unfolding equiv.defs.prod_trans_i_def
      unfolding Product_TA_Defs.product_ta_def Product_TA_Defs.product_trans_def trans_of_def
      apply clarsimp
      apply safe
      unfolding Product_TA_Defs.product_trans_i_def
      unfolding trans_of_def
       apply clarsimp
      unfolding equiv.defs.N_s_def
      unfolding equiv.defs.T_s_def
      unfolding Equiv_TA_Defs.state_ta_def
      unfolding equiv.state_trans_t_def
      unfolding Product_TA_Defs.product_trans_s_def
      by auto
    from \<open>l \<in> _\<close> have [simp]: "length l = p"
      by simp
    from \<open>r = _\<close> have "fst ` collect_store'' pc_u \<subseteq> set r"
      supply find_resets_start.simps[simp del]
      unfolding collect_store''_def equiv.make_f_def
      apply (clarsimp split: option.split_asm)
      subgoal
        using \<open>Some s' = _\<close> unfolding equiv.make_mf_def
        by (auto split: option.split_asm)
      subgoal premises prems for pc' g st f pcs c d pc_t pc''
      proof -
        from prems have
          "steps (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None)) max_steps
            (pc_u, [], s, True, []) (pc', g, st, f, r)"
          "prog ! pc' = Some (INSTR HALT)"
          unfolding PF_unfold stripfp_def N_def PROG_def
          by (auto dest!: exec_steps split: if_split_asm elim!: stripf.elims)
        with prems show ?thesis
          by (force intro: sym dest!: resets_start')
      qed
      done
    with \<open>c \<notin> _\<close> have "c \<notin> fst ` collect_store'' pc_u" by blast
    show ?thesis
    proof (cases "c > m")
      case True
      then show ?thesis
        unfolding k_fun_def by auto
    next
      case False
      with \<open>c \<notin> fst ` _ _\<close> have "c \<in> {0..<m+1} - fst ` collect_store'' pc_u"
        by auto
      from * have "(l ! p') < length (trans ! p')"
        unfolding N_def T_def by auto
      from * have "(pc_g, Sil a, pc_u, l'') \<in> set (trans ! p' ! (l ! p'))"
        "(l ! p') < length (trans ! p')"
        unfolding N_def T_def by auto
      with k_resets \<open>c \<in> _\<close> \<open>p' < _\<close> have "k ! p' ! l'' ! c \<le> k ! p' ! (l ! p') ! c"
        unfolding k_fun_def by force
      with \<open>l' = _\<close> show ?thesis
        unfolding k_fun_def
        apply clarsimp
        apply (rule Max.boundedI)
          apply force
        using p_gt_0 apply force
        apply clarsimp
        subgoal for i
          apply (cases "i = p'")
           apply simp
           apply (rule le_trans)
          by (auto intro: Max_ge)
        done
    qed
  qed
  subgoal premises prems for l s g a r l' s' c
  proof -
    from prems obtain p1 l1 pc_g1 pc_u1 p2 l2 pc_g2 pc_u2 s'' where *:
      "p1 < p" "p2 < p" "l' = l[p1 := l1, p2 := l2]"
      "r = equiv.make_f pc_u1 s @ equiv.make_f pc_u2 s"
      "Some s' = equiv.make_mf pc_u1 s''" "Some s'' = equiv.make_mf pc_u2 s"
      "(l ! p1, pc_g1, In a, pc_u1, l1) \<in> fst (equiv.N ! p1)"
      "(l ! p2, pc_g2, Out a, pc_u2, l2) \<in> fst (equiv.N ! p2)"
      "l \<in> equiv.defs.states' s"
      apply atomize_elim
      unfolding equiv.defs.prod_trans_s_def
      unfolding Product_TA_Defs.product_ta_def Product_TA_Defs.product_trans_def trans_of_def
      apply clarsimp
      apply safe
      subgoal
        unfolding Product_TA_Defs.product_trans_i_def
        by auto
      unfolding Product_TA_Defs.product_trans_s_def
      unfolding trans_of_def
      apply clarsimp
      unfolding equiv.defs.N_s_def
      unfolding equiv.defs.T_s_def
      unfolding Equiv_TA_Defs.state_ta_def
      unfolding equiv.state_trans_t_def
      apply clarsimp
      by blast
    from \<open>l \<in> _\<close> have [simp]: "length l = p"
      by simp
    from * have **:
      "(pc_g1, In a, pc_u1, l1) \<in> set (trans ! p1 ! (l ! p1))" "(l ! p1) < length (trans ! p1)"
      "(pc_g2, Out a, pc_u2, l2) \<in> set (trans ! p2 ! (l ! p2))" "(l ! p2) < length (trans ! p2)"
      unfolding N_def T_def by auto
    with \<open>p1 < p\<close> guaranteed_resets have guaranteed_execution:
      "guaranteed_execution_cond prog pc_u1 max_steps"
      by blast
    thm guaranteed_execution'[of prog pc_u2 max_steps]
    from \<open>r = _\<close> have "fst ` collect_store'' pc_u1 \<subseteq> set r"
      supply find_resets_start.simps[simp del]
      unfolding collect_store''_def
        equiv.make_f_def
      apply (clarsimp split: option.split_asm)
      subgoal
        using \<open>Some s'' = _\<close> unfolding equiv.make_mf_def
        by (auto split: option.split_asm)
      subgoal
        using \<open>Some s'' = _\<close> unfolding equiv.make_mf_def
        by (auto split: option.split_asm)
      subgoal
        using \<open>Some s' = _\<close> unfolding equiv.make_mf_def
        using guaranteed_execution'[OF guaranteed_execution, of "[]" s True "[]" "[]"]
        unfolding stripfp_def PROG_def by auto
      subgoal premises prems for _ _ _ _ r2 _ pc' g st f r1 pcs c d pc_t pc''
      proof -
        from prems have
          "steps (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None)) max_steps
            (pc_u1, [], s, True, []) (pc', g, st, f, r1)"
          "prog ! pc' = Some (INSTR HALT)" "r = r1 @ r2"
          unfolding PF_unfold stripfp_def N_def PROG_def
          by (auto dest!: exec_steps split: if_split_asm elim!: stripf.elims)
        with prems show ?thesis
          by (force intro: sym dest!: resets_start')
      qed
      done
    moreover from \<open>r = _\<close> have "fst ` collect_store'' pc_u2 \<subseteq> set r"
      supply find_resets_start.simps[simp del]
      unfolding collect_store''_def
        equiv.make_f_def
      apply (clarsimp split: option.split_asm)
      subgoal
        using \<open>Some s'' = _\<close> unfolding equiv.make_mf_def
        by (auto split: option.split_asm)
      subgoal
        using \<open>Some s'' = _\<close> unfolding equiv.make_mf_def
        by (auto split: option.split_asm)
      subgoal
        using \<open>Some s' = _\<close> unfolding equiv.make_mf_def
        using guaranteed_execution'[OF guaranteed_execution, of "[]" s True "[]" "[]"]
        unfolding stripfp_def PROG_def by auto
      subgoal premises prems for pc' g st f r1 pcs _ _ _ _ r2 _ c d pc_t pc''
      proof -
        from prems have
          "steps (map_option stripf o (\<lambda>pc. if pc < size prog then prog ! pc else None)) max_steps
            (pc_u2, [], s, True, []) (pc', g, st, f, r1)"
          "prog ! pc' = Some (INSTR HALT)" "r = r2 @ r1"
          unfolding PF_unfold stripfp_def N_def PROG_def
          by (auto dest!: exec_steps split: if_split_asm elim!: stripf.elims)
        with prems show ?thesis
          by (force intro: sym dest!: resets_start')
      qed
      done
    ultimately have c_not_elem: "c \<notin> fst ` collect_store'' pc_u1" "c \<notin> fst ` collect_store'' pc_u2"
      using \<open>c \<notin> _\<close> by auto
    show ?thesis
    proof (cases "c > m")
      case True
      then show ?thesis
        unfolding k_fun_def by auto
    next
      case False
      with c_not_elem have
        "c \<in> {0..<m+1} - fst ` collect_store'' pc_u1"
        "c \<in> {0..<m+1} - fst ` collect_store'' pc_u2"
        by auto
      with ** k_resets \<open>p1 < _\<close> \<open>p2 < _\<close> have
        "k ! p1 ! l1 ! c \<le> k ! p1 ! (l ! p1) ! c" "k ! p2 ! l2 ! c \<le> k ! p2 ! (l ! p2) ! c"
        by (auto split: prod.split_asm)
      with \<open>l' = _\<close> show ?thesis
        unfolding k_fun_def
        apply clarsimp
        apply (rule Max.boundedI)
          apply force
        using p_gt_0 apply force
        apply clarsimp
        subgoal for i
          apply (cases "i = p2")
          subgoal
            apply simp
            apply (rule le_trans)
            by (auto intro: Max_ge)
          apply (cases "i = p1")
           apply simp
           apply (rule le_trans)
          by (auto intro: Max_ge)
        done
    qed
  qed
  done

lemma
  shows k_ceiling':
    "\<forall> l. \<forall>(x,m) \<in> clkp_set A l. m \<le> k_fun l x"
    "\<forall> l g a r l' c. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> c \<notin> set r \<longrightarrow> k_fun l' c \<le> k_fun l c"
  and k_bound':
    "\<forall> l. \<forall> i > m. k_fun l i = 0"
  and k_0':
    "\<forall> l. k_fun l 0 = 0"
  using k_ceiling_1 k_ceiling_2 unfolding k_fun_def by auto

sublocale Reachability_Problem A "(init, s\<^sub>0)" m k_fun "PR_CONST (\<lambda> (l, s). F l s)"
  by (standard; rule k_ceiling' k_bound' k_0')

end (* End of context for precompiled reachability problem with ceiling *)


locale UPPAAL_Reachability_Problem_precompiled_start_state =
  UPPAAL_Reachability_Problem_precompiled _ _ _ _ pred
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

  lemma [intro]:
    "bounded defs'.B s\<^sub>0"
    using bounded unfolding bounded_def N_def by simp

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
    "map trans_of (map conv_A (fst N)) = map ((`) conv_t) (map trans_of (fst N))"
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
  UPPAAL_Reachability_Problem_precompiled_ceiling +
  assumes action_set:
    "\<forall> T \<in> set trans. \<forall> xs \<in> set T. \<forall> (_, a, _) \<in> set xs. pred_act (\<lambda> a. a < na) a"
begin

  (* XXX Why are we re-doing this here? *)
  sublocale Reachability_Problem_Impl_Defs _ _ A "(init, s\<^sub>0)" m k_fun "PR_CONST (\<lambda> (l, s). F l s)" .

  definition
    "states' = {(L, s). L \<in> equiv.defs.states' s \<and> check_pred L s \<and> length s = length bounds}"

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

  lemma bounded'_bounded:
    "bounded' s \<longleftrightarrow> bounded bounds s" if "length s = length bounds"
    using that unfolding bounded'_def bounded_def by simp

  lemma bounded_bounded':
    "bounded bounds s \<Longrightarrow> bounded' s"
    unfolding bounded'_def bounded_def by simp

  lemma P_unfold:
    "(\<forall>q<p. (equiv.defs.P ! q) (L ! q) s) \<longleftrightarrow> (check_pred L s)" if "length s = length bounds"
    unfolding equiv.state_ta_def equiv.state_pred_def check_pred_def using process_length(3) that
    apply simp
    unfolding list_all_iff
    unfolding N_def
    unfolding runf_def P_def
      apply safe
     apply (auto split: option.split simp: bounded'_bounded; auto split: option.split_asm; fail)
    by (force split: option.splits simp: bounded'_bounded)

  lemma P_unfold_1:
    "(\<forall>q<p. (equiv.defs.P ! q) (L ! q) s) \<Longrightarrow> (check_pred L s)"
    unfolding equiv.state_ta_def equiv.state_pred_def check_pred_def using process_length(3)
    apply simp
    unfolding list_all_iff
    unfolding N_def
    unfolding runf_def P_def
    by (auto split: option.split simp: bounded_bounded'; auto split: option.split_asm; fail)

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
              using prems(3) by (auto intro: P_unfold_1)
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
              using prems(5) by (auto intro: P_unfold_1)
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
                by auto (force simp: set_map_filter)
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
            apply (subst P_unfold, assumption)
            apply (subst P_unfold)
            subgoal
              unfolding runf_def by (auto dest!: exec_state_length)
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
              "(L, g, (a, Networks.label.Act (equiv.make_c pc_g, equiv.make_mf pc_u)), r, L')
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
          apply (subst P_unfold)
          subgoal
            using prems(1) by fast
          apply (subst P_unfold)
          subgoal
            using \<open>runf _ _ = _\<close> prems(1)
            unfolding runf_def by (auto dest!: exec_state_length)
          using prems(1) by (force simp: make_mf_simp dest: make_c_simp)
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
     apply (subst (asm) last_product_state_indep[simplified]; force)
    by (subst (asm) last_product_state_indep[simplified]; force)

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


context UPPAAL_Reachability_Problem_precompiled'
begin

  lemma bounded_bounded'':
    "bounded bounds s \<Longrightarrow> length s = length bounds"
    unfolding bounded'_def bounded_def by simp

  lemma P_bounded:
    "(\<forall>q<p. (equiv.defs.P ! q) (L ! q) s) \<Longrightarrow> bounded bounds s"
    unfolding equiv.state_ta_def equiv.state_pred_def check_pred_def using process_length(3) p_gt_0
    apply simp
    unfolding list_all_iff
    unfolding N_def
    unfolding runf_def P_def
    apply (drule spec[of _ 0])
    by (auto split: option.split dest: bounded_bounded''; auto split: option.split_asm)

  lemma P_state_length:
    "(\<forall>q<p. (equiv.defs.P ! q) (L ! q) s) \<Longrightarrow> length s = length bounds"
    by (intro P_bounded bounded_bounded'')

  lemma state_set_state_length:
    "length s = length bounds" if "(L, s) \<in> state_set (trans_of A)"
    using that unfolding state_set_def
    apply (safe dest!: equiv.defs.prod_ta_cases)
    unfolding equiv.defs.prod_trans_i_alt_def equiv.defs.prod_trans_s_alt_def
    by safe (auto dest: P_state_length)

  lemma state_set_states:
    "state_set (trans_of A) \<subseteq> states'"
    using state_set_states' state_set_pred unfolding states'_def
    by (auto intro: P_unfold_1 state_set_state_length)

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
    by (fastforce split: option.split intro: bounded_bounded')

  lemma start_states':
    "(init, s\<^sub>0) \<in> states'"
    using start_pred' init_states bounded unfolding states'_def bounded_def by auto

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
    "(inv_fun, inv_of A) \<in> inv_rel Id states'"
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
    "(a, b) \<in> inv_rel Id B" if "(a, b) \<in> inv_rel Id C" "B \<subseteq> C"
    using that unfolding inv_rel_def b_rel_def fun_rel_def by auto

  lemma inv_fun_inv_of[intro, simp]:
    "(inv_fun, inv_of A) \<in> inv_rel Id states"
    using inv_fun_inv_of' states_states' by (rule inv_rel_mono)

  definition "final_fun \<equiv> \<lambda> (L, s). hd_of_formula formula L s"

  lemma final_fun_final':
    "(final_fun, (\<lambda> (l, s). F l s)) \<in> inv_rel Id states'"
    unfolding F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
     by (force dest!: states'_states')

  lemma final_fun_final[intro, simp]:
    "(final_fun, (\<lambda> (l, s). F l s)) \<in> inv_rel Id states"
    using final_fun_final' states_states' by (rule inv_rel_mono)

  lemma fst_clkp_setD:
    assumes "(c, d) \<in> clkp_set A l"
    shows "c > 0" "c \<le> m" "d \<in> range int"
    using assms clock_set consts_nats clkp_set'_subs
    unfolding Nats_def clk_set'_def TA_clkp_set_unfold by force+

  lemma init_has_trans:
    "(init, s\<^sub>0) \<in> fst ` (trans_of A) \<longleftrightarrow> trans_fun (init, s\<^sub>0) \<noteq> []"
    apply standard
    using trans_fun_trans_of unfolding transition_rel_def apply force
    using trans_fun_trans_of' start_states' unfolding transition_rel_def by fast

end (* End of context *)

context UPPAAL_Reachability_Problem_precompiled'
begin

  abbreviation "k_i \<equiv> IArray (map (IArray o (map (IArray o map int))) k)"

  definition
    "k_impl \<equiv> \<lambda> (l, _). IArray (map (\<lambda> c. Max {k_i !! i !! (l ! i) !! c | i. i < p}) [0..<m+1])"

  lemma k_impl_alt_def:
    "k_impl =
    (\<lambda> (l, _). IArray (map (\<lambda> c. Max ((\<lambda> i. k_i !! i !! (l ! i) !! c) ` {0..<p})) [0..<m+1]))"
  proof -
    have "{i. i < p} = {0..<p}"
      by auto
    then show ?thesis unfolding k_impl_def setcompr_eq_image by auto
  qed

  lemma k_length_alt:
    "\<forall> i < p. \<forall> j < length (k ! i). length (k ! i ! j) = m + 1"
    using k_length(1,3) by (auto dest: nth_mem)

  lemma Max_int_commute:
    "int (Max S) = Max (int ` S)" if "finite S" "S \<noteq> {}"
    apply (rule mono_Max_commute)
      apply rule
    using that by auto

  lemma [intro]:
    "k_impl (l, s) = IArray (k' (l, s))" if
    "(l, s) \<in> states'"
  proof -
    have l_len[simp]: "l ! i < length (trans ! i)" if "i < p" for i
      using \<open>i < p\<close> \<open>(l, s) \<in> _\<close> by auto thm states_len
    have *: "k_i !! i !! (l ! i) !! c = k ! i ! (l ! i) ! c"
      if "c \<le> m" "i < p" for c i
    proof -
      from k_length_alt that k_length(1,2) have "length (k ! i ! (l ! i)) = m + 1"
        by auto
      with that k_length process_length(2) processes_have_trans start_has_trans show ?thesis
        unfolding init_def by auto
    qed
    show ?thesis
      unfolding k_impl_def k'_def k_fun_def

      apply clarsimp
      apply safe
      subgoal
        apply (subst Max_int_commute)
        subgoal
          by auto
        subgoal
          using p_gt_0 by auto
        apply (rule arg_cong[where f = Max])
        apply safe
        using * apply (auto; fail)
        by (auto simp add: *[symmetric]; fail)

      subgoal
        apply (rule Max_eqI)
          apply (auto; fail)
        using k_length_alt k_length processes_have_trans k_0 p_gt_0 unfolding init_def
         apply (auto; fail)

        using k_length_alt k_length processes_have_trans k_0 p_gt_0 unfolding init_def
        apply clarsimp
        apply (rule exI[where x = 0])
        by simp

      subgoal
        apply (subst Max_int_commute)
        subgoal
          by auto
        subgoal
          using p_gt_0 by auto
        apply (rule arg_cong[where f = Max])
        apply safe
        using * apply (auto; fail)
        by (auto simp add: *[symmetric]; fail)
      done
  qed

  lemma [intro]:
    "k_impl (l, s) = IArray (k' (l, s))" if
    "(l, s) \<in> Normalized_Zone_Semantics_Impl_Refine.state_set (trans_of A)"
    using that states_states' by auto

  lemma [intro]:
    "k_impl (init, s\<^sub>0) = IArray (k' (init, s\<^sub>0))"
    using states_states' by auto

  sublocale impl:
    Reachability_Problem_Impl
    where trans_fun = trans_fun
    and trans_impl = trans_fun
    and inv_fun = inv_fun
    and F_fun = final_fun
    and ceiling = k_impl
    and A = A
    and l\<^sub>0 = "(init, s\<^sub>0)"
    and l\<^sub>0i = "(init, s\<^sub>0)"
    and F = "PR_CONST ((\<lambda> (l, s). F l s))"
    and n = m
    and k = k_fun
    and loc_rel = Id
    and show_clock = "show"
    and show_state = "show"
    and states' = states
    unfolding PR_CONST_def
    apply standard
           apply (fastforce simp: inv_rel_def b_rel_def)
    subgoal
      by auto (metis IdI list_rel_id_simp relAPP_def)
         by (fastforce simp: inv_rel_def b_rel_def)+

  (*
  (* XXX Unused *)
  lemma length_reachable:
  "length L' = p" if "E\<^sup>*\<^sup>* a\<^sub>0 ((L', s), u)"
  thm impl.reachable_states impl.(.reachable_def) term (.reachable)
    using states_states' impl.reachable_states[unfolded impl.(.reachable_def), OF that]
    unfolding reachable_def (* by (force simp: init_def) *)
      oops

  lemma length_steps:
  "length L' = p" if "conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>" "\<forall>c\<in>{1..m}. u c = 0"
    using that reachable_decides_emptiness'[of "(L', s')"] by (auto intro: length_reachable)
  *)

  lemma F_reachable_correct':
    "impl.op.F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
      )" if "formula = formula.EX \<phi>"
    using that E_op''.E_from_op_reachability_check[of F_rel "PR_CONST (\<lambda>(x, y). F x y)",
        unfolded F_rel_def, OF HOL.refl]
      reachability_check
    unfolding impl.E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
    unfolding F_rel_def unfolding F_def by force

  lemma PT_PT:
    "defs'.PT = equiv.PT"
    apply simp
    unfolding striptp_def
    apply (rule ext)
    apply clarsimp
    subgoal for x
      apply (cases "PROG x")
       apply (simp; fail)
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
    unfolding conv_A_def
    by (simp add: prod_invariant_conv[symmetric] prod_trans_conv[symmetric])

  lemma F_reachable_correct:
    "impl.op.F_reachable
    \<longleftrightarrow> (\<exists> L' s' u u'.
        conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
      )" if "formula = formula.EX \<phi>" "start_inv_check"
      unfolding F_reachable_correct'[OF that(1)]
      apply (subst product'.prod_correct[symmetric])
      using prod_conv p_p p_gt_0 apply simp
      using prod_conv p_p p_gt_0 apply simp
      using F_reachable_equiv[OF that(2)]
      by (simp add: F_def, simp add: that(1))

  definition
    "reachability_checker_old \<equiv>
      worklist_algo2_impl
        impl.subsumes_impl impl.a\<^sub>0_impl impl.F_impl impl.succs_impl impl.emptiness_check_impl"

  definition
    "reachability_checker' \<equiv>
       pw_impl
        (return o fst) impl.state_copy_impl impl.tracei impl.subsumes_impl impl.a\<^sub>0_impl impl.F_impl
        impl.succs_impl impl.emptiness_check_impl"

  theorem reachability_check':
    "(uncurry0 reachability_checker',
      uncurry0 (
        Refine_Basic.RETURN (\<exists> L' s' u u'.
        conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
       )
      )
     )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn" if "formula = formula.EX \<phi>"
    using impl.pw_impl_hnr_F_reachable
    unfolding reachability_checker'_def F_reachable_correct'[OF that] .

  corollary reachability_checker'_hoare:
    "<emp> reachability_checker'
    <\<lambda> r. \<up>(r = (\<exists> L' s' u u'.
        conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
        \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
       ))
    >\<^sub>t" if "formula = formula.EX \<phi>"
   apply (rule cons_post_rule)
   using reachability_check'[OF that, to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  definition reachability_checker where
    "reachability_checker \<equiv> do
      {
        init_sat \<leftarrow> impl.start_inv_check_impl;
        if init_sat then do
          { x \<leftarrow> reachability_checker';
            return (if x then REACHABLE else UNREACHABLE)
          }
        else
          return INIT_INV_ERR
      }"

  theorem reachability_check:
    "(uncurry0 reachability_checker,
      uncurry0 (
        Refine_Basic.RETURN (
          if start_inv_check
          then
            if
              (
              \<exists> L' s' u u'.
                conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
              \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
              )
            then REACHABLE
            else UNREACHABLE
          else INIT_INV_ERR
      )
     ))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn" if "formula = formula.EX \<phi>"
    apply (simp only: F_reachable_correct[OF that, symmetric] cong: if_cong)
    supply
      impl.pw_impl_hnr_F_reachable
      [unfolded reachability_checker'_def[symmetric], to_hnr, unfolded hn_refine_def,
       rule_format, sep_heap_rules]
    supply
      impl.start_inv_check_impl.refine[to_hnr, unfolded hn_refine_def, rule_format, sep_heap_rules]
    unfolding reachability_checker_def
    by sepref_to_hoare (sep_auto simp: pure_def)

  corollary reachability_checker_hoare:
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r =
        (
          if start_inv_check
          then
            if
              (
              \<exists> L' s' u u'.
                conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
              \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
              )
            then REACHABLE
            else UNREACHABLE
          else INIT_INV_ERR
      )
       )
    >\<^sub>t" if "formula = formula.EX \<phi>"
   apply (rule cons_post_rule)
   using reachability_check[OF that, to_hnr] apply (simp add: hn_refine_def)
   by (sep_auto simp: pure_def)

  (* XXX Add to standard library? Move *)
  lemma list_all_concat:
    "list_all Q (concat xxs) \<longleftrightarrow> (\<forall> xs \<in> set xxs. list_all Q xs)"
    unfolding list_all_iff by auto

  lemma inv_of_init_unfold:
    "u \<turnstile> inv_of (conv_A A) (init, s\<^sub>0) \<longleftrightarrow> (\<forall> i < p. u \<turnstile> conv_cc (inv ! i ! 0))"
  proof -
    have *: "inv_of (conv_A A) (init, s\<^sub>0) = conv_cc (equiv.defs.I' s\<^sub>0 init)"
      using equiv.defs.inv_of_simp[of init s\<^sub>0]
      unfolding inv_of_def conv_A_def by (auto split: prod.split)
    have "u \<turnstile> inv_of (conv_A A) (init, s\<^sub>0) \<longleftrightarrow> (\<forall> i < p. u \<turnstile> conv_cc (I i 0))"
      unfolding * Product_TA_Defs.inv_of_product Product_TA_Defs.product_invariant_def
      apply (simp only: product'.prod.length_L p_p_2 cong: list.map_cong_simp)
      unfolding equiv.defs.N_s_def length_N
      apply (simp cong: list.map_cong_simp)
      unfolding inv_of_def
      apply (simp cong: list.map_cong_simp)
      unfolding init_def
      apply (simp cong: list.map_cong_simp)
      unfolding Equiv_TA_Defs.state_ta_def
      apply (simp cong: list.map_cong_simp)
      unfolding equiv.state_inv_def
      unfolding N_def
      by (force simp: map_concat list_all_concat clock_val_def cong: list.map_cong_simp)
    also have "(\<forall> i < p. u \<turnstile> conv_cc (I i 0)) \<longleftrightarrow> (\<forall> i < p. u \<turnstile> conv_cc (inv ! i ! 0))"
      unfolding I_def using lengths processes_have_trans by fastforce
    finally show ?thesis .
  qed

  corollary reachability_checker_hoare':
    "<emp> reachability_checker
    <\<lambda> r. \<up>(r =
        (
          if (\<forall>u. (\<forall>c\<in>{1..m}. u c = 0) \<longrightarrow> (\<forall> i < p. u \<turnstile> conv_cc (inv ! i ! 0)))
          then
            if
              (
              \<exists> L' s' u u'.
                conv N \<turnstile>\<^sub>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
              \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp \<phi> L' s'
              )
            then REACHABLE
            else UNREACHABLE
          else INIT_INV_ERR
      )
       )
    >\<^sub>t" if "formula = formula.EX \<phi>"
    using reachability_checker_hoare[OF that] unfolding start_inv_check_correct inv_of_init_unfold .

  subsubsection \<open>Post-processing\<close>

  schematic_goal succs_impl_alt_def:
    "impl.succs_impl \<equiv> ?impl"
    unfolding impl.succs_impl_def
    unfolding k_impl_alt_def
    apply (abstract_let
          "\<lambda> (l, _ :: int list). IArray (map (\<lambda> c. MAX i\<in>{0..<p}. k_i !! i !! (l ! i) !! c) [0..<m+1])"
          k_i
        )
    apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> (nat, int) acconstraint list" inv_fun)
    apply (abstract_let "trans_fun" trans_fun)
    unfolding inv_fun_def[abs_def] trans_fun_def[abs_def] trans_s_fun_def trans_i_fun_def trans_i_from_def
    apply (abstract_let "IArray (map IArray inv)" inv)
    apply (abstract_let "IArray (map IArray trans_out_map)" trans_out_map)
    apply (abstract_let "IArray (map IArray trans_in_map)" trans_in_map)
    apply (abstract_let "IArray (map IArray trans_in_map)" trans_in_map)
    by (rule Pure.reflexive)

  lemma reachability_checker'_alt_def':
    "reachability_checker' \<equiv>
      let
        key = return \<circ> fst;
        sub = impl.subsumes_impl;
        copy = impl.state_copy_impl;
        start = impl.a\<^sub>0_impl;
        final = impl.F_impl;
        succs = impl.succs_impl;
        empty = impl.emptiness_check_impl;
        trace = impl.tracei
      in pw_impl key copy trace sub start final succs empty"
    unfolding reachability_checker'_def by simp

  (* XXX Re-inspect these *)
  schematic_goal reachability_checker_alt_def:
    "reachability_checker \<equiv> ?impl"
    unfolding reachability_checker_def
    unfolding reachability_checker'_alt_def' impl.succs_impl_def
    unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
    unfolding
      impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
      impl.unbounded_dbm'_def unbounded_dbm_def
    unfolding k_impl_alt_def
   apply (abstract_let k_i k_i)
   apply (abstract_let "inv_fun :: nat list \<times> int list \<Rightarrow> (nat, int) acconstraint list" )
    apply (abstract_let "trans_fun" trans_fun)
      (*
    unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def trans_i_from_def
      thm inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def trans_i_from_def trans_i_map_def
   apply (abstract_let "IArray (map IArray inv)" )
   apply (abstract_let "IArray (map IArray trans_out_map)" )
   apply (abstract_let "IArray (map IArray trans_in_map)" )
   apply (abstract_let "IArray (map IArray trans_i_map)" )
  *)
   unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
   unfolding impl.F_impl_def
   unfolding final_fun_def[abs_def]
   unfolding impl.subsumes_impl_def
   unfolding impl.emptiness_check_impl_def
   unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

end (* End of locale *)

lemmas [code] = UPPAAL_Reachability_Problem_precompiled'.k_impl_def

paragraph \<open>Some post refinements\<close>
code_thms "fw_upd'"
code_thms fw_impl'
code_thms fw_impl

term dbm_add
thm fw_upd'_def[of "m :: int DBM'" k i j]

abbreviation plus_int :: "int \<Rightarrow> int \<Rightarrow> int" where
  "plus_int a b \<equiv> a + b"

fun dbm_add_int :: "int DBMEntry \<Rightarrow> int DBMEntry \<Rightarrow> int DBMEntry"
where
  "dbm_add_int \<infinity>     _      = \<infinity>" |
  "dbm_add_int _      \<infinity>     = \<infinity>" |
  "dbm_add_int (Le a) (Le b) = (Le (plus_int a b))" |
  "dbm_add_int (Le a) (Lt b) = (Lt (plus_int a b))" |
  "dbm_add_int (Lt a) (Le b) = (Lt (plus_int a b))" |
  "dbm_add_int (Lt a) (Lt b) = (Lt (plus_int a b))"

lemma dbm_add_int:
  "dbm_add = dbm_add_int"
  apply (rule ext)+
  subgoal for x y
    by (cases x; cases y) auto
  done

definition
  "fw_upd'_int m k i j =
    Refine_Basic.RETURN
     (op_mtx_set m (i, j)
       (min (op_mtx_get m (i, j)) (dbm_add_int (op_mtx_get m (i, k)) (op_mtx_get m (k, j)))))"

definition
  "fw_upd_impl_int n \<equiv> \<lambda>ai bib bia bi. do {
                      xa \<leftarrow> mtx_get (Suc n) ai (bia, bib);
                      xb \<leftarrow> mtx_get (Suc n) ai (bib, bi);
                      x \<leftarrow> mtx_get (Suc n) ai (bia, bi);
                      let e = (dbm_add_int xa xb);
                      if e < x then mtx_set (Suc n) ai (bia, bi) e else Heap_Monad.return ai
                    }"

lemma fw_upd_impl_int_eq:
  "fw_upd_impl_int = fw_upd_impl"
  unfolding fw_upd_impl_int_def fw_upd_impl_def
  unfolding dbm_add_int add
  unfolding Let_def ..

definition
  "fw_impl_int n \<equiv>
    imp_for' 0 (n + 1)
     (\<lambda>xb. imp_for' 0 (n + 1)
            (\<lambda>xd. imp_for' 0 (n + 1) (\<lambda>xf \<sigma>'''''. fw_upd_impl_int n \<sigma>''''' xb xd xf)))"

lemma fw_impl'_int:
  "fw_impl = fw_impl_int"
  unfolding fw_impl_def fw_impl_int_def
  unfolding fw_upd_impl_int_eq ..

context UPPAAL_Reachability_Problem_precompiled_defs'
begin

  definition "run_impl program pc s \<equiv> exec program max_steps (pc, [], s, True, []) []"

  lemma runf_impl:
    "runf = run_impl PF"
    unfolding runf_def run_impl_def ..

  lemma runt_impl:
    "runt = run_impl PT"
    unfolding runt_def run_impl_def ..

  definition
    "make_cconstr_impl program pcs =
    List.map_filter
     (\<lambda>pc. case program pc of None \<Rightarrow> None | Some (INSTR x) \<Rightarrow> Map.empty x
           | Some (CEXP ac) \<Rightarrow> Some ac)
     pcs"

  lemma make_cconstr_impl:
    "make_cconstr = make_cconstr_impl PROG"
    unfolding make_cconstr_def make_cconstr_impl_def ..

  definition
    "check_g_impl programf program pc s \<equiv>
    case run_impl programf pc s of None \<Rightarrow> None
    | Some ((x, xa, xb, True, xc), pcs) \<Rightarrow> Some (make_cconstr_impl program pcs)
    | Some ((x, xa, xb, False, xc), pcs) \<Rightarrow> None"

  lemma check_g_impl:
    "check_g = check_g_impl PT PROG'"
    unfolding check_g_impl_def check_g_def runt_impl PROG'_PROG make_cconstr_impl ..

  (*
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
  *)

  definition
    "make_reset_impl program m1 s \<equiv>
      case run_impl program m1 s of
        Some ((_, _, _, _, r1), _) \<Rightarrow> r1
      | None \<Rightarrow> []
    "

  lemma make_reset_impl:
    "make_reset = make_reset_impl PF"
    unfolding make_reset_def make_reset_impl_def runf_impl ..

  definition
    "check_pred_impl program bnds L s \<equiv>
    list_all
     (\<lambda>q. case run_impl program (pred ! q ! (L ! q)) s of None \<Rightarrow> False
          | Some ((x, xa, xb, f, xc), xd) \<Rightarrow>
              f \<and> (\<forall>i<length s. fst (bnds !! i) < s ! i \<and> s ! i < snd (bnds !! i)))
     [0..<p]"

  lemma check_pred_impl:
    "check_pred = check_pred_impl PF (IArray bounds)"
    unfolding check_pred_def check_pred_impl_def runf_impl bounded'_def ..

  definition
    "pairs_by_action_impl pf pt porig bnds \<equiv> \<lambda> (L, s) OUT. concat o
      map (\<lambda> (i, g1, a, m1, l1). List.map_filter
      (\<lambda> (j, g2, a, m2, l2).
        if i = j then None else
        case (check_g_impl pt porig g1 s, check_g_impl pt porig g2 s) of
          (Some cc1, Some cc2) \<Rightarrow>
          case run_impl pf m2 s of
            Some ((_, _, s1, _, r2), _) \<Rightarrow>
            case run_impl pf m1 s1 of
              Some (( _, _, s', _, _), _) \<Rightarrow>
                if check_pred_impl pf bnds (L[i := l1, j := l2]) s'
                then Some (cc1 @ cc2, a, make_reset_impl pf m1 s @ r2, (L[i := l1, j := l2], s'))
                else None
            | _ \<Rightarrow> None
          | _ \<Rightarrow> None
        | _ \<Rightarrow> None
      )
      OUT)
        "

  lemma pairs_by_action_impl:
    "pairs_by_action = pairs_by_action_impl PF PT PROG' (IArray bounds)"
    unfolding pairs_by_action_def pairs_by_action_impl_def
    unfolding check_g_impl make_reset_impl check_pred_impl runf_impl ..

  definition
    "all_actions_by_state_impl upt_p empty_ran i L \<equiv>
    fold (\<lambda>ia. actions_by_state ia (i !! ia !! (L ! ia))) upt_p empty_ran"

  lemma all_actions_by_state_impl:
    "all_actions_by_state = all_actions_by_state_impl [0..<p] (repeat [] na)"
    unfolding all_actions_by_state_def all_actions_by_state_impl_def ..

  definition
    "trans_i_from_impl programf programt program bnds trans_i_array \<equiv>
    \<lambda>(L, s) i.
       List.map_filter
        (\<lambda>(g, a, m, l').
            case check_g_impl programt program g s of None \<Rightarrow> None
            | Some cc \<Rightarrow>
                case run_impl programf m s of None \<Rightarrow> None
                | Some ((xx, xa, s', xb, r), xc) \<Rightarrow>
                    if check_pred_impl programf (IArray bounds) (L[i := l']) s'
                    then Some (cc, a, r, L[i := l'], s') else None)
        (trans_i_array !! i !! (L ! i))"

  lemma trans_i_from_impl:
    "trans_i_from = trans_i_from_impl PF PT PROG' (IArray bounds) (IArray (map IArray trans_i_map))"
    unfolding trans_i_from_def trans_i_from_impl_def
    unfolding check_g_impl runf_impl check_pred_impl ..

end

context UPPAAL_Reachability_Problem_precompiled'
begin

  lemma PF_alt_def:
    "PF = (\<lambda> pc. if pc < length prog then (IArray (map (map_option stripf) prog)) !! pc else None)"
    unfolding stripfp_def PROG'_def by auto

  lemma PT_alt_def:
    "PT = (\<lambda> pc. if pc < length prog then (IArray (map (map_option stript) prog)) !! pc else None)"
    unfolding striptp_def PROG'_def by auto

  thm inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def trans_i_from_def trans_i_map_def

  thm check_g_impl_def runf_impl check_pred_impl_def check_pred_def

  schematic_goal reachability_checker_alt_def_refined:
    "reachability_checker \<equiv> ?impl"
    unfolding reachability_checker_alt_def
    unfolding fw_impl'_int
    unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def
    unfolding trans_i_from_impl
    unfolding runf_impl runt_impl check_g_impl pairs_by_action_impl check_pred_impl
    apply (abstract_let "IArray (map IArray inv)" inv)
    apply (abstract_let "IArray (map IArray trans_out_map)" trans_out_map)
    apply (abstract_let "IArray (map IArray trans_in_map)" trans_in_map)
    apply (abstract_let "IArray (map IArray trans_i_map)" trans_i_map)
    apply (abstract_let "IArray bounds" bounds)
    apply (abstract_let PF PF)
    apply (abstract_let PT PT)
    unfolding PF_alt_def PT_alt_def
    apply (abstract_let PROG' PROG')
    unfolding PROG'_def
    apply (abstract_let "length prog" len_prof)
    apply (abstract_let "IArray (map (map_option stripf) prog)" prog_f)
    apply (abstract_let "IArray (map (map_option stript) prog)" prog_t)
    apply (abstract_let "IArray prog" prog)
    unfolding all_actions_by_state_impl
    apply (abstract_let "[0..<p]")
    apply (abstract_let "[0..<na]")
    apply (abstract_let "{0..<p}")
    apply (abstract_let "[0..<m+1]")
    by (rule Pure.reflexive)

end (* End of precompiled' locale context *)

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

  (*
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

  *)

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
      \<and> p > 0 \<and> m > 0
      \<and> (\<forall> i < p. trans ! i \<noteq> []) \<and> (\<forall> q < p. trans ! q ! 0 \<noteq> [])
      \<and> check_nat_subs \<and> clk_set' = {1..m}
      \<and> check_resets
      "

  lemma finite_clkp_set'[intro, simp]:
    "finite clkp_set'"
    unfolding clkp_set'_def
    using [[simproc add: finite_Collect]]
    by (auto intro!: finite_vimageI finite_imageI simp: inj_on_def)

  lemma check_pre:
    "UPPAAL_Reachability_Problem_precompiled p m inv pred trans prog \<longleftrightarrow> check_pre"
    unfolding
      UPPAAL_Reachability_Problem_precompiled_def
      check_pre_def check_nat_subs check_resets_def
    by auto

end (* End of definitions context for precompiled reachachability problem*)


context UPPAAL_Reachability_Problem_precompiled_defs
begin

context
  fixes k :: "nat list list list"
begin

  definition
    "check_ceiling \<equiv>
    UPPAAL_Reachability_Problem_precompiled_ceiling_axioms p m max_steps inv trans prog k"

  lemma check_axioms:
    "UPPAAL_Reachability_Problem_precompiled_ceiling p m max_steps inv pred trans prog k
    \<longleftrightarrow> check_pre \<and> check_ceiling"
    unfolding UPPAAL_Reachability_Problem_precompiled_ceiling_def check_pre check_ceiling_def
    by auto

end

end

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.collect_cexp_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.collect_store_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.check_resets_alt_def

export_code UPPAAL_Reachability_Problem_precompiled_defs.collect_cexp in SML module_name Test

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs.check_pre
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
  uses UPPAAL_Reachability_Problem_precompiled'.reachability_checker_alt_def_refined

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

context UPPAAL_Reachability_Problem_precompiled_defs
begin

  lemma collect_store''_alt_def:
    "collect_store'' pc \<equiv>
    case find_resets_start prog pc of
      None \<Rightarrow> {} |
      Some pc' \<Rightarrow>
        \<Union> (
          (\<lambda> cmd. case cmd of Some (INSTR (STOREC c x)) \<Rightarrow> {(c, x)} | _ \<Rightarrow> {}) `
            ((!) prog) ` {pc .. pc'}
        )"
    unfolding collect_store''_def
    apply (rule eq_reflection)
    apply (auto simp del: find_resets_start.simps split: option.split_asm)
    by (auto intro: sym intro!: bexI split: option.split instrc.split_asm instr.split_asm
        simp del: find_resets_start.simps
        )

  lemma collect_cexp'_alt_def:
    "collect_cexp' pc \<equiv>
      \<Union> ((\<lambda> cmd. case cmd of Some (CEXP ac) \<Rightarrow> {ac} | _ \<Rightarrow> {}) `
          ((!) prog) ` steps_approx max_steps prog pc
      )"
    unfolding collect_cexp'_def
    by (auto 4 3 intro!: eq_reflection bexI intro: sym split: option.splits instrc.split_asm)

end

lemmas [code] =
  UPPAAL_Reachability_Problem_precompiled_defs'.PROG'_def
  UPPAAL_Reachability_Problem_precompiled_start_state_def
  UPPAAL_Reachability_Problem_precompiled_ceiling_axioms_def
  UPPAAL_Reachability_Problem_precompiled_defs.N_def
  UPPAAL_Reachability_Problem_precompiled_defs.collect_store''_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs.clkp_set''_def
  UPPAAL_Reachability_Problem_precompiled_defs.collect_cexp'_alt_def
  UPPAAL_Reachability_Problem_precompiled_defs'.pairs_by_action_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.make_reset_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.check_g_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.run_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.make_cconstr_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.check_pred_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.all_actions_by_state_impl_def
  UPPAAL_Reachability_Problem_precompiled_defs'.trans_i_from_impl_def

lemmas [code] =
  Equiv_TA_Defs.state_ta_def Prod_TA_Defs.N_s_def Product_TA_Defs.states_def

export_code UPPAAL_Reachability_Problem_precompiled'_axioms in SML module_name Test

export_code UPPAAL_Reachability_Problem_precompiled' in SML module_name Test

(* export_code reachability_checker_impl in SML_imp module_name TA *)

hide_const check_and_verify

definition [code]:
  "check_and_verify p m k max_steps I T prog final bounds P s\<^sub>0 na \<equiv>
    if UPPAAL_Reachability_Problem_precompiled' p m max_steps I T prog bounds P s\<^sub>0 na k
    then
      reachability_checker_impl p m max_steps I T prog bounds P s\<^sub>0 na k final
      \<bind> (\<lambda> x. return (Some x))
    else return None"

abbreviation "N \<equiv> UPPAAL_Reachability_Problem_precompiled_defs.N"

theorem reachability_check:
  "(uncurry0 (check_and_verify p m k max_steps I T prog (formula.EX formula) bounds P s\<^sub>0 na),
    uncurry0 (
       Refine_Basic.RETURN (
        if UPPAAL_Reachability_Problem_precompiled' p m max_steps I T prog bounds P s\<^sub>0 na k
        then Some (
          if (\<forall>u. (\<forall>c\<in>{1..m}. u c = 0) \<longrightarrow> (\<forall> i < p. u \<turnstile> conv_cc (I ! i ! 0)))
            then
              if
                (
                \<exists> L' s' u u'.
                  conv (N p I P T prog bounds) \<turnstile>\<^sub>max_steps
                  \<langle>repeat 0 p, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
                \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s'
                )
              then REACHABLE
              else UNREACHABLE
            else INIT_INV_ERR
            )
        else None
       )
    )
   )
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a id_assn"
proof -
  define A where "A \<equiv> conv (N p I P T prog bounds)"
  define start_inv where
    "start_inv \<equiv> (\<forall>u. (\<forall>c\<in>{1..m}. u c = 0) \<longrightarrow> (\<forall> i < p. u \<turnstile> conv_cc (I ! i ! 0)))"
  define reach where
    "reach \<equiv>
      \<exists> L' s' u u'.
        A \<turnstile>\<^sub>max_steps
        \<langle>repeat 0 p, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
      \<and> (\<forall> c \<in> {1..m}. u c = 0) \<and> check_bexp formula L' s'"
  thm UPPAAL_Reachability_Problem_precompiled'.reachability_checker_hoare'
  thm HOL.refl[of "formula.EX formula"]
  note [sep_heap_rules] =
    UPPAAL_Reachability_Problem_precompiled'.reachability_checker_hoare'
    [ OF _ HOL.refl[of "formula.EX formula"],
      unfolded UPPAAL_Reachability_Problem_precompiled_defs.init_def,
      of p m max_steps I T prog bounds P s\<^sub>0 na k,
      unfolded A_def[symmetric] start_inv_def[symmetric] reach_def[symmetric]
    ]
  show ?thesis
    unfolding A_def[symmetric] start_inv_def[symmetric] reach_def[symmetric]
    unfolding check_and_verify_def
    by sepref_to_hoare (sep_auto simp: reachability_checker_impl.refine[symmetric])
qed

export_code open
  check_and_verify init_pred_check time_indep_check1 time_indep_check1 conjunction_check2
  checking SML_imp

end (* End of theory *)