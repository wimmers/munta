theory Generalized_Network_Language_Impl
  imports
    Simple_Network_Language_Impl 
    Generalized_Network_Language
    TA_Impl.Normalized_Zone_Semantics_Impl_Refine
    "HOL-Library.IArray" "HOL-Library.AList"
    TA_Library.More_Methods
    TA_Library.Bijective_Embedding
    TA_Impl_Misc2
    TA_More2
    TA_Equivalences
    "HOL-Eisbach.Eisbach_Tools"
    TA_Library.TA_Syntax_Bundles
    "Tag_Explorer"
begin

unbundle no_library_syntax

paragraph \<open>Default maps\<close>

definition default_map_of :: "'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "default_map_of a xs \<equiv> FinFun.map_default a (map_of xs)"

lemma default_map_of_alt_def:
  "default_map_of a xs x = (if x \<in> dom (map_of xs) then the (map_of xs x) else a)"
  unfolding default_map_of_def map_default_def by (auto split: option.split_asm)

lemma range_default_map_of:
  "range (default_map_of x xs) \<subseteq> snd ` set xs \<union> {x}"
  unfolding default_map_of_def map_default_def
  by (auto split: option.split_asm) (meson img_snd map_of_SomeD)

lemma finite_range_default_map_of:
  "finite (range (default_map_of x m))"
proof -
  have "range (default_map_of x m) \<subseteq> the ` range (map_of m) \<union> {x}"
    unfolding default_map_of_def FinFun.map_default_def
    by (auto split: option.splits) (metis image_eqI option.sel rangeI)
  also have "finite \<dots>"
    by (blast intro: finite_range_map_of)
  finally show ?thesis .
qed

lemma map_index'_inj:
  "L = L'"
  if "length L = length L'" "map_index' n f L = map_index' n g L'" "set L \<subseteq> S" "set L' \<subseteq> T"
     "\<forall> i < length L + n. \<forall> x \<in> S. \<forall>y \<in> T. f i x = g i y \<longrightarrow> x = y"
  using that
proof (induction "length L" arbitrary: L L' n)
  case 0
  then show ?case
    by simp
next
  case (Suc x)
  from Suc.prems obtain a b L1 L1' where *:
    "length L1 = x" "length L1' = x" "L = a # L1" "L' = b # L1'"
    by (smt Suc.hyps(2) length_Suc_conv)
  show ?case
    unfolding \<open>L = _\<close> \<open>L' = _\<close>
    apply (clarsimp, rule conjI)
    subgoal
      by (smt *(3,4) Suc.hyps(2) Suc.prems Suc_less_eq add_Suc_shift less_add_Suc2
            list.set_intros(1) list_tail_coinc map_index'.simps(2) set_mp)
    subgoal
      apply (rule Suc.hyps)
      using Suc.prems * by auto
    done
qed

lemma map_index_inj:
  "L = L'"
  if "map_index f L = map_index g L'" "set L \<subseteq> S" "set L' \<subseteq> T"
     "\<forall> i < length L. \<forall> x \<in> S. \<forall>y \<in> T. f i x = g i y \<longrightarrow> x = y"
  using that by - (rule map_index'_inj, auto dest: map_index_eq_imp_length_eq)

lemma map_index_inj1:
  "L = L'"
  if "map_index f L = map_index g L'"
     "\<forall> i < length L. f i (L ! i) = g i (L' ! i) \<longrightarrow> L ! i = L' ! i"
proof (intros add: nth_equalityI)
  from that(1) show \<open>length L = length L'\<close>
    by (rule map_index_eq_imp_length_eq)
  fix i :: \<open>nat\<close>
  assume \<open>i < length L\<close>
  with that have "map_index f L ! i = map_index g L' ! i"
    by auto
  with \<open>i < length L\<close> \<open>length L = length L'\<close> have "f i (L ! i) = g i (L' ! i)"
    by simp
  with \<open>i < length L\<close> that(2) show \<open>L ! i = L' ! i\<close>
    by simp
qed

lemma map_index_update:
  "map_index f (xs[i := a]) = (map_index f xs)[i := f i a]"
  by (rule nth_equalityI) (auto simp: nth_list_update')

lemma map_trans_broad_aux1:
  "map_index map_loc (fold (\<lambda>p L. L[p := ls' p]) ps L) =
  fold (\<lambda>p L. L[p := map_loc p (ls' p)]) ps (map_index map_loc L)"
  by (induction ps arbitrary: L) (auto simp: map_index_update)

lemma ComD2:
  fixes map_action
  assumes "inj map_action" "Com (map_action a) = map_act map_action a'"
  shows "a' = Com a"
  using assms(2) by (cases a')  (auto simp: injD[OF assms(1)])

lemma SilD2:
  fixes map_action
  assumes "inj map_action" "Sil (map_action a) = map_act map_action a'"
  shows "a' = Sil a"
  using assms(2) by (cases a')  (auto simp: injD[OF assms(1)])

lemma (in Prod_TA_Defs) trans_sync_tagged_def:
  "trans_sync =
    {((L, s), concat (map gs ps), Sync sync, concat (map rs ps), (L', s')) |
    sync L s L' s' bs gs as fs rs ls' ps.
      ''sync'' \<bbar> sync \<in> syncs \<and>
      ''enabled'' \<bbar> (\<forall>(p, a, b) \<in> set sync. b \<longrightarrow> p \<in> set ps) \<and>
      ''only syncs'' \<bbar> (\<forall>p < n_ps. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps) \<and>
      ''actions'' \<bbar> (\<forall>(p, a, _) \<in> set sync. as p = a) \<and>
      TRANS ''sync'' \<bbar>
        (\<forall>p \<in> set ps. (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      ''committed'' \<bbar>
        ((\<exists>p \<in> set ps. L ! p \<in> committed (N p)) \<or> (\<forall>p < n_ps. L ! p \<notin> committed (N p))) \<and>
      ''maximal'' \<bbar> (\<forall>q < n_ps. q \<notin> set ps \<longrightarrow>
        \<not> (\<exists>b g a f r l'.
            (L!q, b, g, Com a, f, r, l') \<in> trans (N q) \<and> (q, a, False) \<in> set sync
          \<and> check_bexp s b True)) \<and>
      SEL ''range'' \<bbar> set ps \<subseteq> {0..<n_ps} \<and> SEL ''sublist'' \<bbar> subseq ps (map fst sync) \<and>
      ''bexp'' \<bbar> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
      ''new loc'' \<bbar> L' = fold (\<lambda>p L . L[p := ls' p]) ps L \<and>
      ''upds''    \<bbar> is_upds_idxs s (map fs ps) s' \<and>
      L \<in> states \<and> ''bounded'' \<bbar> bounded bounds s \<and> ''bounded'' \<bbar> bounded bounds s'
    }"
  unfolding trans_sync_def by untag standard

lemma (in Prod_TA_Defs) trans_sync_alt_def:
  "trans_sync =
    {((L, s), concat (map gs ps), Sync sync, concat (map rs ps), (L', s')) |
    sync L s L' s' bs gs as fs rs ls' ps.
      ''sync'' \<bbar> sync \<in> syncs \<and>
      ''enabled'' \<bbar> (\<forall>(p, a, b) \<in> set sync. b \<longrightarrow> p \<in> set ps) \<and>
      ''only syncs'' \<bbar> (\<forall>p < n_ps. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps) \<and>
      ''actions'' \<bbar> (\<forall>(p, a, _) \<in> set sync. as p = a) \<and>
      TRANS ''sync'' \<bbar>
        (\<forall>p \<in> set ps. (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      ''committed'' \<bbar>
        ((\<exists>p \<in> set ps. L ! p \<in> committed (N p)) \<or> (\<forall>p < n_ps. L ! p \<notin> committed (N p))) \<and>
      ''maximal'' \<bbar> (\<forall>q < n_ps. q \<notin> set ps \<longrightarrow>
        \<not> (\<exists>b g a f r l'.
            (L!q, b, g, Com a, f, r, l') \<in> trans (N q) \<and> (q, a, False) \<in> set sync
          \<and> check_bexp s b True)) \<and>
      SEL ''range'' \<bbar> set ps \<subseteq> {0..<n_ps} \<and> SEL ''sublist'' \<bbar> subseq ps (map fst sync) \<and>
      ''bexp'' \<bbar> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
      ''new loc'' \<bbar> L' = fold (\<lambda>p L . L[p := ls' p]) ps L \<and>
      ''upds''    \<bbar> is_upds_idxs s (map fs ps) s' \<and>
      L \<in> states \<and> ''bounded'' \<bbar> bounded bounds s \<and> ''bounded'' \<bbar> bounded bounds s' \<and>
      ''fix conds''  \<bbar> (\<forall>p. p\<notin>set ps \<longrightarrow> bs p = bexp.true) \<and>
      ''fix guards'' \<bbar> (\<forall>p. p\<notin>set ps \<longrightarrow> gs p = []) \<and>
      ''fix upds''   \<bbar> (\<forall>p. p\<notin>set ps \<longrightarrow> fs p = []) \<and>
      ''fix resets'' \<bbar> (\<forall>p. p\<notin>set ps \<longrightarrow> rs p = [])
    }"
  unfolding trans_sync_tagged_def
proof ((intro Collect_eqI iffI; elims add: more_elims), goal_cases)
  case prems: (1 x sync L s L' s' bs gs as fs rs ls' ps)
  let ?f = "\<lambda>gs p. if p \<in> set ps then gs p else []"
  let ?bs = "\<lambda>p. if p \<in> set ps then bs p else bexp.true"
  let ?gs = "?f gs" let ?fs = "?f fs" let ?rs = "?f rs"
  have [simp]: "map gs ps = map ?gs ps" "map rs ps = map ?rs ps" "map fs ps = map ?fs ps"
    by (simp cong: map_cong)+
  with prems show ?case
    by (inst_existentials sync L s L' s' ?bs ?gs as ?fs ?rs ls' ps) (tag, (assumption | simp))+
qed blast


definition conv_automaton where
  "conv_automaton \<equiv> \<lambda>(committed, urgent, trans, inv).
    (committed,
     urgent,
     map (\<lambda>(l, b, g, a, f, r, l'). (l, b, conv_cc g, a, f, r, l')) trans,
     map (\<lambda>(s, cc). (s, conv_cc cc)) inv)"

definition automaton_of where
  "automaton_of \<equiv>
    \<lambda>(committed, urgent, trans, inv). (set committed, set urgent, set trans, default_map_of [] inv)"

locale Generalized_Network_Impl_Defs =
  fixes automata ::
    "('s list \<times> 's list \<times> ('a act, 's, 'c, 't, 'x, int) transition list
      \<times> ('s \<times> ('c, 't) cconstraint) list) list"
    and syncs :: "(nat \<times> 'a \<times> bool) list list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
begin

definition \<comment>\<open>Number of state variables\<close>
  "n_vs = length bounds'"

definition
  "B x \<equiv> if x \<in> dom (map_of bounds') then the (map_of bounds' x) else (0, 0)"

sublocale Prod_TA_Defs
  "(set syncs, map automaton_of automata, map_of bounds')" .

lemma L_len[intro, dest]:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

end

(*
locale Generalized_Network_Impl =
  Generalized_Network_Impl_Defs automata broadcast bounds
  for
    automata ::
    "('s list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) list"
  and broadcast bounds
*)

locale Generalized_Network_Impl =
  fixes automata ::
    "('s list \<times> 's list \<times> ('a act, 's, 'c, int, 'x, int) transition list
      \<times> ('s \<times> ('c, int) cconstraint) list) list"
    and syncs :: "(nat \<times> 'a \<times> bool) list list"
    and bounds' :: "('x \<times> (int \<times> int)) list"
begin

sublocale Generalized_Network_Impl_Defs automata syncs bounds' .

end


paragraph \<open>Mapping through the product construction\<close>

lemma f_the_inv_f:
  "f (the_inv f x) = x" if "inj f" "x \<in> range f"
  using that by (auto simp: the_inv_f_f)

context Generalized_Network_Impl
begin

lemma N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

(* XXX Remove? *)
lemma covn_N_eq:
  \<open>N i = automaton_of (automata ! i)\<close> if \<open>i < n_ps\<close>
  using that unfolding N_def n_ps_def fst_conv snd_conv by (intro nth_map; simp)

end

inductive_cases check_bexp_elims:
  "check_bexp s bexp.true bv"
  "check_bexp s (bexp.not b) bv"
  "check_bexp s (bexp.and b1 b2) bv"
  "check_bexp s (bexp.or b1 b2) bv"
  "check_bexp s (bexp.imply b1 b2) bv"
  "check_bexp s (le i x) bv"
  "check_bexp s (lt i x) bv"
  "check_bexp s (ge i x) bv"
  "check_bexp s (eq i x) bv"
  "check_bexp s (gt i x) bv"

inductive_cases is_val_elims:
  "is_val s (const c) d"
  "is_val s (var x)   v"
  "is_val s (if_then_else b e1 e2) v"
  "is_val s (binop f e1 e2) v"
  "is_val s (unop f e) v"

method fprem =
  (match premises in R: _ \<Rightarrow> \<open>rule R[elim_format]\<close>, assumption)

context Generalized_Network_Impl
begin

paragraph \<open>Conversion from integers to reals commutes with product construction.\<close>

sublocale conv: Prod_TA_Defs
  "(set syncs, map (Generalized_Network_Language.conv_A o automaton_of) automata, map_of bounds')" .

lemma (in -) conv_ac_inj:
  "ac = ac'" if "conv_ac ac = conv_ac ac'"
  using that by (cases ac; cases ac'; auto)

lemma (in -) conv_cc_inj:
  "cc = cc'" if "conv_cc cc = conv_cc cc'"
  using that by (subst (asm) inj_map_eq_map) (auto simp add: conv_ac_inj intro: injI)

context
begin

lemma conv_alt_def:
  "conv (set syncs, map automaton_of automata, map_of bounds') =
    (set syncs, map (Generalized_Network_Language.conv_A o automaton_of) automata, map_of bounds')"
  unfolding conv_def by simp

private lemma 2:
  "Generalized_Network_Language.conv_A o automaton_of = (\<lambda>(committed, urgent, trans, inv).
    (set committed,
     set urgent,
     set (map Generalized_Network_Language.conv_t trans),
     default_map_of [] (map (\<lambda> (l, g). (l, conv_cc g)) inv)))"
  apply (rule ext)
  apply clarsimp
  unfolding Generalized_Network_Language.conv_A_def automaton_of_def
  apply (clarsimp split: prod.split)
  unfolding default_map_of_def
  unfolding FinFun.map_default_def
  apply (rule ext)
  subgoal for xs a
    by (induction xs) auto
  done

lemma conv_n_ps_eq:
  "conv.n_ps = n_ps"
  by (simp add: Prod_TA_Defs.n_ps_def)

lemma conv_N_eq:
  "conv.N i = Generalized_Network_Language.conv_A (N i)" if "i < n_ps"
  using that unfolding n_ps_def Prod_TA_Defs.N_def fst_conv snd_conv by (subst nth_map | simp)+

private lemma 5:
  "inv (conv.N i) = conv_cc o (inv (N i))" if "i < n_ps"
  unfolding conv_N_eq[OF that] unfolding Generalized_Network_Language.conv_A_def
  by (simp split: prod.split add: inv_def)

lemma trans_conv_N_eq:
  "trans (conv.N i) = Generalized_Network_Language.conv_t ` (trans (N i))"  if "i < n_ps"
  unfolding conv_N_eq[OF that] unfolding Generalized_Network_Language.conv_A_def
  by (simp split: prod.split add: trans_def)

private lemma 71:
  "(l, b, conv_cc g, a, r, u, l')\<in>trans (conv.N i)"
  if "(l, b, g, a, r, u, l')\<in> trans (N i)" "i < n_ps"
  using that by (force simp add: trans_conv_N_eq Generalized_Network_Language.conv_t_def)

private lemma 72:
  "(l, b, conv_cc g, a, r, u, l')\<in>trans (conv.N i)
\<longleftrightarrow> (l, b, g, a, r, u, l')\<in>trans (N i)" if "i < n_ps"
  by (auto simp: trans_conv_N_eq[OF that] Generalized_Network_Language.conv_t_def
           dest: conv_cc_inj intro: image_eqI[rotated])

private lemma 73:
  "\<exists>g'. g = conv_cc g' \<and> (l, b, g', a, r, u, l')\<in>trans (N i)"
  if "(l, b, g, a, r, u, l')\<in>trans (conv.N i)" "i < n_ps"
  using that by (force simp: trans_conv_N_eq Generalized_Network_Language.conv_t_def)

lemma conv_bounds[simp]:
  "conv.bounds = bounds"
  unfolding conv.bounds_def bounds_def by simp

lemma conv_states[simp]:
  "conv.states = states"
  unfolding conv.states_def states_def conv_n_ps_eq
  by (auto simp add: trans_conv_N_eq Generalized_Network_Language.conv_t_def) (fastforce, force)

private lemma 9:
  "committed (conv.N p) = committed (N p)" if \<open>p < n_ps\<close>
  unfolding conv_N_eq[OF that] unfolding Generalized_Network_Language.conv_A_def
  by (simp split: prod.split add: committed_def)

private lemma 10:
  "conv.syncs = set syncs"
  unfolding conv.syncs_def by simp

lemma conv_trans_int:
  "conv.trans_int = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_int"
  unfolding conv.trans_int_def trans_int_def
  supply [simp] = L_len
  apply standard
  subgoal
    by (clarsimp simp: Generalized_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq 9)
      (intros add: more_intros, solve_triv+)
  subgoal
    by (rule subsetI,
        clarsimp simp: Generalized_Network_Language.conv_t_def conv_n_ps_eq trans_conv_N_eq 9[symmetric])
      ((drule (1) 71)+, intros add: more_intros, solve_triv+)
  done

lemma n_ps_rangeD:
  "p < n_ps" if "p \<in> set ps" "set ps \<subseteq> {0..<n_ps}"
  using that by auto

lemma conv_trans_sync:
  "conv.trans_sync = (\<lambda>(l, g, a, r, l'). (l, map conv_ac g, a, r, l')) ` trans_sync"
  unfolding conv.trans_sync_alt_def trans_sync_alt_def
  apply standard
  supply [simp] = L_len
  subgoal
  proof -
    have **: "\<exists> gs'. gs = conv_cc o gs' \<and>
          (\<forall>p\<in>set ps.(L ! p, bs p, gs' p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p))"
      if assms[untagged]:
        "\<forall>p\<in>set ps. (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (conv.N p)"
        "SEL ''range'' \<bar> set ps \<subseteq> {0..<n_ps}" "''fix guards'' \<bar> \<forall>p. p \<notin> set ps \<longrightarrow> gs p = []"
      for L ps bs gs as fs rs ls'
    proof -
      have *: "gs p = conv_cc (Hilbert_Choice.inv conv_cc (gs p))" if "p \<in> set ps" for p
        using that assms by (auto 4 3 simp: f_inv_into_f dest!: 73)
      show ?thesis
        apply (inst_existentials "Hilbert_Choice.inv conv_cc o gs")
        subgoal
          apply (rule ext)
          subgoal for p
            apply (cases "p \<in> set ps")
            subgoal
              by (simp, erule *)
            subgoal
              using assms(3) by (auto intro: injI inv_f_eq conv_ac_inj)
            done
          done
        subgoal
          using assms * by (force dest!: conv_cc_inj 73)
        done
    qed
    show ?thesis
      apply (rule subsetI)
      apply (clarsimp simp add: conv_n_ps_eq 9 10 syncs_def split: prod.split_asm)
      unfolding TAG_def[where t = "TRANS _"]
      apply (drule **, (tag, assumption), (tag, assumption))
      apply elims
      apply (fo_rule image_eqI[rotated])
      apply (intro CollectI exI conjI)
      apply solve_triv
      preferT \<open>''upds''\<close> \<comment> \<open>Start with this to get the right instantiation\<close>
        apply (tag, assumption)
      apply (all \<open>(tag, assumption)?\<close>)
      preferT \<open>''enabled''\<close>
        apply (tag, blast)
      preferT \<open>''actions''\<close>
        apply (tag, blast)
      preferT \<open>''committed''\<close>
        apply (tag- \<open>SEL ''range''\<close>, simp add: 9 subset_code(1); fail)
      preferT \<open>''maximal''\<close>
        apply (tag, blast dest: 71)
      preferT \<open>''fix guards''\<close>
        apply (tag, simp; fail)
      subgoal \<comment> \<open>Equation from @{thm image_eqI}\<close>
        apply (simp add: map_concat)
        done
      done
  qed
  subgoal
    apply (rule subsetI)
    apply (clarsimp simp: conv_n_ps_eq trans_conv_N_eq 10 syncs_def map_concat)
    apply (intros add: more_intros)
    apply solve_triv+
    apply (tag- \<open>SEL ''range''\<close>, subst comp_def, fast elim: 71 intro: n_ps_rangeD; fail)
    preferT \<open>''committed''\<close>
      apply (tag- \<open>SEL ''range''\<close>, simp add: 9 subset_code(1); fail)
    preferT \<open>''maximal''\<close>
      apply (tag, simp add: Generalized_Network_Language.conv_t_def, fast; fail)
    apply (tag, assumption)+
    apply (tag, simp; fail)+
  done
done

lemma conv_prod_ta:
  "conv.prod_ta = Normalized_Zone_Semantics_Impl.conv_A prod_ta"
  unfolding conv.prod_ta_def prod_ta_def
  unfolding conv.trans_prod_def trans_prod_def
  unfolding conv.prod_inv_def prod_inv_def
  unfolding conv.N_def N_def conv_n_ps_eq
  unfolding conv_A_def
  apply simp
  apply (rule conjI)
  subgoal
    unfolding image_Un
    by ((fo_rule arg_cong2)+; rule conv_trans_int conv_trans_sync)
  subgoal \<comment>\<open>Invariant\<close>
    unfolding conv.N_def N_def
    by (rule ext) (auto simp: 5 map_concat intro!: map_cong arg_cong[where f = concat])
  done

end (* Anonymous context for private lemmas *)

paragraph \<open>Fundamentals\<close>

definition "clkp_set' \<equiv>
    (\<Union> A \<in> set automata. \<Union> g \<in> set (snd (snd (snd A))). collect_clock_pairs (snd g))
  \<union> (\<Union> A \<in> set automata. \<Union> (l, b, g, _) \<in> set (fst (snd (snd A))). collect_clock_pairs g)"

definition clk_set'  where
  \<open>clk_set'  =
  fst ` clkp_set' \<union>
  (\<Union> A \<in> set automata. \<Union> (_, _, _, _, _, r, _) \<in> set (fst (snd (snd A))). set r)\<close>

lemma (in -) default_map_of_in_listD:
  "x \<in> \<Union> (set ` snd ` set invs)" if "x \<in> set (default_map_of [] invs l)"
proof -
  have "[] \<noteq> default_map_of [] invs l"
    using that by force
  then have "default_map_of [] invs l \<in> snd ` set invs"
    by (metis (no_types) UNIV_I Un_insert_right range_default_map_of[of "[]" "invs"]
          image_eqI insertE subsetCE sup_bot.right_neutral)
  with that show ?thesis
    by blast
qed

lemma collect_clock_pairs_invsI:
  "(a, b) \<in> \<Union> ((collect_clock_pairs o snd) ` set invs)"
  if "(a, b) \<in> collect_clock_pairs (default_map_of [] invs l)"
  using that unfolding collect_clock_pairs_def by (auto dest!: default_map_of_in_listD)

lemma mem_trans_N_iff:
  "t \<in> trans (N i) \<longleftrightarrow> t \<in> set (fst (snd (snd (automata ! i))))"
  if "i < n_ps"
  unfolding N_eq[OF that] by (auto split: prod.splits simp: automaton_of_def trans_def)

lemma length_automata_eq_n_ps:
  "length automata = n_ps"
  unfolding n_ps_def by simp

lemma clkp_set'_subs:
  "Timed_Automata.clkp_set prod_ta \<subseteq> clkp_set'"
  unfolding Timed_Automata.clkp_set_def clkp_set'_def
  apply (rule union_subsetI)
  subgoal
    unfolding Timed_Automata.collect_clki_def inv_of_prod prod_inv_def
    apply (auto simp: collect_clock_pairs_concat)
    apply (subst (asm) N_eq)
     apply assumption
    subgoal for a b L i
      apply (inst_existentials "automata ! i")
      subgoal
        unfolding automaton_of_def
        by (force dest!: nth_mem collect_clock_pairs_invsI
            split: prod.split_asm simp: inv_def Prod_TA_Defs.n_ps_def)
      done
    done
  subgoal
    apply simp
    unfolding trans_prod_def Timed_Automata.collect_clkt_def
    apply safe
    subgoal
      unfolding trans_int_def by (fastforce simp: length_automata_eq_n_ps mem_trans_N_iff)
    subgoal
      unfolding trans_sync_tagged_def
      by (clarsimp, tag- \<open>TRANS _\<close> \<open>SEL ''range''\<close>)
         (fastforce simp: length_automata_eq_n_ps mem_trans_N_iff collect_clock_pairs_concat)
      done
    done

lemma collect_clkvt_subs:
  "collect_clkvt (trans_of prod_ta) \<subseteq>
    (\<Union> A \<in> set automata. \<Union> (_, _, _, _, _, r, _) \<in> set (fst (snd (snd A))). set r)"
  apply simp
  unfolding collect_clkvt_def
  apply auto
  unfolding trans_prod_def
  subgoal
    apply simp
    unfolding trans_prod_def Timed_Automata.collect_clkt_def
    apply safe
    subgoal
      unfolding trans_int_def
      by (fastforce
          simp: length_automata_eq_n_ps mem_trans_N_iff
          dest!: collect_clock_pairs_append_cases)
    subgoal
      unfolding trans_sync_tagged_def
      by (clarsimp, tag- \<open>TRANS _\<close> \<open>SEL ''range''\<close>)
         (fastforce simp: length_automata_eq_n_ps mem_trans_N_iff collect_clock_pairs_concat)
    done
  done

lemma clk_set'_subs: "clk_set prod_ta \<subseteq> clk_set'"
  using collect_clkvt_subs clkp_set'_subs unfolding clk_set'_def by auto

end (* Simple Network Impl *)


lemma (in Prod_TA_Defs) finite_range_invI:
  "finite (range prod_inv)" if assms: "\<forall> i < n_ps. finite (range (inv (N i)))"
proof -
  let ?N = "\<Union> (range ` inv ` N ` {0..<n_ps})"
  let ?X = "{I. set I \<subseteq> ?N \<and> length I \<le> n_ps}"
  have "finite ?N"
    using assms by auto
  then have "finite ?X"
    by (rule finite_lists_length_le)
  moreover have "range prod_inv \<subseteq> concat ` ?X \<union> {[]}"
  proof
    fix x assume "x \<in> range prod_inv"
    then consider L where "x = concat (map (\<lambda>p. (inv (N p)) (L ! p)) [0..<n_ps])" | "x = []"
      unfolding prod_inv_def by (auto split: if_split_asm)
    then show "x \<in> concat ` ?X \<union> {[]}"
      by (cases; force)
  qed
  ultimately show ?thesis by - (drule finite_subset; auto)
qed

definition (in Prod_TA_Defs)
  "loc_set =
  (\<Union> {fst ` trans (N p) | p. p < n_ps} \<union>
        \<Union> {(snd o snd o snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p) | p. p < n_ps})"

lemma (in Prod_TA_Defs) states_loc_set:
  "states \<subseteq> {L. set L \<subseteq> loc_set \<and> length L = n_ps}"
  unfolding states_def loc_set_def
  apply (intros add: more_intros)
   apply (elims add: more_elims)
   apply (drule mem_nth)
   apply simp
   apply (elims add: allE, assumption)
   apply (simp split: prod.split_asm)
   apply (erule disjE; (intros add: disjI1 disjI2 more_intros, solve_triv+); fail)
  by (elims add: more_elims)

lemma (in Prod_TA_Defs) finite_states:
  assumes finite_trans: "\<forall>p < n_ps. finite (trans (N p))"
  shows "finite states"
proof -
  have "states \<subseteq> {L. set L \<subseteq> loc_set \<and> length L = n_ps}"
    by (rule states_loc_set)
  also from finite_trans have "finite \<dots>"
    unfolding loc_set_def by (intro finite_intros) auto
  finally show ?thesis .
qed

context Generalized_Network_Impl
begin

lemma trans_N_finite:
  assumes "p < n_ps"
  shows "finite (trans (N p))"
  using assms by (subst N_eq) (auto simp: automaton_of_def trans_def split: prod.split)

lemma states_finite:
  "finite states"
  by (intros add: finite_states trans_N_finite)

lemma bounded_finite:
  "finite {s. bounded bounds s}"
proof -
  let ?l = "Min {fst (the (bounds x)) | x. x \<in> dom bounds}"
  let ?u = "Max {snd (the (bounds x)) | x. x \<in> dom bounds}"
  have "finite (dom bounds)"
    unfolding bounds_def by simp
  then have "{s. bounded bounds s} \<subseteq> {s. dom s = dom bounds \<and> ran s \<subseteq> {?l..?u}}"
    unfolding bounded_def
    apply clarsimp
    apply (rule conjI)
    subgoal for s v
      unfolding ran_is_image
      apply clarsimp
      subgoal for x l u
        by (rule order.trans[where b = "fst (the (bounds x))"]; (rule Min_le)?; force)
      done
    subgoal for s v
      unfolding ran_is_image
      apply clarsimp
      subgoal for x l u
        by (rule order.trans[where b = "snd (the (bounds x))"]; (rule Max_ge)?; force)
      done
    done
  also from \<open>finite (dom bounds)\<close> have "finite \<dots>"
    by (rule finite_set_of_finite_maps) rule
  finally show ?thesis .
qed

lemma trans_prod_finite:
  "finite trans_prod"
proof -
  have "finite trans_int"
  proof -
    have "trans_int \<subseteq>
      {((L, s), g, Internal a, r, (L', s')) | L s p l b g a f r l' s' L'.
        L \<in> states \<and> bounded bounds s \<and> p < n_ps \<and>
        (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
        bounded bounds s'
        \<and> L' = L[p := l']
      }"
      unfolding trans_int_def by (force simp: L_len)
    also have "finite \<dots>"
    proof -
      have "finite {(a, b, c, d, e, f, g). (a, b, c, Sil d, e, f, g) \<in> trans (N p)}"
        if "p < n_ps" for p
        using [[simproc add: finite_Collect]] that
        by (auto intro: trans_N_finite finite_vimageI injI)
      with states_finite bounded_finite show ?thesis
        by defer_ex
    qed
    finally show ?thesis .
  qed
  moreover have "finite trans_sync"
  proof -
    define P where "P sync ps \<equiv> set ps \<subseteq> {0..<n_ps} \<and> subseq ps (map fst sync)"
      for ps and sync :: "(nat \<times> 'a \<times> bool) list"
    define Q where "Q as n bs gs fs rs \<equiv>
      (\<forall>p < n. \<exists> q < n_ps. \<exists> l l'. (l, bs ! p, gs ! p, as ! p, fs ! p, rs ! p, l') \<in> trans (N q)) \<and>
              length as = n \<and> length bs = n \<and> length gs = n \<and> length fs = n \<and> length rs = n"
      for as n bs gs fs rs
    define tag where "tag x = True" for x :: 's
    have Q_I: "Q (map as ps) (length ps) (map bs ps) (map gs ps) (map fs ps) (map rs ps)"
      if "set ps \<subseteq> {0..<n_ps}"
         "\<forall>p\<in>set ps. (L ! p, bs p, gs p, as p, fs p, rs p, ls' p) \<in> trans (N p)"
      for ps :: "nat list" and L as bs gs fs rs ls'
      using that unfolding Q_def by (auto 4 4 dest!: nth_mem)
    have "trans_sync \<subseteq>
      {((L, s), concat gs, Sync sync, concat rs, (L', s'')) |
      L s sync ps as bs gs fs rs L' s''.
        L \<in> states \<and> bounded bounds s \<and> \<^cancel>\<open>a \<in> set broadcast \<and>\<close> sync \<in> set syncs \<and>
        \<^cancel>\<open>p < n_ps \<and>\<close>
        \<^cancel>\<open>(l, b, g, Com a, f, r, l') \<in> trans (N p) \<and>\<close>
        P sync ps \<and>
        Q as (length ps) bs gs fs rs \<and>
        L' \<in> states \<and>
        bounded bounds s''\<^cancel>\<open> \<and>
        tag l'\<close>
    }"
      unfolding trans_sync_def syncs_def
      apply (rule subsetI)
      apply (elims add: more_elims)
      apply (intros add: more_intros)
             apply solve_triv+
         apply (unfold P_def; solve_triv)
        apply (rule Q_I; assumption)
      by (blast intro: state_preservation_updI state_preservation_fold_updI)
    also have "finite \<dots>"
    proof -
      have "finite {(a, b, c, e, f, g). (a, b, c, Com d, e, f, g) \<in> trans (N p)}"
        if "p < n_ps" for p d
        using [[simproc add: finite_Collect]] that
        by (auto intro: trans_N_finite finite_vimageI injI)
      moreover have "finite {ps. P sync ps}" for sync
        unfolding P_def by (simp add: finite_subseqs)
      moreover have "finite {(as, bs, gs, fs, rs). Q as n bs gs fs rs}" (is "finite ?S") for n
      proof -
        let ?T = "\<Union> (trans ` N ` {0..<n_ps})"
        have "?S \<subseteq> {(as, bs, gs, fs, rs).
          (set as \<subseteq> (\<lambda>(_,_,_,a,_). a) ` ?T \<and> length as = n) \<and>
          (set bs \<subseteq> (\<lambda>(_,b,_). b) ` ?T \<and> length bs = n) \<and>
          (set gs \<subseteq> (\<lambda>(_,_,g,_). g) ` ?T \<and> length gs = n) \<and>
          (set fs \<subseteq> (\<lambda>(_,_,_,_,f,_). f) ` ?T \<and> length fs = n) \<and>
          (set rs \<subseteq> (\<lambda>(_,_,_,_,_,r,_). r) ` ?T \<and> length rs = n)
        }"
          unfolding Q_def by (safe; (drule mem_nth; elims; drule spec; elims; force))
        also have "finite \<dots>"
          using trans_N_finite by (intro finite_intros more_finite_intros) auto
        finally show ?thesis .
      qed
      ultimately show ?thesis
        using states_finite bounded_finite by defer_ex
    qed
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (simp add: trans_prod_def)
qed

lemma prod_inv_finite:
  "finite (range prod_inv)"
  apply (intros add: finite_range_invI)
  unfolding length_automata_eq_n_ps[symmetric]
  unfolding N_def
  unfolding automaton_of_def
  by (auto intro: finite_range_default_map_of split: prod.split simp: inv_def)

end (* Simple Network Impl *)

paragraph \<open>Collecting variables from expressions.\<close>

definition (in Prod_TA_Defs)
  "var_set =
  (\<Union>S \<in> {(fst \<circ> snd) ` trans (N p) | p. p < n_ps}. \<Union>b \<in> S. vars_of_bexp b) \<union>
  (\<Union>S \<in> {(fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` trans (N p) | p. p < n_ps}.
    \<Union>f \<in> S. \<Union> ((x, e), _) \<in> set f. {x} \<union> vars_of_exp e)"

locale Generalized_Network_Impl_nat_defs =
  Generalized_Network_Impl automata
  for automata ::
    "(nat list \<times> nat list \<times> (nat act, nat, nat, int, nat, int) transition list
      \<times> (nat \<times> (nat, int) cconstraint) list) list" +
  fixes m :: nat and num_states :: "nat \<Rightarrow> nat" and num_actions :: nat

locale Generalized_Network_Impl_nat =
  Generalized_Network_Impl_nat_defs +
  assumes has_clock: "m > 0"
  assumes non_empty: "0 < length automata"
    (* assumes "length automata = length state_nums" *)
  assumes trans_num_states:
    "\<forall>i < n_ps. let (_, _, trans, _) = (automata ! i) in \<forall> (l, _, _, _, _, _, l') \<in> set trans.
      l < num_states i \<and> l' < num_states i"
    and inv_num_states:
    "\<forall>i < n_ps. let (_, _, _, inv) = (automata ! i) in \<forall> (x, _) \<in> set inv. x < num_states i"
  assumes var_set:
    "\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, _, _, f, _, _) \<in> set trans.
      \<forall>((x, upd), _) \<in> set f. x < n_vs \<and> (\<forall>i \<in> vars_of_exp upd. i < n_vs)"
    "\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, b, _, _, _, _, _) \<in> set trans.
      \<forall>i \<in> vars_of_bexp b. i < n_vs"
  assumes bounds:
    "\<forall> i < n_vs. fst (bounds' ! i) = i"
  assumes action_set:
    "\<forall>sync \<in> set syncs. \<forall>(p, a, b) \<in> set sync. p < length automata \<and> a < num_actions"
    "\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, _, a, _, _, _) \<in> set trans.
        pred_act (\<lambda>a. a < num_actions) a"
    "\<forall>sync \<in> set syncs. distinct (map fst sync)"
  assumes clock_set:
    "\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, g, _, _, r, _) \<in> set trans.
      (\<forall>c \<in> set r. 0 < c \<and> c \<le> m) \<and>
      (\<forall> (c, x) \<in> collect_clock_pairs g. 0 < c \<and> c \<le> m \<and> x \<in> \<nat>)
      "
    "\<forall>(_, _, _, inv) \<in> set automata. \<forall>(l, g) \<in> set inv.
      (\<forall> (c, x) \<in> collect_clock_pairs g. 0 < c \<and> c \<le> m \<and> x \<in> \<nat>)
      "
  assumes weak_synchronizations:
    "\<forall>(_, _, trans, _) \<in> set automata. \<forall>(_, _, g, a, _, _, _) \<in> set trans. \<forall>sync \<in> set syncs.
      case a of Com a \<Rightarrow> (p, a, False) \<in> set sync \<longrightarrow> g = [] | _ \<Rightarrow> True"
begin

lemma weak_synchronizations_unguarded:
  "\<forall>p < n_ps. \<forall>sync l b g a f r l'. sync \<in> set syncs \<and>
    (l, b, g, Com a, f, r, l') \<in> trans (N p) \<and> (p, a, False) \<in> set sync \<longrightarrow> g = []"
  using weak_synchronizations by (fastforce dest: nth_mem simp: n_ps_def mem_trans_N_iff)

sublocale conv: Prod_TA
  "(set syncs, map (Generalized_Network_Language.conv_A o automaton_of) automata, map_of bounds')"
  using weak_synchronizations_unguarded
  by - (standard,
        fastforce simp: conv.syncs_def Generalized_Network_Language.conv_t_def
          conv_n_ps_eq trans_conv_N_eq)

sublocale TA_Start_No_Ceiling prod_ta init m
proof standard
  show "finite (trans_of prod_ta)"
    using trans_prod_finite by simp
next
  show "finite (range (inv_of prod_ta))"
    using prod_inv_finite by simp
next
  from clk_set'_subs have "clk_set prod_ta \<subseteq> clk_set'" .
  also have "\<dots> \<subseteq> {1..m}"
    using clock_set unfolding clk_set'_def clkp_set'_def by force
  finally show "clk_set prod_ta \<subseteq> {1..m}" .
next
  from clock_set have "\<forall>(_, d)\<in>clkp_set'. d \<in> \<nat>"
    unfolding clkp_set'_def by force
  then show "\<forall>(_, d)\<in>Timed_Automata.clkp_set prod_ta. d \<in> \<nat>"
    by (auto dest!: subsetD[OF clkp_set'_subs])
next
  show "0 < m"
    by (rule has_clock)
qed

end (* Simple Network Impl nat *)


context Generalized_Network_Impl
begin

definition "sem \<equiv> (set syncs, map (automaton_of o conv_automaton) automata, map_of bounds')"

sublocale sem: Prod_TA_sem sem .

lemma sem_N_eq:
  "sem.N p = automaton_of (conv_automaton (automata ! p))" if \<open>p < n_ps\<close>
  using that unfolding sem.N_def n_ps_def unfolding sem_def fst_conv snd_conv
  by (subst nth_map) auto

end (* Simple Network Impl *)

inductive_cases step_u_elims:
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>"
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Sync sync\<^esub> \<langle>L', s', u'\<rangle>"

inductive_cases step_u_elims':
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>"
  "(broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Sync sync\<^esub> \<langle>L', s', u'\<rangle>"

lemma (in Prod_TA_Defs) states_lengthD:
  "length L = n_ps" if "L \<in> states"
  using that unfolding states_def by simp

end (* Theory *)