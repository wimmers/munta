theory Leadsto_Map
  imports Leadsto Unified_PW_Hashing Liveness_Subsumption_Map Heap_Hash_Map Next_Key
begin

definition map_to_set :: "('b \<rightharpoonup> 'a set) \<Rightarrow> 'a set" where
  "map_to_set m = (\<Union> (ran m))"

hide_const wait

definition
  "map_list_set_rel =
    {(ml, ms). dom ml = dom ms
     \<and> (\<forall> k \<in> dom ms. set (the (ml k)) = the (ms k) \<and> distinct (the (ml k)))
     \<and> finite (dom ml)
    }"

context Worklist_Map2_Defs
begin

definition
  "add_pw'_map3 passed wait a \<equiv>
   nfoldli (succs a) (\<lambda>(_, _, brk). \<not>brk)
    (\<lambda>a (passed, wait, _).
      do {
      (* ASSERT (\<forall> wait \<in> ran wait. \<forall> x \<in> set wait. \<not> empty x); *)
      RETURN (
        if empty a then
            (passed, wait, False)
        else if F' a then (passed, wait, True)
        else
          let k = key a; passed' = (case passed k of Some passed' \<Rightarrow> passed' | None \<Rightarrow> [])
          in
            if \<exists> x \<in> set passed'. a \<unlhd> x then
              (passed, wait, False)
            else
              (passed(k \<mapsto> (a # passed')), a # wait, False)
        )
      }
    )
    (passed,wait,False)"

definition
  "pw_map_inv3 \<equiv> \<lambda> (passed, wait, brk).
    \<exists> passed'. (passed, passed') \<in> map_list_set_rel \<and> pw_map_inv (passed', wait, brk)
  "

definition pw_algo_map3 where
  "pw_algo_map3 = do
    {
      if F a\<^sub>0 then RETURN (True, Map.empty)
      else if empty a\<^sub>0 then RETURN (False, Map.empty)
      else do {
        (passed, wait) \<leftarrow> RETURN ([key a\<^sub>0 \<mapsto> [a\<^sub>0]], [a\<^sub>0]);
        (passed, wait, brk) \<leftarrow> WHILEIT pw_map_inv3 (\<lambda> (passed, wait, brk). \<not> brk \<and> wait \<noteq> [])
          (\<lambda> (passed, wait, brk). do
            {
              (a, wait) \<leftarrow> take_from_list wait;
              ASSERT (reachable a);
              if empty a then RETURN (passed, wait, brk) else add_pw'_map3 passed wait a
            }
          )
          (passed, wait, False);
          RETURN (brk, passed)
      }
    }
  "

end -- \<open>Worklist Map 2 Defs\<close>

lemma map_list_set_rel_empty[refine, simp, intro]:
  "(Map.empty, Map.empty) \<in> map_list_set_rel"
  unfolding map_list_set_rel_def by auto

lemma map_list_set_rel_single:
  "(ml(key a\<^sub>0 \<mapsto> [a\<^sub>0]), ms(key a\<^sub>0 \<mapsto> {a\<^sub>0})) \<in> map_list_set_rel" if "(ml, ms) \<in> map_list_set_rel"
  using that unfolding map_list_set_rel_def by auto

context Worklist_Map2
begin

lemma refine_start[refine]:
  "(([key a\<^sub>0 \<mapsto> [a\<^sub>0]], [a\<^sub>0]), [key a\<^sub>0 \<mapsto> {a\<^sub>0}], [a\<^sub>0]) \<in> map_list_set_rel \<times>\<^sub>r Id"
  by (simp add: map_list_set_rel_single)

lemma pw_map_inv_ref:
  "pw_map_inv (x1, x2, x3) \<Longrightarrow> (x1a, x1) \<in> map_list_set_rel \<Longrightarrow> pw_map_inv3 (x1a, x2, x3)"
  unfolding pw_map_inv3_def by auto

lemma refine_aux[refine]:
  "(x1, x) \<in> map_list_set_rel \<Longrightarrow> ((x1, x2, False), x, x2, False) \<in> map_list_set_rel \<times>\<^sub>r Id \<times>\<^sub>r Id"
  by simp

lemma map_list_set_relD:
  "ms k = Some (set xs)" if "(ml, ms) \<in> map_list_set_rel" "ml k = Some xs"
  using that unfolding map_list_set_rel_def
  by clarsimp (metis (mono_tags, lifting) domD domI option.sel)

lemma map_list_set_rel_distinct:
  "distinct xs" if "(ml, ms) \<in> map_list_set_rel" "ml k = Some xs"
  using that unfolding map_list_set_rel_def by clarsimp (metis domI option.sel)

lemma map_list_set_rel_NoneD1[dest, intro]:
  "ms k = None" if "(ml, ms) \<in> map_list_set_rel" "ml k = None"
  using that unfolding map_list_set_rel_def by auto

lemma map_list_set_rel_NoneD2[dest, intro]:
  "ml k = None" if "(ml, ms) \<in> map_list_set_rel" "ms k = None"
  using that unfolding map_list_set_rel_def by auto

lemma map_list_set_rel_insert:
  "(ml, ms) \<in> map_list_set_rel \<Longrightarrow>
   ml (key a) = Some xs \<Longrightarrow>
   ms (key a) = Some (set xs) \<Longrightarrow>
   a \<notin> set xs \<Longrightarrow>
   (ml(key a \<mapsto> a # xs), ms(key a \<mapsto> insert a (set xs))) \<in> map_list_set_rel"
  apply (frule map_list_set_rel_distinct) unfolding map_list_set_rel_def by auto

lemma add_pw'_map3_ref:
  "add_pw'_map3 ml xs a \<le> \<Down> (map_list_set_rel \<times>\<^sub>r Id) (add_pw'_map2 ms xs a)"
  if "(ml, ms) \<in> map_list_set_rel" "\<not> empty a"
  using that unfolding add_pw'_map3_def add_pw'_map2_def
  apply refine_rcg
     apply refine_dref_type
     apply (simp; fail)
    apply (simp; fail)
   apply (simp; fail)
  apply (clarsimp simp: Let_def)
  apply safe
  subgoal
    by (auto dest: map_list_set_relD[OF _ sym])
  subgoal
    apply (auto split: option.split_asm)
    by (metis (mono_tags, lifting)
          map_list_set_relD map_list_set_rel_NoneD1 option.collapse option.sel option.simps(3)
        )
  subgoal premises prems for a ms x2a ml x2c
  proof (cases "ml (key a)")
    case None
    with \<open>(ml, ms) \<in> map_list_set_rel\<close> have "ms (key a) = None"
      by auto
    with None \<open>(ml, ms) \<in> map_list_set_rel\<close> show ?thesis
      by (auto intro: map_list_set_rel_single)
  next
    case (Some xs)
    from map_list_set_relD[OF \<open>(ml, ms) \<in> map_list_set_rel\<close> \<open>ml _ = _\<close>] have
      "ms (key a) = Some (set xs)"
      by auto
    moreover from prems have "a \<notin> set xs"
      by (metis Some empty_subsumes' local.eq_refl)
    ultimately show ?thesis
      using Some \<open>(ml, ms) \<in> map_list_set_rel\<close> by (auto intro: map_list_set_rel_insert)
  qed
  done

lemma pw_algo_map3_ref[refine]:
  "pw_algo_map3 \<le> \<Down> (Id \<times>\<^sub>r map_list_set_rel) pw_algo_map2"
  unfolding pw_algo_map3_def pw_algo_map2_def
  apply refine_rcg
              apply refine_dref_type
              apply (simp; fail)+
          apply (clarsimp, rule refine_aux; assumption)
  by (auto intro: add_pw'_map3_ref pw_map_inv_ref)

lemma pw_algo_map2_ref':
  "pw_algo_map2 \<le> \<Down> (bool_rel \<times>\<^sub>r map_set_rel) pw_algo"
proof -
  note pw_algo_map2_ref
  also note pw_algo_map_ref
  also note pw_algo_unified_ref
  finally show ?thesis .
qed

lemma pw_algo_map3_ref'[refine]:
  "pw_algo_map3 \<le> \<Down> (bool_rel \<times>\<^sub>r (map_list_set_rel O map_set_rel)) pw_algo"
proof -
  have [simp]:
    "((bool_rel \<times>\<^sub>r map_list_set_rel) O (bool_rel \<times>\<^sub>r map_set_rel))
    = (bool_rel \<times>\<^sub>r (map_list_set_rel O map_set_rel))"
    unfolding relcomp_def prod_rel_def by auto
  note pw_algo_map3_ref
  also note pw_algo_map2_ref'
  finally show ?thesis
    by (simp add: conc_fun_chain)
qed

end -- \<open>Worklist Map 2 Defs\<close>

lemma (in Worklist_Map2_finite) map_set_rel_finite_domI[intro]:
  "finite (dom m)" if "(m, S) \<in> map_set_rel"
  using that unfolding map_set_rel_def by auto

lemma (in Worklist_Map2_finite) map_set_rel_finiteI:
  "finite S" if "(m, S) \<in> map_set_rel"
  using that unfolding map_set_rel_def
  apply clarsimp
  apply (rule finite_Union)
   apply (auto intro: map_dom_ran_finite; fail)
  apply (auto simp: ran_def; fail)
  done

lemma (in Worklist_Map2_finite) map_set_rel_finite_ranI[intro]:
  "finite S'" if "(m, S) \<in> map_set_rel" "S' \<in> ran m"
  using that unfolding map_set_rel_def ran_def by auto

locale Leadsto_Search_Space_Key =
  A: Worklist_Map2 _ _ _ _ _ _ _ succs1 +
  Leadsto_Search_Space
  for succs1
  (*
  fixes key :: "'v \<Rightarrow> 'k"
  assumes subsumes_key[intro, simp]: "a \<preceq> b \<Longrightarrow> key a = key b" *)
begin

sublocale A': Worklist_Map2_finite a\<^sub>0 "\<lambda> _. False" "op \<preceq>" empty "op \<unlhd>" E key succs1 "\<lambda> _. False"
  by (standard; blast intro!: A.succs_correct)

interpretation B:
  Liveness_Search_Space_Key
  "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>0 "\<lambda> _. False" "op \<preceq>" "\<lambda> x. A.reachable x \<and> \<not> empty x"
  "\<lambda> _. False" succs key
  apply standard
    (* XXX This is not yet correct *)
  sorry

context
  fixes a\<^sub>1 :: 'a
begin

interpretation B':
  Liveness_Search_Space_Key_Defs
  a\<^sub>1 "\<lambda> _. False" "op \<preceq>" "\<lambda> x. A.reachable x \<and> \<not> empty x"
  "\<lambda> _. False" succs "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" key .

definition has_cycle_map where
  "has_cycle_map = B'.dfs_map"

context
  assumes "A.reachable a\<^sub>1"
begin

interpretation B':
  Liveness_Search_Space_Key
  "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>1 "\<lambda> _. False" "op \<preceq>" "\<lambda> x. A.reachable x \<and> \<not> empty x"
  "\<lambda> _. False" succs key
proof (standard, goal_cases)
  case prems: (1 a)
  interpret Subgraph_Start E a\<^sub>0 "\<lambda> a x. E a x \<and> Q x \<and> \<not> empty x"
    by standard auto
  from prems[unfolded Graph_Start_Defs.reachable_def] show ?case
    apply (subst succs_correct)
    unfolding B.G.E'_def
    including graph_automation
    using \<open>A.reachable a\<^sub>1\<close> by (auto intro: A.empty_E)
next
  case 2
  then show ?case by (rule A.finite_reachable)
next
  case (3 a b)
    (* XXX This is not yet correct *)
  then show ?case sorry
qed

lemmas has_cycle_map_ref[refine] = B'.dfs_map_dfs_refine[folded has_cycle_map_def has_cycle_def]

end (* Reachability assumption *)

end (* Second start state *)

definition outer_inv where
  "outer_inv passed done todo \<equiv> \<lambda> (r, passed').
    (r \<longrightarrow> (\<exists> a. A.reachable a \<and> \<not> empty a \<and> P a \<and> Q a \<and> reaches_cycle a))
     \<and> (\<not> r \<longrightarrow>
          (\<forall> a \<in> \<Union> done. P a \<and> Q a \<longrightarrow> \<not> reaches_cycle a)
         \<and> B.liveness_compatible passed'
         \<and> passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}
       )
  "

definition inner_inv where
  "inner_inv passed done todo \<equiv> \<lambda> (r, passed').
    (r \<longrightarrow> (\<exists> a. A.reachable a \<and> \<not> empty a \<and> P a \<and> Q a \<and> reaches_cycle a))
     \<and> (\<not> r \<longrightarrow>
          (\<forall> a \<in> done. P a \<and> Q a \<longrightarrow> \<not> reaches_cycle a)
         \<and> B.liveness_compatible passed'
         \<and> passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}
       )
  "

definition leadsto' :: "bool nres" where
  "leadsto' = do {
    (r, passed) \<leftarrow> A'.pw_algo_map2;
    let passed = ran passed;
    (r, _) \<leftarrow> FOREACHcdi (outer_inv passed) passed (\<lambda>(b,_). \<not>b)
      (\<lambda> passed' (_,acc).
          FOREACHcdi (inner_inv acc) passed' (\<lambda>(b,_). \<not>b)
            (\<lambda>v' (_,passed).
              do {
                ASSERT(A.reachable v');
                if P v' \<and> Q v' then has_cycle v' passed else RETURN (False, passed)
              }
            )
            (False, acc)
      )
      (False, {});
    RETURN r
  }"

lemma leadsto'_correct:
  "leadsto' \<le> leadsto_spec"
proof -
  define inv where
    "inv \<equiv> \<lambda> passed it (r, passed').
       (r \<longrightarrow> (\<exists> a. A.reachable a \<and> \<not> empty a \<and> P a \<and> Q a \<and> reaches_cycle a))
     \<and> (\<not> r \<longrightarrow>
          (\<forall> a \<in> passed - it. \<not> reaches_cycle a)
         \<and> B.liveness_compatible passed'
         \<and> passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}
       )
    "

  have [simp, intro]:
    "\<not> A'.F_reachable"
    unfolding A'.F_reachable_def by simp

  have B_reaches_empty:
    "\<not> empty b" if "\<not> empty a" "B.reaches a b" for a b
    using that(2,1)by induction auto

  interpret Subgraph_Start E a\<^sub>0 "\<lambda> a x. E a x \<and> Q x \<and> \<not> empty x"
    by standard auto

  have B_A_reaches:
    "A.reaches a b" if "B.reaches a b" for a b
    using that by (rule reaches)

  have reaches_iff: "B.reaches a x \<longleftrightarrow> B.G.G'.reaches a x"
    if "A.reachable a" "\<not> empty a" for a x
    unfolding reaches_cycle_def thm B.G.E'_def
    apply standard
    using that
      apply (rotate_tac 3)
     apply (induction rule: rtranclp.induct)
      apply blast
     apply rule
      apply assumption
     apply (subst B.G.E'_def)
    subgoal for a b c
      by (auto dest: B_reaches_empty)
    subgoal
      by (rule B.G.reaches)
    done

  have reaches1_iff: "B.reaches1 a x \<longleftrightarrow> B.G.G'.reaches1 a x"
    if "A.reachable a" "\<not> empty a" for a x
    unfolding reaches_cycle_def
    apply standard
    subgoal
      using that
        apply (rotate_tac 3)
      apply (induction rule: tranclp.induct)
       apply (rule tranclp.intros(1), auto simp: B.G.E'_def; fail)
      apply (
          rule tranclp.intros(2);
          auto 4 3 simp: B.G.E'_def dest:B_reaches_empty tranclp_into_rtranclp
          )
      done
    subgoal
      by (rule B.G.reaches1)
    done

  have reaches_cycle_iff: "reaches_cycle a \<longleftrightarrow> (\<exists>x. B.G.G'.reaches a x \<and> B.G.G'.reaches1 x x)"
    if "A.reachable a" "\<not> empty a" for a
    unfolding reaches_cycle_def
    apply (subst reaches_iff[OF that])
    using reaches1_iff B.G.G'_reaches_V that by blast

  have aux1:
    "\<not> reaches_cycle x"
    if
      "\<forall>a. A.reachable a \<and> \<not> empty a \<longrightarrow> (\<exists>x\<in>passed. a \<preceq> x)"
      "passed \<subseteq> {a. A.reachable a \<and> \<not> empty a}"
      "\<forall> y \<in> ran passed'. \<forall> x \<in> y. P x \<and> Q x \<longrightarrow> \<not> reaches_cycle x"
      "A.reachable x" "\<not> empty x" "P x" "Q x"
      "(passed', passed) \<in> A'.map_set_rel"
    for x passed passed'
  proof (rule ccontr, simp)
    assume "reaches_cycle x"
    from that obtain x' where x':"x' \<in> passed" "x \<preceq> x'"
      by auto
    with \<open>(_, _) \<in> _\<close> obtain y where y: "y \<in> ran passed'" "x' \<in> y"
      unfolding A'.map_set_rel_def by auto
    from x' that have "P x'" "Q x'"
      by (auto intro: P_mono Q_mono)
    with \<open>x' \<in> passed\<close> that(3) y have "\<not> reaches_cycle x'"
      by auto
    have "A.reachable x'" "\<not> empty x'"
      using \<open>x' \<in> passed\<close> that(2) A.empty_mono \<open>x \<preceq> x'\<close> that(5) by auto
    note reaches_cycle_iff' = reaches_cycle_iff[OF this] reaches_iff[OF this] reaches1_iff[OF this]
    from \<open>reaches_cycle x\<close> guess y unfolding reaches_cycle_def
      by safe
    interpret
      Subsumption_Graph_Pre_Nodes
        "op \<preceq>" A.subsumes_strictly "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>0
        "\<lambda> x. A.reachable x \<and> \<not> empty x"
      by standard (rule B.mono[simplified]; assumption)
    from \<open>B.reaches x y\<close> \<open>x \<preceq> x'\<close> \<open>B.reaches1 y y\<close> reaches_cycle_mono[OF B.finite_V] obtain y' where
      "y \<preceq> y'" "B.G.G'.reaches x' y'" "B.G.G'.reaches1 y' y'"
      apply atomize_elim
      apply (subst (asm) reaches_iff[rotated 2])
        defer
        defer
        apply (subst (asm) reaches1_iff)
          defer
          defer
      using \<open>A.reachable x\<close> \<open>\<not> empty x\<close> \<open>A.reachable x'\<close> \<open>\<not> empty x'\<close> \<open>B.reaches1 y y\<close>
      by (auto simp: B.reaches1_reaches_iff2 dest!: B.G.G'_reaches_V)
    with \<open>A.reachable x'\<close> \<open>\<not> empty x'\<close> have "reaches_cycle x'"
      unfolding reaches_cycle_iff'
      by auto
    with \<open>\<not> reaches_cycle x'\<close> show False ..
  qed

  note [refine_vcg] = A'.pw_algo_map2_correct[THEN order.trans]

  show ?thesis
    unfolding leadsto'_def leadsto_spec_def
    apply (refine_rcg refine_vcg)

      (* Input is finite 1 *)
    subgoal
      by (auto intro: map_dom_ran_finite)

      (* Outer invariant holds initially *)
      subgoal
        unfolding outer_inv_def B.liveness_compatible_def by simp

      (* Input is finite 2 *)
      subgoal
        by auto

      (* Inner invariant holds initially *)
      subgoal for x a b S1 S2 todo \<sigma> aa passed
        unfolding inner_inv_def outer_inv_def by simp

      (* Assertion *)
      subgoal
        unfolding inner_inv_def outer_inv_def A'.map_set_rel_def by auto

      (* Inner invariant is preserved *)
      subgoal for _ _ b S1 S2 xa \<sigma> aa passed S1' S2' a\<^sub>1 \<sigma>' ab passed'
        unfolding outer_inv_def
        apply clarsimp
        subgoal premises prems for p
        proof -
          from prems have "a\<^sub>1 \<in> p"
            unfolding A'.map_set_rel_def by auto
          with \<open>passed \<subseteq> _\<close> \<open>p \<subseteq> _\<close> have "A.reachable a\<^sub>1"
            by auto
          interpret B':
            Liveness_Search_Space
            "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>1 "\<lambda> _. False" "op \<preceq>"
            "\<lambda> x. A.reachable x \<and> \<not> empty x" "\<lambda> _. False" succs
          proof (standard, goal_cases)
            case prems: (1 a)
            interpret Subgraph_Start E a\<^sub>0 "\<lambda> a x. E a x \<and> Q x \<and> \<not> empty x"
              by standard auto
            from prems[unfolded Graph_Start_Defs.reachable_def] show ?case
              apply (subst succs_correct)
              unfolding B.G.E'_def
              including graph_automation
              using \<open>A.reachable a\<^sub>1\<close> by (auto intro: A.empty_E)
          next
            case 2
            then show ?case by (rule A.finite_reachable)
          qed
          from \<open>inner_inv _ _ _ _\<close> have
            "B'.liveness_compatible passed'" "passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}"
            unfolding inner_inv_def by auto
          from B'.dfs_correct[OF _ _ this] \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>p \<subseteq> _\<close> have
            "B'.dfs passed' \<le> B'.dfs_spec"
            by auto
          then show ?thesis
            unfolding has_cycle_def
            apply (rule order.trans)
            unfolding B'.dfs_spec_def
            apply clarsimp
            subgoal for r passed1
              apply (cases r)
               apply simp
              subgoal
                unfolding inner_inv_def
                using \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>p \<subseteq> _\<close>
                apply simp
                apply (inst_existentials a\<^sub>1)
                by (auto 4 3 simp: reaches_cycle_iff intro: prems)
              subgoal
                using \<open>inner_inv _ _ _ _\<close> \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>p \<subseteq> _\<close> reaches_cycle_iff
                unfolding inner_inv_def by auto
                done
              done
          qed
          done

          (* Current state filtered out *)
          subgoal for x a b S1 S2 xa \<sigma> aa ba S1a S2a xb \<sigma>' ab bb
            unfolding inner_inv_def by auto

          (* Break \<and> inner inv \<longrightarrow> outer inv *)
          subgoal for x a b S1 S2 xa \<sigma> aa ba S1a S2a \<sigma>'
            unfolding inner_inv_def outer_inv_def by auto

          (* \<not> Break \<and> inner inv \<longrightarrow> outer inv *)
          subgoal for x a b S1 S2 xa \<sigma> aa ba \<sigma>'
            unfolding inner_inv_def outer_inv_def by auto

          (* Break \<and> outer inv \<longrightarrow> cycle *)
          subgoal for x a b S1 S2 \<sigma> aa ba
            unfolding outer_inv_def by auto

          (* \<not> Break \<and> outer inv \<longrightarrow> cycle *)
          (* I \<and> \<not> b \<longrightarrow> post *)
          subgoal for x a b \<sigma> aa ba
            unfolding outer_inv_def by (auto dest!: aux1)

          done
      qed

lemma init_ref[refine]:
  "((False, Map.empty), False, {}) \<in> bool_rel \<times>\<^sub>r A'.map_set_rel"
  unfolding A'.map_set_rel_def by auto

lemma map_set_rel_id:
  "Liveness_Search_Space_Key.map_set_rel key = A'.map_set_rel"
  unfolding A'.map_set_rel_def B.map_set_rel_def ..

lemma has_cycle_map_ref'[refine]:
  assumes "(P1, P1') \<in> A'.map_set_rel" "(a, a') \<in> Id" "A.reachable a"
  shows "has_cycle_map a P1 \<le> \<Down> (bool_rel \<times>\<^sub>r A'.map_set_rel) (has_cycle a' P1')"
  using has_cycle_map_ref assms by (auto simp: map_set_rel_id)

definition leadsto_map3' :: "bool nres" where
  "leadsto_map3' = do {
    (r, passed) \<leftarrow> A'.pw_algo_map2;
    let passed = ran passed;
    (r, _) \<leftarrow> FOREACHcd passed (\<lambda>(b,_). \<not>b)
      (\<lambda> passed' (_,acc).
        do {
          passed' \<leftarrow> SPEC (\<lambda>l. set l = passed');
          nfoldli passed' (\<lambda>(b,_). \<not>b)
            (\<lambda>v' (_,passed).
              if P v' \<and> Q v' then has_cycle_map v' passed else RETURN (False, passed)
            )
            (False, acc)
        }
      )
      (False, Map.empty);
    RETURN r
  }"

definition "pw_algo_map2_copy = A'.pw_algo_map2"

lemma [refine]:
  "A'.pw_algo_map2 \<le>
    \<Down> (br id (\<lambda> (_, m). finite (dom m) \<and> (\<forall> k S. m k = Some S \<longrightarrow> finite S))) pw_algo_map2_copy"
proof -
  have [refine]:
    "(x, x') \<in> Id \<Longrightarrow>
     x' = (x1, x2) \<Longrightarrow>
     x = (x1a, x2a) \<Longrightarrow>
     A'.pw_map_inv (x1, x2, False)
    \<Longrightarrow> ((x1a, x2a, False), x1, x2, False) \<in>
        (br id (\<lambda> m. finite (dom m) \<and> (\<forall> k S. m k = Some S \<longrightarrow> finite S))) \<times>\<^sub>r Id \<times>\<^sub>r Id"
    for x x' x1 x2 x1a x2a
    by (auto simp: br_def A'.pw_map_inv_def A'.map_set_rel_def)
  show ?thesis
    unfolding pw_algo_map2_copy_def
    unfolding A'.pw_algo_map2_def
    apply refine_rcg
                  apply refine_dref_type
                  prefer 5
                  apply assumption
                 apply (assumption | (simp add: br_def; fail) | (auto simp: br_def; fail))+
    subgoal
      apply (clarsimp simp: br_def)
      subgoal premises prems
        using \<open>finite _\<close> \<open>\<forall>k S. _ \<longrightarrow> finite _\<close>
        unfolding A'.add_pw'_map2_def
        apply refine_rcg
           apply refine_dref_type
           apply (auto simp: Let_def split!: option.split)
        done
      done
    by (simp add: br_def)
qed

lemma leadsto_map3'_ref[refine]:
  "leadsto_map3' \<le> \<Down> Id leadsto'"
  unfolding leadsto_map3'_def leadsto'_def
  apply (subst (2) pw_algo_map2_copy_def[symmetric])
  apply (subst (2) FOREACHcdi_def)
  apply (subst (2) FOREACHcd_def)
  apply refine_rcg
               apply refine_dref_type
  by (auto simp: br_def intro: map_dom_ran_finite)

definition leadsto_map3 :: "bool nres" where
  "leadsto_map3 = do {
    (r, passed) \<leftarrow> A'.pw_algo_map3;
    let passed = ran passed;
    (r, _) \<leftarrow> FOREACHcd passed (\<lambda>(b,_). \<not>b)
      (\<lambda> passed' (_,acc).
          nfoldli passed' (\<lambda>(b,_). \<not>b)
            (\<lambda>v' (_,passed).
              if P v' \<and> Q v' then has_cycle_map v' passed else RETURN (False, passed)
            )
            (False, acc)
      )
      (False, Map.empty);
    RETURN r
  }"

lemma start_ref:
  "((False, Map.empty), False, Map.empty) \<in> Id \<times>\<^sub>r map_list_set_rel"
  by simp

lemma map_list_set_rel_ran_set_rel:
  "(ran ml, ran ms) \<in> \<langle>br set (\<lambda>_. True)\<rangle>set_rel" if "(ml, ms) \<in> map_list_set_rel"
  using that unfolding map_list_set_rel_def set_rel_def
  apply safe
  subgoal for x
    unfolding ran_def dom_def by force
  subgoal for x'
    unfolding ran_def by (auto dest!: A.map_list_set_relD[OF that] simp: br_def)
  subgoal
    unfolding Domain_fst br_def by auto
  done

lemma Id_list_rel_ref:
  "(x'a, x'a) \<in> \<langle>Id\<rangle>list_rel"
  by simp

lemma map_list_set_rel_finite_ran:
  "finite (ran ml)" if "(ml, ms) \<in> map_list_set_rel"
  using that unfolding map_list_set_rel_def by (auto intro: map_dom_ran_finite)

lemma leadsto_map3_ref[refine]:
  "leadsto_map3 \<le> \<Down> Id leadsto'"
  unfolding leadsto_map3_def leadsto'_def
  apply (subst (2) FOREACHcdi_def)
  apply (subst (2) FOREACHcd_def)
  apply (refine_rcg map_list_set_rel_ran_set_rel map_list_set_rel_finite_ran)
      prefer 4
    apply (rule rhs_step_bind_SPEC)
    apply (clarsimp simp: br_def; rule HOL.refl; fail)
   apply (refine_rcg Id_list_rel_ref; simp; fail)
   by auto

definition leadsto_map4 :: "bool nres" where
  "leadsto_map4 = do {
    (r, passed) \<leftarrow> A'.pw_algo_map3;
    ASSERT (finite (dom passed));
    passed \<leftarrow> ran_of_map passed;
    (r, _) \<leftarrow> nfoldli passed (\<lambda>(b,_). \<not>b)
      (\<lambda> passed' (_,acc).
          nfoldli passed' (\<lambda>(b,_). \<not>b)
            (\<lambda>v' (_,passed).
              if P v' \<and> Q v' then has_cycle_map v' passed else RETURN (False, passed)
            )
            (False, acc)
      )
      (False, Map.empty);
    RETURN r
  }"

lemma ran_of_map_ref:
  "ran_of_map m \<le> SPEC (\<lambda>c. (c, ran m') \<in> br set (\<lambda> _. True))" if "finite (dom m)" "(m, m') \<in> Id"
  using ran_of_map_correct[OF that(1)] that(2) unfolding br_def by (simp add: pw_le_iff)

lemma aux_ref:
  "(xa, x'a) \<in> Id \<Longrightarrow>
       x'a = (x1b, x2b) \<Longrightarrow> xa = (x1c, x2c) \<Longrightarrow> (x1c, x1b) \<in> bool_rel"
  by simp

definition "foo = A'.pw_algo_map3"

lemma [refine]:
  "A'.pw_algo_map3 \<le> \<Down> (br id (\<lambda> (_, m). finite (dom m))) foo"
proof -
  have [refine]:
    "(x, x') \<in> Id \<Longrightarrow>
     x' = (x1, x2) \<Longrightarrow>
     x = (x1a, x2a) \<Longrightarrow>
     A'.pw_map_inv3 (x1, x2, False)
    \<Longrightarrow> ((x1a, x2a, False), x1, x2, False) \<in> (br id (\<lambda> m. finite (dom m))) \<times>\<^sub>r Id \<times>\<^sub>r Id"
    for x x' x1 x2 x1a x2a
    by (auto simp: br_def A'.pw_map_inv3_def map_list_set_rel_def)
  show ?thesis
    unfolding foo_def
    unfolding A'.pw_algo_map3_def
    apply refine_rcg
                  apply refine_dref_type
                  prefer 5
                  apply assumption
                 apply (assumption | (simp add: br_def; fail) | (auto simp: br_def; fail))+
    subgoal
      apply (clarsimp simp: br_def)
      subgoal premises prems
        using \<open>finite _\<close>
        unfolding A'.add_pw'_map3_def
        apply refine_rcg
           apply refine_dref_type
           apply (auto simp: Let_def)
        done
      done
    by (simp add: br_def)
qed

lemma leadsto_map4_ref[refine]:
  "leadsto_map4 \<le> \<Down> Id leadsto_map3"
  unfolding leadsto_map4_def leadsto_map3_def FOREACHcd_def
  apply (subst (2) foo_def[symmetric])
  apply (refine_rcg ran_of_map_ref)
     apply refine_dref_type
     apply (simp add: br_def; fail)
    apply (simp add: br_def; fail)
   apply (rule rhs_step_bind_SPEC)
  by (auto simp: br_def)

definition leadsto_map4' :: "bool nres" where
  "leadsto_map4' = do {
    (r, passed) \<leftarrow> A'.pw_algo_map2;
    ASSERT (finite (dom passed));
    passed \<leftarrow> ran_of_map passed;
    (r, _) \<leftarrow> nfoldli passed (\<lambda>(b,_). \<not>b)
      (\<lambda> passed' (_,acc).
        do {
          passed' \<leftarrow> SPEC (\<lambda>l. set l = passed');
          nfoldli passed' (\<lambda>(b,_). \<not>b)
            (\<lambda>v' (_,passed).
              if P v' \<and> Q v' then has_cycle_map v' passed else RETURN (False, passed)
            )
            (False, acc)
        }
      )
      (False, Map.empty);
    RETURN r
  }"

lemma leadsto_map4'_ref:
  "leadsto_map4' \<le> \<Down> Id leadsto_map3'"
  unfolding leadsto_map4'_def leadsto_map3'_def FOREACHcd_def
  apply (subst (2) pw_algo_map2_copy_def[symmetric])
  apply (refine_rcg ran_of_map_ref)
     apply refine_dref_type
     apply (simp add: br_def; fail)
    apply (simp add: br_def; fail)
   apply (rule rhs_step_bind_SPEC)
  by (auto simp: br_def)

lemma leadsto_map4'_correct:
  "leadsto_map4' \<le> leadsto_spec_alt"
proof -
  note leadsto_map4'_ref
  also note leadsto_map3'_ref
  also note leadsto'_correct
  also note leadsto_spec_leadsto_spec_alt
  finally show ?thesis .
qed

end (* Leadsto Search Space Key *)

end (* Theory *)