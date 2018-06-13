theory Leadsto
  imports Liveness_Subsumption Unified_PW TA.CTL
begin

context Subsumption_Graph_Pre_Nodes
begin

context
  assumes finite_V: "finite {x. V x}"
begin

  (* XXX Duplication *)
lemma steps_cycle_mono:
  assumes "G'.steps (x # ws @ y # xs @ [y])" "x \<preceq> x'" "V x" "V x'"
  shows "\<exists> y' xs' ys'. y \<preceq> y' \<and> G'.steps (x' # xs' @ y' # ys' @ [y'])"
proof -
  let ?n  = "card {x. V x} + 1"
  let ?xs = "y # concat (replicate ?n (xs @ [y]))"
  from assms(1) have "G'.steps (x # ws @ [y])" "G'.steps (y # xs @ [y])"
    by (auto intro: Graph_Start_Defs.graphI_aggressive2)
  with G'.steps_replicate[of "y # xs @ [y]" ?n] have "G'.steps ?xs"
    by auto
  from steps_mono[OF \<open>G'.steps (x # ws @ [y])\<close> \<open>x \<preceq> x'\<close> \<open>V x\<close> \<open>V x'\<close>] obtain ys where
    "G'.steps (x' # ys)" "list_all2 (\<preceq>) (ws @ [y]) ys"
    by auto
  then obtain y' ws' where "G'.steps (x' # ws' @ [y'])" "y \<preceq> y'"
    unfolding list_all2_append1 list_all2_Cons1 by auto
  with \<open>G'.steps (x # ws @ [y])\<close> have "V y" "V y'"
    subgoal
      using G'_steps_V_last assms(3) by fastforce
    using G'_steps_V_last \<open>G'.steps (x' # ws' @ [y'])\<close> assms(4) by fastforce
  with steps_mono[OF \<open>G'.steps ?xs\<close> \<open>y \<preceq> y'\<close>] obtain ys where ys:
    "list_all2 (\<preceq>) (concat (replicate ?n (xs @ [y]))) ys" "G'.steps (y' # ys)"
    by auto
  let ?ys = "filter ((\<preceq>) y) ys"
  have "length ?ys \<ge> ?n"
    using list_all2_replicate_elem_filter[OF ys(1), of y]
    by auto
  have "set ?ys \<subseteq> set ys"
    by auto
  also have "\<dots> \<subseteq> {x. V x}"
    using \<open>G'.steps (y' # _)\<close> \<open>V y'\<close> by (auto simp: list_all_iff dest: G'_steps_V_all)
  finally have "\<not> distinct ?ys"
    using distinct_card[of ?ys] \<open>_ >= ?n\<close>
    by - (rule ccontr; drule distinct_length_le[OF finite_V]; simp)
  from not_distinct_decomp[OF this] obtain as y'' bs cs where "?ys = as @ [y''] @ bs @ [y''] @ cs"
    by auto
  then obtain as' bs' cs' where
    "ys = as' @ [y''] @ bs' @ [y''] @ cs'"
    apply atomize_elim
    apply simp
    apply (drule filter_eq_appendD filter_eq_ConsD filter_eq_appendD[OF sym], clarify)+
    apply clarsimp
    subgoal for as1 as2 bs1 bs2 cs'
      by (inst_existentials "as1 @ as2" "bs1 @ bs2") simp
    done
  from \<open>G'.steps (y' # _)\<close> have "G'.steps (y' # as' @ y'' # bs' @ [y''])"
    unfolding \<open>ys = _\<close> by (force intro: Graph_Start_Defs.graphI_aggressive2)
  moreover from \<open>?ys = _\<close> have "y \<preceq> y''"
  proof -
    from \<open>?ys = _\<close> have "y'' \<in> set ?ys" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis
    using \<open>G'.steps (x' # ws' @ [y'])\<close>
    by (inst_existentials y'' "ws' @ y' # as'" bs';
        fastforce intro: Graph_Start_Defs.graphI_aggressive1
        )
qed

lemma reaches_cycle_mono:
  assumes "G'.reaches x y" "y \<rightarrow>\<^sup>+ y" "x \<preceq> x'" "V x" "V x'"
  shows "\<exists> y'. y \<preceq> y' \<and> G'.reaches x' y' \<and> y' \<rightarrow>\<^sup>+ y'"
proof -
  from assms obtain xs ys where "G'.steps (x # xs)" "y = last (x # xs)" "G'.steps (y # ys @ [y])"
    apply atomize_elim
    including reaches_steps_iff
    apply safe
    subgoal for xs xs'
      by (inst_existentials "tl xs" xs') auto
    done
  then obtain ws where "G'.steps (x # ws @ y # ys @ [y])"
    apply atomize_elim
    apply (cases xs)
     apply (inst_existentials ys)
     apply simp
      apply rotate_tac
     apply (rule G'.steps_append', assumption+, simp+)
    apply auto
     apply (inst_existentials "[] :: 'a list")
     apply (auto dest: G'.steps_append; fail)
    apply (drule G'.steps_append)
      apply assumption
     apply simp
    apply simp
    proof -
      fix a :: 'a and list :: "'a list"
      assume a1: "G'.steps (x # a # list @ ys @ [last list])"
      assume "list \<noteq> []"
      then have "butlast (a # list) @ [last list] = a # list"
        by (metis (no_types) append_butlast_last_id last_ConsR list.simps(3))
      then show "\<exists>as. G'.steps (x # as @ last list # ys @ [last list])"
        using a1 by (metis (no_types) Cons_eq_appendI append.assoc self_append_conv2)
    qed
    from steps_cycle_mono[OF this \<open>x \<preceq> x'\<close> \<open>V x\<close> \<open>V x'\<close>] guess y' xs' ys' by safe
    then have "G'.steps (x' # xs' @ [y'])" "G'.steps (y' # ys' @ [y'])"
      by (force intro: Graph_Start_Defs.graphI_aggressive2)+
    with \<open>y \<preceq> y'\<close> show ?thesis
      including reaches_steps_iff by force
  qed

end (* Finite subgraph *)

end (* Subsumption Graph Pre Nodes *)

locale Leadsto_Search_Space =
  A: Search_Space'_finite E a\<^sub>0 _ "(\<preceq>)" empty
  for E a\<^sub>0 empty and subsumes :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
  +
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes P_mono: "a \<preceq> a' \<Longrightarrow> \<not> empty a \<Longrightarrow> P a \<Longrightarrow> P a'"
  assumes Q_mono: "a \<preceq> a' \<Longrightarrow> \<not> empty a \<Longrightarrow> Q a \<Longrightarrow> Q a'"
  fixes succs_Q :: "'a \<Rightarrow> 'a list"
  assumes succs_Q_correct: "A.reachable a \<Longrightarrow> set (succs_Q a) = {y. E a y \<and> Q y \<and> \<not> empty y}"
begin

sublocale A': Search_Space'_finite E a\<^sub>0 "\<lambda> _. False" "(\<preceq>)" empty
  apply standard
          apply (rule A.refl A.trans A.mono A.empty_subsumes A.empty_mono A.empty_E; assumption)+
    apply assumption
   apply blast
  apply (rule A.finite_reachable)
  done

sublocale B:
  Liveness_Search_Space
  "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>0 "\<lambda> _. False" "(\<preceq>)" "\<lambda> x. A.reachable x \<and> \<not> empty x"
  succs_Q
  apply standard
       apply (rule A.refl A.trans; assumption)+
  subgoal for a b a'
    by safe (drule A.mono; auto intro: Q_mono dest: A.mono A.empty_mono)
    apply blast
   apply (auto intro: A.finite_reachable; fail)
  subgoal
    apply (subst succs_Q_correct)
    unfolding Subgraph_Node_Defs.E'_def by auto
  done

context
  fixes a\<^sub>1 :: 'a
begin

interpretation B':
  Liveness_Search_Space
  "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>1 "\<lambda> _. False" "(\<preceq>)" "\<lambda> x. A.reachable x \<and> \<not> empty x" succs_Q
  by standard

definition has_cycle where
  "has_cycle = B'.dfs"

end (* Second start state *)

definition leadsto :: "bool nres" where
  "leadsto = do {
    (r, passed) \<leftarrow> A'.pw_algo;
    let P = {x. x \<in> passed \<and> P x \<and> Q x};
    (r, _) \<leftarrow>
              FOREACH\<^sub>C P (\<lambda>(b,_). \<not>b) (\<lambda>v' (_,P). has_cycle v' P) (False,{});
    RETURN r
  }"

definition
  "reaches_cycle a =
    (\<exists> b. (\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y)\<^sup>*\<^sup>* a b \<and> (\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y)\<^sup>+\<^sup>+ b b)"

definition leadsto_spec where
  "leadsto_spec = SPEC (\<lambda> r. r \<longleftrightarrow> (\<exists> a. A.reachable a \<and> \<not> empty a \<and> P a \<and> Q a \<and> reaches_cycle a))"

lemma
  "leadsto \<le> leadsto_spec"
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
      "\<forall>x \<in> passed. P x \<and> Q x \<longrightarrow> \<not> reaches_cycle x"
      "A.reachable x" "\<not> empty x" "P x" "Q x"
    for x passed
  proof (rule ccontr, simp)
    assume "reaches_cycle x"
    from that obtain x' where "x' \<in> passed" "x \<preceq> x'"
      by auto
    with that have "P x'" "Q x'"
      by (auto intro: P_mono Q_mono)
    with \<open>x' \<in> passed\<close> that(3) have "\<not> reaches_cycle x'"
      by auto
    have "A.reachable x'" "\<not> empty x'"
      using \<open>x' \<in> passed\<close> that(2) A.empty_mono \<open>x \<preceq> x'\<close> that(5) by auto
    note reaches_cycle_iff' = reaches_cycle_iff[OF this] reaches_iff[OF this] reaches1_iff[OF this]
    from \<open>reaches_cycle x\<close> guess y unfolding reaches_cycle_def
      by safe
    interpret
      Subsumption_Graph_Pre_Nodes
        "(\<preceq>)" A.subsumes_strictly "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y"
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


  show ?thesis
    unfolding leadsto_def leadsto_spec_def
    apply (refine_rcg refine_vcg)
      subgoal for _ r passed
      apply (refine_vcg
            FOREACHc_rule'[where I = "inv {x \<in> passed. P x \<and> Q x}"]
            )

      (* Result of first reachability computation is finite *)
      subgoal
        by (auto intro: finite_subset[OF _ A.finite_reachable])

      (* Invariant holds initially *)
      subgoal
        unfolding inv_def B.liveness_compatible_def by auto

      (* Invariant is preserved *)
      subgoal for a\<^sub>1 it \<sigma> a passed'
        apply clarsimp
          subgoal premises prems
          proof -
            interpret B':
              Liveness_Search_Space
              "\<lambda> x y. E x y \<and> Q y \<and> \<not> empty y" a\<^sub>1 "\<lambda> _. False" "(\<preceq>)"
              "\<lambda> x. A.reachable x \<and> \<not> empty x" succs_Q
              by standard
            from \<open>inv _ _ _\<close> have
              "B'.liveness_compatible passed'" "passed' \<subseteq> {x. A.reachable x \<and> \<not> empty x}"
              unfolding inv_def by auto
            from B'.dfs_correct[OF _ this] \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>it \<subseteq> _\<close> have
              "B'.dfs passed' \<le> B'.dfs_spec"
              by auto
            then show ?thesis
              unfolding has_cycle_def
              apply (rule order.trans)
              unfolding B'.dfs_spec_def
              apply clarsimp
              subgoal for r passed'
                apply (cases r)
                 apply simp
                subgoal
                  unfolding inv_def
                  using \<open>passed \<subseteq> _\<close> \<open>a\<^sub>1 \<in> _\<close> \<open>it \<subseteq> _\<close>
                  apply simp
                    apply (inst_existentials a\<^sub>1)
                  by (auto 4 3 simp: reaches_cycle_iff)
                  subgoal
                    using \<open>inv _ _ _\<close> \<open>passed \<subseteq> _\<close> reaches_cycle_iff unfolding inv_def by blast
                  done
                done
            qed
            done

          (* I \<and> \<not> b \<longrightarrow> post *)
          subgoal for \<sigma> a b
            unfolding inv_def by (auto dest!: aux1)

          (* I \<and> b \<longrightarrow> post *)
          subgoal for it \<sigma> a b
            unfolding inv_def by auto
          done
        done
    qed

definition leadsto_spec_alt where
  "leadsto_spec_alt =
    SPEC (\<lambda> r.
      r \<longleftrightarrow>
      (\<exists> a. (\<lambda> x y. E x y \<and> \<not> empty y)\<^sup>*\<^sup>* a\<^sub>0 a \<and> \<not> empty a \<and> P a \<and> Q a \<and> reaches_cycle a)
    )"

lemma E_reaches_non_empty:
  "(\<lambda> x y. E x y \<and> \<not> empty y)\<^sup>*\<^sup>* a b" if "a \<rightarrow>* b" "A.reachable a" "\<not> empty b" for a b
  using that
proof induction
  case base
  then show ?case by blast
next
  case (step y z)
  from \<open>a \<rightarrow>* y\<close> \<open>A.reachable a\<close> have "A.reachable y"
    by - (rule A.reachable_reaches)
  have "\<not> empty y"
  proof (rule ccontr, simp)
    assume "empty y"
    from A.empty_E[OF \<open>A.reachable y\<close> \<open>empty y\<close> \<open>E y z\<close>] \<open>\<not> empty z\<close> show False by blast
  qed
  with step show ?case
    by (auto intro: rtranclp.intros(2))
qed

lemma leadsto_spec_leadsto_spec_alt:
  "leadsto_spec \<le> leadsto_spec_alt"
  unfolding leadsto_spec_def leadsto_spec_alt_def
  by (auto
      intro: Subgraph.intro Subgraph.reaches[rotated] E_reaches_non_empty[OF _ A.start_reachable]
      simp: A.reachable_def
     )

end (* Leadsto Search Space *)

end (* Theory *)
