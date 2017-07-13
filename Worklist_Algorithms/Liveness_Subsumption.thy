(* Authors: Simon Wimmer, Peter Lammich *)
theory Liveness_Subsumption
  imports "$AFP/Refine_Imperative_HOL/Sepref" Worklist_Common "../Subsumption_Graphs"
begin

context Search_Space_Defs_Empty
begin

text \<open>Plain set membership is also an option.\<close>
definition "check_loop v ST = (\<exists> v' \<in> ST. v' \<preceq> v)"

definition dfs :: "('a set \<times> bool) nres" where
  "dfs \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      if check_loop v ST then RETURN (P, ST, True)
      else do {
        if \<exists> v' \<in> P. v \<preceq> v' then
          RETURN (P, ST, False)
        else do {
            let ST=insert v ST;
            (P, ST, r) \<leftarrow>
              FOREACH\<^sub>C {v' . E v v'} (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
            let ST = ST - {v};
            let P = insert v P;
            RETURN (P, ST, r)
          }
      }
    ) ({},{},a\<^sub>0);
    RETURN (P, r)
  }"

definition liveness_compatible where "liveness_compatible P \<equiv>
    (\<forall> x x' y. reachable x \<and> x \<rightarrow> y \<and> x' \<in> P \<and> x \<preceq> x' \<longrightarrow> (\<exists> y' \<in> P. y \<preceq> y')) \<and>
    (\<forall> s' \<in> P. \<forall> s. s \<preceq> s' \<and> reachable s \<longrightarrow>
      \<not> (\<lambda> x y. E x y \<and> (\<exists> x' \<in> P. \<exists> y' \<in> P. x \<preceq> x' \<and> y \<preceq> y'))\<^sup>+\<^sup>+ s s)
    "

definition "dfs_spec \<equiv> SPEC (\<lambda>(P,r). r \<longleftrightarrow> (\<exists> x. reachable x \<and> x \<rightarrow>\<^sup>+ x))"

end (* Search Space Defs *)

context Search_Space_finite_strict
begin

lemma check_loop_loop: "\<exists> v' \<in> ST. v' \<preceq> v" if "check_loop v ST"
  using that unfolding check_loop_def by blast

lemma check_loop_no_loop: "v \<notin> ST" if "\<not> check_loop v ST"
  using that unfolding check_loop_def by blast

context
  assumes empty: "empty = (\<lambda> x. False)"
begin

lemma mono:
  "a \<preceq> b \<Longrightarrow> a \<rightarrow> a' \<Longrightarrow> reachable a \<Longrightarrow> reachable b \<Longrightarrow> \<exists> b'. b \<rightarrow> b' \<and> a' \<preceq> b'"
  by (auto intro: mono simp: empty)

interpretation Subsumption_Graph_Pre "op \<preceq>" "op \<prec>" E a\<^sub>0
  by standard (blast intro: mono)

context
  fixes P :: "'a set" and E1 E2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and v :: 'a
  defines [simp]: "E1 \<equiv> \<lambda>x y. x \<rightarrow> y \<and> (\<exists>x'\<in>P. x \<preceq> x') \<and> (\<exists>x\<in>P. y \<preceq> x)"
  defines [simp]: "E2 \<equiv> \<lambda>x y. x \<rightarrow> y \<and> (x \<preceq> v \<or> (\<exists>xa\<in>P. x \<preceq> xa)) \<and> (y \<preceq> v \<or> (\<exists>x\<in>P. y \<preceq> x))"
begin

interpretation G:  Graph_Defs E1  .
interpretation G': Graph_Defs E2 .
interpretation SG: Subgraph E2 E1 by standard auto
interpretation SG': Subgraph_Start E a\<^sub>0 E1 by standard auto
interpretation SG'': Subgraph_Start E a\<^sub>0 E2 by standard auto

lemma liveness_compatible_extend:
  assumes
    "reachable s" "reachable v" "s \<preceq> v"
    "liveness_compatible P"
    "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
    "E2\<^sup>+\<^sup>+ s s"
  shows False
proof -
  include graph_automation_aggressive
  have 1: "\<exists> b' \<in> P. b \<preceq> b'" if "G.reaches a b" "a \<preceq> a'" "a' \<in> P" for a a' b
    using that by cases auto
  have 2: "E1 a b" if "a \<rightarrow> b" "a \<preceq> a'" "a' \<in> P" "reachable a" for a a' b
    using assms(4) that unfolding liveness_compatible_def by auto
  from assms(6) have "E2\<^sup>+\<^sup>+ s s"
    by auto
  have 4: "G.reaches a b" if "G'.reaches a b" "a \<preceq> a'" "a' \<in> P" "reachable a" for a a' b
    using that
  proof induction
    case base
    then show ?case
      by blast
  next
    case (step b c)
    then have "G.reaches a b"
      by auto
    from \<open>reachable a\<close> \<open>G.reaches a b\<close> have "reachable b"
      by blast
    from \<open>G.reaches a b\<close> \<open>a \<preceq> a'\<close> \<open>a' \<in> P\<close> obtain b' where "b' \<in> P" "b \<preceq> b'"
      by (fastforce dest: 1)
    with \<open>E2 b c\<close> \<open>reachable b\<close> have "E1 b c"
      by (fastforce intro: 2)
    with \<open>G.reaches a b\<close> show ?case
      by blast
  qed
  from \<open>E2\<^sup>+\<^sup>+ s s\<close> obtain x where "E2 s x" "G'.reaches x s"
    by atomize_elim blast (* XXX *)
  then have "s \<rightarrow> x"
    by auto
  with \<open>s \<preceq> v\<close> \<open>reachable s\<close> \<open>reachable v\<close> obtain x' where "v \<rightarrow> x'" "x \<preceq> x'"
    by (auto dest: mono)
  with assms(5) obtain x'' where "x \<preceq> x''" "x'' \<in> P"
    by (auto intro: order_trans)
  from 4[OF \<open>G'.reaches x s\<close> \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close>] \<open>s \<rightarrow> x\<close> assms(1) have "G.reaches x s"
    by blast
  with \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close> obtain s' where "s \<preceq> s'" "s' \<in> P"
    by (blast dest: 1)
  with \<open>s \<rightarrow> x\<close> \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close> have "E1 s x"
    by auto
  with \<open>G.reaches x s\<close> have "G.reaches1 s s"
    by blast
  with assms(4) \<open>s' \<in> P\<close> \<open>s \<preceq> s'\<close> \<open>reachable s\<close> show False
    unfolding liveness_compatible_def by auto
qed

lemma liveness_compatible_extend':
  assumes
    "reachable s" "reachable v" "s \<preceq> s'" "s' \<in> P"
    "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
    "liveness_compatible P"
    "E2\<^sup>+\<^sup>+ s s"
  shows False
proof -
  show ?thesis
  proof (cases "G.reaches1 s s")
    case True
    with assms show ?thesis
      unfolding liveness_compatible_def by auto
  next
    case False
    with SG.non_subgraph_cycle_decomp[of s s] assms(7) obtain c d where **:
      "G'.reaches s c" "E2 c d" "\<not> E1 c d" "G'.reaches d s"
      by auto
    from \<open>E2 c d\<close> \<open>\<not> E1 c d\<close> have "c \<preceq> v \<or> d \<preceq> v"
      by auto
    with \<open>reachable s\<close> ** obtain v' where "G'.reaches1 v' v'" "v' \<preceq> v" "reachable v'"
      by (auto simp del: E2_def E1_def intro!: that)
    with assms show ?thesis
      by (auto intro: liveness_compatible_extend)
  qed
qed

end (* Edge sets restricted to passed set *)

lemma liveness_compatible_cycle_start:
  assumes
    "liveness_compatible P" "reachable x" "x \<rightarrow>\<^sup>+ x" "a\<^sub>0 \<preceq> s" "s \<in> P"
  shows False
proof -
  include graph_automation_aggressive
  have *: "\<exists> y \<in> P. x \<preceq> y" if "reachable x" for x
    using that assms unfolding liveness_compatible_def by induction auto
  have **:
    "(\<lambda>x y. x \<rightarrow> y \<and> (\<exists>x'\<in>P. x \<preceq> x') \<and> (\<exists>x\<in>P. y \<preceq> x))\<^sup>+\<^sup>+ a b \<longleftrightarrow> a \<rightarrow>\<^sup>+ b " if "reachable a" for a b
    apply standard
    subgoal
      by (induction rule: tranclp_induct; blast)
    subgoal
      using \<open>reachable a\<close>
      by - (induction rule: tranclp.induct, auto 4 4 intro: *)
    done
  from assms show ?thesis
    unfolding liveness_compatible_def
    by (clarsimp simp add: **) (blast dest: *)
qed

lemma liveness_compatible_inv:
  assumes "reachable v" "liveness_compatible P" "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
  shows "liveness_compatible (insert v P)"
  using assms
  apply (subst liveness_compatible_def)
  apply safe
     apply clarsimp_all
     apply (meson mono order_trans; fail)
    apply (subst (asm) liveness_compatible_def, meson; fail)
  by (blast intro: liveness_compatible_extend liveness_compatible_extend')+

lemma dfs_correct:
  "dfs \<le> dfs_spec"
proof -

  define rpre where "rpre \<equiv> \<lambda>(P,ST,v).
        reachable v
      \<and> P \<subseteq> {x. reachable x}
      \<and> ST \<subseteq> {x. reachable x}
      \<and> liveness_compatible P
      \<and> (\<forall> s \<in> ST. s \<rightarrow>\<^sup>+ v)
    "

  define rpost where "rpost \<equiv> \<lambda>(P,ST,v) (P',ST',r).
    (r \<longrightarrow> (\<exists> x x'. reachable x \<and> x \<rightarrow>\<^sup>+ x' \<and> x \<preceq> x')) \<and>
    (\<not> r \<longrightarrow>
      P \<subseteq> P'
      \<and> P' \<subseteq> {x. reachable x}
      \<and> ST \<subseteq> {x. reachable x}
      \<and> ST' = ST
      \<and> (\<forall> s \<in> ST. s \<rightarrow>* v)
      \<and> liveness_compatible P'
      \<and> (\<exists> v' \<in> P'. v \<preceq> v')
      )
      "

  define inv where "inv \<equiv> \<lambda> P ST v it (P', ST', r).
    (r \<longrightarrow> (\<exists> x x'. reachable x \<and> x \<rightarrow>\<^sup>+ x' \<and> x \<preceq> x')) \<and>
    (\<not> r \<longrightarrow>
        P \<subseteq> P'
      \<and> P' \<subseteq> {x. reachable x}
      \<and> ST \<subseteq> {x. reachable x}
      \<and> ST' = ST
      \<and> (\<forall> s \<in> ST. s \<rightarrow>* v)
      \<and> liveness_compatible P'
      \<and> (\<forall> v \<in> {v'. E v v'} - it. (\<exists> v' \<in> P'. v \<preceq> v'))
    )
  "

  define Termination :: "(('a set \<times> 'a set \<times> 'a) \<times> 'a set \<times> 'a set \<times> 'a) set" where
    "Termination = inv_image (finite_psupset {x. reachable x}) (\<lambda> (a,b,c). b)"

  have rpre_init: "rpre ({}, {}, a\<^sub>0)"
    unfolding rpre_def liveness_compatible_def by auto

  have wf: "wf Termination"
    unfolding Termination_def by (blast intro: finite_reachable)

  have successors_finite: "finite {v'. v \<rightarrow> v'}" if "reachable v" for v
    using finitely_branching[OF that] by (auto simp: empty)

  show ?thesis
    unfolding dfs_def dfs_spec_def
    apply (refine_rcg refine_vcg)
    apply (rule order.trans)
     apply(rule RECT_rule[where
          pre = rpre and
          V = Termination and
          M = "\<lambda>x. SPEC (rpost x)"
          ])

        apply refine_mono

      (* Termination *)
       apply (rule wf; fail)

      (* Precondition holds initially *)
      apply (rule rpre_init; fail)

     defer

      (* The postcondition establishes the specification *)
    subgoal
      apply refine_vcg
      unfolding rpost_def pre_cycle_cycle[OF finite_reachable]
      including graph_automation
      using liveness_compatible_cycle_start by blast

    apply (thin_tac "_ = f")

    (* Pre \<longrightarrow> Post *)
    apply refine_vcg

    (* Cycle found *)
    subgoal for f x a b aa ba
      by (subst rpost_def, subst (asm) (2) rpre_def, auto 4 4 dest: check_loop_loop)

    (* Subsumption *)
    subgoal for f x P b ST v
      by (subst rpost_def, subst (asm) (2) rpre_def, force)

    (* Foreach *)
    subgoal for f x P b ST v

      apply (refine_vcg
          FOREACHc_rule'[where I = "inv P (insert v ST) v"]
          )
          apply clarsimp_all
      (* Finitely Branching *)
      subgoal
        by (auto intro: successors_finite simp: rpre_def rpost_def)

      (* Pre \<longrightarrow> Invariant *)
      subgoal
        by (subst (asm) (2) rpre_def, subst inv_def, auto)

      (* Invariant *)
      subgoal for v' it P' ST' c
        apply (rule order.trans)
         apply rprems

        (* Inv \<longrightarrow> Pre *)
        subgoal
          including graph_automation by (subst rpre_def, subst (asm) inv_def, auto 4 3)

        (* Termination *)
        subgoal
          unfolding Termination_def
          by (auto simp: finite_psupset_def inv_def dest: check_loop_no_loop)

        (* Post \<longrightarrow> Inv *)
        subgoal
          apply (subst inv_def, subst (asm) inv_def, subst rpost_def)
          apply (clarsimp simp: it_step_insert_iff)
          by (safe; (intro exI conjI)?; blast intro: rtranclp_trans)
        done

      (* No cycle \<longrightarrow> Post *)
      subgoal for P' ST' c
        by (subst rpost_def, subst (asm) inv_def,
            auto intro: liveness_compatible_inv dest: check_loop_no_loop)

      (* Cycle \<longrightarrow> Post *)
      subgoal
        by (subst (asm) inv_def, subst (asm) (2) rpre_def, subst rpost_def, auto)
      done
    done
qed

end (* Search Space Finite Strict *)

end (* Theory *)