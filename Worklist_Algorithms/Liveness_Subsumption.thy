theory Liveness_Subsumption
  imports "$AFP/Refine_Imperative_HOL/Sepref" Worklist_Locales "../Subsumption_Graphs"
begin

(* XXX Duplication with Unified_PW *)
lemma (in Search_Space_finite) finitely_branching:
  assumes "reachable a"
  shows "finite ({a'. E a a' \<and> \<not> empty a'})"
proof -
  have "{a'. E a a' \<and> \<not> empty a'} \<subseteq> {a'. reachable a' \<and> \<not> empty a'}"
    using assms(1) by (auto intro: reachable_step)
  then show ?thesis using finite_reachable
    by (rule finite_subset)
qed

context Search_Space_Defs_Empty
begin

definition dfs :: "('a set \<times> bool) nres" where
  "dfs \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      if v\<in>ST then RETURN (P, ST, True)
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

context
  assumes empty: "empty = (\<lambda> x. False)"
begin

lemma mono:
  "a \<preceq> b \<Longrightarrow> a \<rightarrow> a' \<Longrightarrow> reachable a \<Longrightarrow> reachable b \<Longrightarrow> \<exists> b'. b \<rightarrow> b' \<and> a' \<preceq> b'"
  by (auto intro: mono simp: empty)

lemma liveness_compatible_extend:
  assumes
    "reachable s" "reachable v" "s \<preceq> v"
    "liveness_compatible P"
    "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
    "(\<lambda>x y. x \<rightarrow> y \<and> (x \<preceq> v \<or> (\<exists>xa\<in>P. x \<preceq> xa)) \<and> (y \<preceq> v \<or> (\<exists>x\<in>P. y \<preceq> x)))\<^sup>+\<^sup>+ s s"
  shows False
proof -
  define E E'
    where E_def [simp]: "E  \<equiv> \<lambda>x y. x \<rightarrow> y \<and> (\<exists>x'\<in>P. x \<preceq> x') \<and> (\<exists>x\<in>P. y \<preceq> x)"
      and E'_def[simp]: "E' \<equiv> \<lambda>x y. x \<rightarrow> y \<and> (x \<preceq> v \<or> (\<exists>xa\<in>P. x \<preceq> xa)) \<and> (y \<preceq> v \<or> (\<exists>x\<in>P. y \<preceq> x))"
  interpret G:  Graph_Defs E  .
  interpret G': Graph_Defs E' .
  have 1: "\<exists> b' \<in> P. b \<preceq> b'" if "G.reaches a b" "a \<preceq> a'" "a' \<in> P" for a a' b
    using that by cases auto
  have 2: "E a b" if "a \<rightarrow> b" "a \<preceq> a'" "a' \<in> P" "reachable a" for a a' b
    using assms(4) that unfolding liveness_compatible_def by auto
  have 3: "reachable b" if \<open>reachable a\<close> \<open>G.reaches a b\<close> for a b
    by (metis E_def mono_rtranclp reachable_reaches that(1) that(2))
  from assms(6) have "E'\<^sup>+\<^sup>+ s s"
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
    from \<open>E' b c\<close> have "b \<rightarrow> c"
      by auto
    from \<open>reachable a\<close> \<open>G.reaches a b\<close> have "reachable b"
      by (blast intro: 3)
    from \<open>G.reaches a b\<close> \<open>a \<preceq> a'\<close> \<open>a' \<in> P\<close> obtain b' where "b' \<in> P" "b \<preceq> b'"
      by (fastforce dest: 1)
    with \<open>b \<rightarrow> c\<close> \<open>reachable b\<close> have "E b c"
      by (blast intro: 2)
    with \<open>G.reaches a b\<close> show ?case
      by (meson rtranclp.rtrancl_into_rtrancl) (* XXX *)
  qed
  from \<open>E'\<^sup>+\<^sup>+ s s\<close> obtain x where "E' s x" "G'.reaches x s"
    by atomize_elim (meson tranclpD) (* XXX *)
  then have "s \<rightarrow> x"
    by auto
  with \<open>s \<preceq> v\<close> \<open>reachable s\<close> \<open>reachable v\<close> obtain x' where "v \<rightarrow> x'" "x \<preceq> x'"
    by (auto dest: mono)
  with assms(5) obtain x'' where "x \<preceq> x''" "x'' \<in> P"
    by (auto intro: order_trans)
  from 4[OF \<open>G'.reaches x s\<close> \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close>] have "G.reaches x s"
    using \<open>s \<rightarrow> x\<close> assms(1) reachable_step by blast
  with \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close> obtain s' where "s \<preceq> s'" "s' \<in> P"
    by (blast dest: 1)
  with \<open>s \<rightarrow> x\<close> \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close> have "E s x"
    by auto
  with \<open>G.reaches x s\<close> have "G.reaches1 s s"
    by (meson rtranclp_into_tranclp2) (* XXX *)
  with assms(4) \<open>s' \<in> P\<close> \<open>s \<preceq> s'\<close> \<open>reachable s\<close> show False
    unfolding liveness_compatible_def by auto
qed

lemma liveness_compatible_extend':
  assumes
    "reachable s" "reachable v" "s \<preceq> s'" "s' \<in> P"
    "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
    "liveness_compatible P"
    "(\<lambda>x y. x \<rightarrow> y \<and> (x \<preceq> v \<or> (\<exists>xa\<in>P. x \<preceq> xa)) \<and> (y \<preceq> v \<or> (\<exists>x\<in>P. y \<preceq> x)))\<^sup>+\<^sup>+ s s"
  shows False
proof -
  define E E'
    where E_def [simp]: "E  \<equiv> \<lambda>x y. x \<rightarrow> y \<and> (\<exists>x'\<in>P. x \<preceq> x') \<and> (\<exists>x\<in>P. y \<preceq> x)"
      and E'_def[simp]: "E' \<equiv> \<lambda>x y. x \<rightarrow> y \<and> (x \<preceq> v \<or> (\<exists>xa\<in>P. x \<preceq> xa)) \<and> (y \<preceq> v \<or> (\<exists>x\<in>P. y \<preceq> x))"
  interpret G:  Graph_Defs E  .
  interpret G': Graph_Defs E' .
  (* XXX Lemma *)
  have *: "\<exists> c d. G'.reaches a c \<and> E' c d \<and> \<not> E c d \<and> G'.reaches d b"
    if "G'.reaches1 a b" "\<not> G.reaches1 a b" for a b
    using that
  proof induction
    case (base y)
    then show ?case
      by auto
  next
    case (step y z)
    show ?case
    proof (cases "E y z")
      case True
      with step have "\<not> G.reaches1 a y"
        by (auto simp del: E_def E'_def intro: tranclp.trancl_into_trancl) (* XXX *)
      with step obtain c d where
        "G'.reaches a c" "E' c d" "\<not> E c d" "G'.reaches d y"
        by auto
      with \<open>E' y z\<close> show ?thesis
        by (blast intro: rtranclp.rtrancl_into_rtrancl) (* XXX *)
    next
      case False
      with step show ?thesis
        by (intro exI conjI) (auto simp del: E_def E'_def)
    qed
  qed
  have 3[intro]: "reachable b" if \<open>reachable a\<close> \<open>G'.reaches a b\<close> for a b
    by (metis E'_def mono_rtranclp reachable_reaches that(1) that(2))
  show ?thesis
  proof (cases "G.reaches1 s s")
    case True
    with assms show ?thesis
      unfolding liveness_compatible_def by auto
  next
    case False
    with *[of s s] assms(7) obtain c d where **:
      "G'.reaches s c" "E' c d" "\<not> E c d" "G'.reaches d s"
      by auto
    from \<open>E' c d\<close> \<open>\<not> E c d\<close> have "c \<preceq> v \<or> d \<preceq> v"
      by auto
    with \<open>reachable s\<close> ** obtain v' where "G'.reaches1 v' v'" "v' \<preceq> v" "reachable v'"
      by (auto simp del: E'_def E_def intro!: that)
    with assms show ?thesis
      by (auto intro: liveness_compatible_extend)
  qed
qed

lemma liveness_compatible_cycle_start:
  assumes
    "liveness_compatible P" "reachable x" "x \<rightarrow>\<^sup>+ x"
    "a\<^sub>0 \<preceq> s" "s \<in> P"
  shows False
proof -
  have *: "\<exists> y \<in> P. x \<preceq> y" if "reachable x" for x
    using that
  proof induction
    case start
    from assms show ?case
      by auto
  next
    case (step a b)
    then obtain a' where "a' \<in> P" "a \<preceq> a'"
      by auto
    with assms(1) \<open>reachable a\<close> \<open>a \<rightarrow> b\<close> show ?case
      unfolding liveness_compatible_def by auto
  qed
  have **:
    "(\<lambda>x y. x \<rightarrow> y \<and> (\<exists>x'\<in>P. x \<preceq> x') \<and> (\<exists>x\<in>P. y \<preceq> x))\<^sup>+\<^sup>+ a b \<longleftrightarrow>
     a \<rightarrow>\<^sup>+ b
    " if "reachable a" for a b
    apply standard
    subgoal
      by (induction rule: tranclp_induct; blast intro: tranclp.intros(2))
    subgoal
      using \<open>reachable a\<close>
      including graph_automation
      by - (induction rule: tranclp.induct, auto 4 4 intro: * tranclp.intros(2))
    done
  from assms show ?thesis
    unfolding liveness_compatible_def
    by (clarsimp simp add: **) (blast dest: *)
qed

lemma liveness_compatible_inv:
  assumes "reachable v" "\<forall>s\<in>ST. s \<rightarrow>* v" "liveness_compatible P'" "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P'. va \<preceq> x)"
  shows "liveness_compatible (insert v P')"
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
    (r \<longrightarrow> (\<exists> x. v \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x)) \<and>
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
    (r \<longrightarrow> (\<exists> x. v \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x)) \<and>
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
      unfolding rpost_def reachable_def
      including graph_automation
      using liveness_compatible_cycle_start by blast


    apply (thin_tac "_ = f")

    (* Pre \<longrightarrow> Post *)
    apply refine_vcg

    (* Cycle found *)
    subgoal for f x a b aa ba
      by (subst rpost_def, subst (asm) (2) rpre_def, force)

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
          unfolding Termination_def by (auto simp: finite_psupset_def inv_def)

        (* Post \<longrightarrow> Inv *)
        subgoal
          apply (subst inv_def, subst (asm) inv_def, subst rpost_def)
          apply (clarsimp simp: it_step_insert_iff)
          by (safe; (intro exI conjI)?; blast intro: rtranclp_trans)
        done

      (* No cycle \<longrightarrow> Post *)
      subgoal for P' ST' c
        by (subst rpost_def, subst (asm) inv_def, auto intro: liveness_compatible_inv)

      (* Cycle \<longrightarrow> Post *)
      subgoal
        by (subst (asm) inv_def, subst (asm) (2) rpre_def, subst rpost_def, auto)
      done
    done
qed

end (* Search Space Finite Strict *)

end (* Theory *)