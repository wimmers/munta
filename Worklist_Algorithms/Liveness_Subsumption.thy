(* Authors: Simon Wimmer, Peter Lammich *)
theory Liveness_Subsumption
  imports
    Refine_Imperative_HOL.Sepref Worklist_Common TA_Library.Subsumption_Graphs
begin

context Search_Space_Nodes_Defs
begin

sublocale G: Subgraph_Node_Defs .

no_notation E ("_ \<rightarrow> _" [100, 100] 40)
notation G.E' ("_ \<rightarrow> _" [100, 100] 40)
no_notation reaches ("_ \<rightarrow>* _" [100, 100] 40)
notation G.G'.reaches ("_ \<rightarrow>* _" [100, 100] 40)
no_notation reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40)
notation G.G'.reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40)

text \<open>Plain set membership is also an option.\<close>
definition "check_loop v ST = (\<exists> v' \<in> set ST. v' \<preceq> v)"

definition dfs :: "'a set \<Rightarrow> (bool \<times> 'a set) nres" where
  "dfs P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      do {
        if check_loop v ST then RETURN (P, ST, True)
        else do {
          if \<exists> v' \<in> P. v \<preceq> v' then
            RETURN (P, ST, False)
          else do {
              let ST = v # ST;
              (P, ST', r) \<leftarrow>
                FOREACHcd {v'. v \<rightarrow> v'} (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
              ASSERT (ST' = ST);
              let ST = tl ST';
              let P = insert v P;
              RETURN (P, ST, r)
            }
        }
      }
    ) (P,[],a\<^sub>0);
    RETURN (r, P)
  }"

definition liveness_compatible where "liveness_compatible P \<equiv>
    (\<forall> x x' y. x \<rightarrow> y \<and> x' \<in> P \<and> x \<preceq> x' \<longrightarrow> (\<exists> y' \<in> P. y \<preceq> y')) \<and>
    (\<forall> s' \<in> P. \<forall> s. s \<preceq> s' \<and> V s \<longrightarrow>
      \<not> (\<lambda> x y. x \<rightarrow> y \<and> (\<exists> x' \<in> P. \<exists> y' \<in> P. x \<preceq> x' \<and> y \<preceq> y'))\<^sup>+\<^sup>+ s s)
    "

definition "dfs_spec \<equiv>
  SPEC (\<lambda> (r, P).
    (r \<longrightarrow> (\<exists> x. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x))
  \<and> (\<not> r \<longrightarrow> \<not> (\<exists> x. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x)
      \<and> liveness_compatible P \<and> P \<subseteq> {x. V x}
    )
  )"

end (* Search Space Defs *)

locale Liveness_Search_Space_pre =
  Search_Space_Nodes +
  assumes finite_V: "finite {a. V a}"
begin

lemma check_loop_loop: "\<exists> v' \<in> set ST. v' \<preceq> v" if "check_loop v ST"
  using that unfolding check_loop_def by blast

lemma check_loop_no_loop: "v \<notin> set ST" if "\<not> check_loop v ST"
  using that unfolding check_loop_def by blast

lemma mono:
  "a \<preceq> b \<Longrightarrow> a \<rightarrow> a' \<Longrightarrow> V b \<Longrightarrow> \<exists> b'. b \<rightarrow> b' \<and> a' \<preceq> b'"
  by (auto dest: mono simp: G.E'_def)

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

(* XXX Generalize *)
lemma G_subgraph_reaches[intro]:
  "G.G'.reaches a b" if "G.reaches a b"
  using that by induction auto

(* XXX Generalize *)
lemma G'_subgraph_reaches[intro]:
  "G.G'.reaches a b" if "G'.reaches a b"
  using that by induction auto

lemma liveness_compatible_extend:
  assumes
    "V s" "V v" "s \<preceq> v"
    "liveness_compatible P"
    "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
    "E2\<^sup>+\<^sup>+ s s"
  shows False
proof -
  include graph_automation_aggressive
  have 1: "\<exists> b' \<in> P. b \<preceq> b'" if "G.reaches a b" "a \<preceq> a'" "a' \<in> P" for a a' b
    using that by cases auto
  have 2: "E1 a b" if "a \<rightarrow> b" "a \<preceq> a'" "a' \<in> P" "V a" for a a' b
    using assms(4) that unfolding liveness_compatible_def by auto
  from assms(6) have "E2\<^sup>+\<^sup>+ s s"
    by auto
  have 4: "G.reaches a b" if "G'.reaches a b" "a \<preceq> a'" "a' \<in> P" "V a" for a a' b
    using that
  proof induction
    case base
    then show ?case
      by blast
  next
    case (step b c)
    then have "G.reaches a b"
      by auto
    from \<open>V a\<close> \<open>G.reaches a b\<close> have "V b"
      including subgraph_automation by blast
    from \<open>G.reaches a b\<close> \<open>a \<preceq> a'\<close> \<open>a' \<in> P\<close> obtain b' where "b' \<in> P" "b \<preceq> b'"
      by (fastforce dest: 1)
    with \<open>E2 b c\<close> \<open>V b\<close> have "E1 b c"
      by (fastforce intro: 2)
    with \<open>G.reaches a b\<close> show ?case
      by blast
  qed
  from \<open>E2\<^sup>+\<^sup>+ s s\<close> obtain x where "E2 s x" "G'.reaches x s"
    by atomize_elim blast (* XXX *)
  then have "s \<rightarrow> x"
    by auto
  with \<open>s \<preceq> v\<close> \<open>V s\<close> \<open>V v\<close> obtain x' where "v \<rightarrow> x'" "x \<preceq> x'"
    by (auto dest: mono)
  with assms(5) obtain x'' where "x \<preceq> x''" "x'' \<in> P"
    by (auto intro: order_trans)
  from 4[OF \<open>G'.reaches x s\<close> \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close>] \<open>s \<rightarrow> x\<close> \<open>V s\<close> have "G.reaches x s"
    including subgraph_automation by blast
  with \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close> obtain s' where "s \<preceq> s'" "s' \<in> P"
    by (blast dest: 1)
  with \<open>s \<rightarrow> x\<close> \<open>x \<preceq> x''\<close> \<open>x'' \<in> P\<close> have "E1 s x"
    by auto
  with \<open>G.reaches x s\<close> have "G.reaches1 s s"
    by blast
  with assms(4) \<open>s' \<in> P\<close> \<open>s \<preceq> s'\<close> \<open>V s\<close> show False
    unfolding liveness_compatible_def by auto
qed

lemma liveness_compatible_extend':
  assumes
    "V s" "V v" "s \<preceq> s'" "s' \<in> P"
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
    with \<open>V s\<close> ** obtain v' where "G'.reaches1 v' v'" "v' \<preceq> v" "V v'"
      apply atomize_elim
      apply (erule disjE)
      subgoal
        including graph_automation_aggressive
        by (blast intro: rtranclp_trans G.subgraphI) (* XXX Fix automation *)
      subgoal
        unfolding G'.reaches1_reaches_iff2
        by (blast intro: rtranclp_trans intro: G.subgraphI) (* XXX Fix automation *)
      done
    with assms show ?thesis
      by (auto intro: liveness_compatible_extend)
  qed
qed

end (* Edge sets restricted to passed set *)

lemma liveness_compatible_cycle_start:
  assumes
    "liveness_compatible P" "a \<rightarrow>* x" "x \<rightarrow>\<^sup>+ x" "a \<preceq> s" "s \<in> P"
  shows False
proof -
  include graph_automation_aggressive
  have *: "\<exists> y \<in> P. x \<preceq> y" if "G.G'.reaches a x" for x
    using that assms unfolding liveness_compatible_def by induction auto
  have **:
    "(\<lambda>x y. x \<rightarrow> y \<and> (\<exists>x'\<in>P. x \<preceq> x') \<and> (\<exists>x\<in>P. y \<preceq> x))\<^sup>+\<^sup>+ a' b \<longleftrightarrow> a' \<rightarrow>\<^sup>+ b "
    if "a \<rightarrow>* a'" for a' b
    apply standard
    subgoal
      by (induction rule: tranclp_induct; blast)
    subgoal
      using \<open>a \<rightarrow>* a'\<close>
      apply - apply (induction rule: tranclp.induct)
      subgoal for a' b'
        by (auto intro: *)
      by (rule tranclp.intros(2), auto intro: *)
    done
  from assms show ?thesis
    unfolding liveness_compatible_def by clarsimp (blast dest: * ** intro: G.subgraphI)
qed

lemma liveness_compatible_inv:
  assumes "V v" "liveness_compatible P" "\<forall>va. v \<rightarrow> va \<longrightarrow> (\<exists>x\<in>P. va \<preceq> x)"
  shows "liveness_compatible (insert v P)"
  using assms
  apply (subst liveness_compatible_def)
  apply safe
     apply clarsimp_all
     apply (meson mono order_trans; fail)
    apply (subst (asm) liveness_compatible_def, meson; fail)
  by (blast intro: liveness_compatible_extend liveness_compatible_extend')+

interpretation subsumption: Subsumption_Graph_Pre_Nodes "(\<preceq>)" "(\<prec>)" E V
  by standard (drule mono, auto simp: Subgraph_Node_Defs.E'_def)

lemma pre_cycle_cycle:
  "(\<exists> x x'. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x' \<and> x \<preceq> x') \<longleftrightarrow> (\<exists> x. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x)"
  by (meson G.E'_def G.G'.reaches1_reaches_iff1 subsumption.pre_cycle_cycle_reachable finite_V)

lemma reachable_alt:
  "V v" if "V a\<^sub>0" "a\<^sub>0 \<rightarrow>* v"
  using that(2,1) by cases (auto simp: G.E'_def)

lemma dfs_correct:
  "dfs P \<le> dfs_spec" if "V a\<^sub>0" "liveness_compatible P" "P \<subseteq> {x. V x}"
proof -

  define rpre where "rpre \<equiv> \<lambda>(P,ST,v).
        a\<^sub>0 \<rightarrow>* v
      \<and> V v
      \<and> P \<subseteq> {x. V x}
      \<and> set ST \<subseteq> {x. a\<^sub>0 \<rightarrow>* x}
      \<and> set ST \<subseteq> {x. V x}
      \<and> liveness_compatible P
      \<and> (\<forall> s \<in> set ST. s \<rightarrow>\<^sup>+ v)
      \<and> distinct ST
    "

  define rpost where "rpost \<equiv> \<lambda>(P,ST,v) (P',ST',r).
    (r \<longrightarrow> (\<exists> x x'. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x' \<and> x \<preceq> x') \<and> ST' = ST) \<and>
    (\<not> r \<longrightarrow>
      P \<subseteq> P'
      \<and> P' \<subseteq> {x. V x}
      \<and> set ST \<subseteq> {x. a\<^sub>0 \<rightarrow>* x}
      \<and> ST' = ST
      \<and> (\<forall> s \<in> set ST. s \<rightarrow>* v)
      \<and> liveness_compatible P'
      \<and> (\<exists> v' \<in> P'. v \<preceq> v')
      \<and> distinct ST
      )
      "

  define inv where "inv \<equiv> \<lambda> P ST v (_ :: 'a set) it (P', ST', r).
    (r \<longrightarrow> (\<exists> x x'. a\<^sub>0 \<rightarrow>* x \<and> x \<rightarrow>\<^sup>+ x' \<and> x \<preceq> x') \<and> ST' = ST) \<and>
    (\<not> r \<longrightarrow>
        P \<subseteq> P'
      \<and> P' \<subseteq> {x. V x}
      \<and> set ST \<subseteq> {x. a\<^sub>0 \<rightarrow>* x}
      \<and> ST' = ST
      \<and> (\<forall> s \<in> set ST. s \<rightarrow>* v)
      \<and> set ST \<subseteq> {x. V x}
      \<and> liveness_compatible P'
      \<and> (\<forall> v \<in> {v'. v \<rightarrow> v'} - it. (\<exists> v' \<in> P'. v \<preceq> v'))
      \<and> distinct ST
    )
  "

  define Termination :: "(('a set \<times> 'a list \<times> 'a) \<times> 'a set \<times> 'a list \<times> 'a) set" where
    "Termination = inv_image (finite_psupset {x. V x}) (\<lambda> (a,b,c). set b)"

  have rpre_init: "rpre (P, [], a\<^sub>0)"
    unfolding rpre_def using \<open>V a\<^sub>0\<close> \<open>liveness_compatible P\<close> \<open>P \<subseteq> _\<close> by auto

  have wf: "wf Termination"
    unfolding Termination_def by (blast intro: finite_V)

  have successors_finite: "finite {v'. v \<rightarrow> v'}" for v
    using finite_V unfolding G.E'_def by auto

  show ?thesis
    unfolding dfs_def dfs_spec_def
    apply (refine_rcg refine_vcg)
    apply (rule Orderings.order.trans)
     apply(rule RECT_rule[where
          pre = rpre and
          V = Termination and
          M = "\<lambda>x. SPEC (rpost x)"
          ])

      (* Trimono *)
      subgoal
        unfolding FOREACHcd_def by refine_mono

      (* Termination *)
       apply (rule wf; fail)

      (* Precondition holds initially *)
      apply (rule rpre_init; fail)

     defer

    (* The postcondition establishes the specification *)
    subgoal
      apply refine_vcg
      unfolding rpost_def pre_cycle_cycle
      including graph_automation
      by (auto dest: liveness_compatible_cycle_start)

    apply (thin_tac "_ = f")

    (* Pre \<longrightarrow> Post *)
    apply refine_vcg

    (*
    (* Assertion *)
    subgoal for f x a b aa ba
      unfolding rpre_def by auto

    (* Assertion *)
    subgoal for f x a b aa ba
      unfolding rpre_def by auto
    *)

    (* Cycle found *)
    subgoal for f x a b aa ba
      by (subst rpost_def, subst (asm) (2) rpre_def, auto 4 4 dest: check_loop_loop)

    (* Subsumption *)
    subgoal for f x P b ST v
      by (subst rpost_def, subst (asm) (2) rpre_def, force)

    (* Foreach *)
    subgoal for f x P b ST v

      thm nfoldli_rule
      apply (refine_vcg
          FOREACHcd_rule[where I = "inv P (v # ST) v"]
          )
         apply clarsimp_all
        (*
      (* Finitely Branching *)
      subgoal
        thm succs_correct
        apply (auto intro: successors_finite simp: rpre_def rpost_def succs_correct)
          apply (subst succs_correct)
          oops
*)

      (* Finitely Branching *)
      subgoal
        by (auto intro: successors_finite)

      (* Pre \<longrightarrow> Invariant *)
      subgoal
        using \<open>V a\<^sub>0\<close>
        by (
          subst (asm) (2) rpre_def, subst inv_def,
          auto dest: check_loop_no_loop
        )

      (* Invariant *)
      subgoal for _ it v' P' ST' c
        apply (rule Orderings.order.trans)
         apply rprems

        (* Inv \<longrightarrow> Pre *)
        subgoal
          apply (subst rpre_def, subst (asm) inv_def)
          apply clarsimp
          subgoal premises prems
          proof -
            from prems \<open>V a\<^sub>0\<close> have "v \<rightarrow> v'"
              by auto
            with prems show ?thesis
              by (auto intro: G.E'_V2)
          qed
          done

        (* Termination *)
        subgoal
          using \<open>V a\<^sub>0\<close> unfolding Termination_def
          by (auto simp: finite_psupset_def inv_def intro: G.subgraphI)

        (* Post \<longrightarrow> Inv *)
        subgoal
          apply (subst inv_def, subst (asm) inv_def, subst rpost_def)
          apply (clarsimp simp: it_step_insert_iff)
          by (safe; (intro exI conjI)?; (blast intro: rtranclp_trans))

        done

      (* Cycle \<longrightarrow> Assertion *)
      subgoal
        by (subst (asm) inv_def, simp)

      (* Cycle \<longrightarrow> Post *)
      subgoal for P' ST' c
        using \<open>V a\<^sub>0\<close> by (subst rpost_def, subst (asm) inv_def, auto)

      (* No cycle \<longrightarrow> Assertion *)
      subgoal
        by (subst (asm) inv_def, simp)

      (* No cycle \<longrightarrow> Post *)
      subgoal for P' ST'
        using \<open>V a\<^sub>0\<close>
        by (subst rpost_def, subst (asm) inv_def, auto intro: liveness_compatible_inv G.subgraphI)

      done
    done
qed

end (* Search Space Finite Strict *)

locale Liveness_Search_Space_Defs =
  Search_Space_Nodes_Defs +
  fixes succs :: "'a \<Rightarrow> 'a list"
begin

definition dfs1 :: "'a set \<Rightarrow> (bool \<times> 'a set) nres" where
  "dfs1 P \<equiv> do {
    (P,ST,r) \<leftarrow> RECT (\<lambda>dfs (P,ST,v).
      do {
        ASSERT (V v \<and> set ST \<subseteq> {x. V x});
        if check_loop v ST then RETURN (P, ST, True)
        else do {
          if \<exists> v' \<in> P. v \<preceq> v' then
            RETURN (P, ST, False)
          else do {
              let ST = v # ST;
              (P, ST', r) \<leftarrow>
                nfoldli (succs v) (\<lambda>(_,_,b). \<not>b) (\<lambda>v' (P,ST,_). dfs (P,ST,v')) (P,ST,False);
              ASSERT (ST' = ST);
              let ST = tl ST';
              let P = insert v P;
              RETURN (P, ST, r)
            }
        }
      }
    ) (P,[],a\<^sub>0);
    RETURN (r, P)
  }"

end (* Liveness Search Space Defs *)

locale Liveness_Search_Space =
  Liveness_Search_Space_Defs +
  Liveness_Search_Space_pre +
  assumes succs_correct: "V a \<Longrightarrow> set (succs a) = {x. a \<rightarrow> x}"
  assumes finite_V: "finite {a. V a}"
begin

(* XXX
  The following complications only arise because we add the assertion in this refinement step.
*)
lemma succs_ref[refine]:
  "(succs a, succs b) \<in> \<langle>Id\<rangle>list_rel" if "(a, b) \<in> Id"
  using that by auto

lemma start_ref[refine]:
  "((P, [], a\<^sub>0), P, [], a\<^sub>0) \<in> Id \<times>\<^sub>r br id (\<lambda> xs. set xs \<subseteq> {x. V x}) \<times>\<^sub>r br id V" if "V a\<^sub>0"
  using that by (auto simp: br_def)

lemma refine_aux[refine]:
  "((x, x1c, True), x', x1a, True) \<in> Id \<times>\<^sub>r br id (\<lambda>xs. set xs \<subseteq> Collect V) \<times>\<^sub>r Id"
  if "(x1c, x1a) \<in> br id (\<lambda>xs. set xs \<subseteq> {x. V x})" "(x, x') \<in> Id"
  using that by auto

lemma refine_loop:
  "(\<And>x x'. (x, x') \<in> Id \<times>\<^sub>r br id (\<lambda>xs. set xs \<subseteq> {x. V x}) \<times>\<^sub>r br id V \<Longrightarrow>
            dfs' x \<le> \<Down> (Id \<times>\<^sub>r br id (\<lambda>xs. set xs \<subseteq> Collect V) \<times>\<^sub>r bool_rel) (dfsa x')) \<Longrightarrow>
   (x, x') \<in> Id \<times>\<^sub>r br id (\<lambda>xs. set xs \<subseteq> {x. V x}) \<times>\<^sub>r br id V \<Longrightarrow>
   x2 = (x1a, x2a) \<Longrightarrow>
   x' = (x1, x2) \<Longrightarrow>
   x2b = (x1c, x2c) \<Longrightarrow>
   x = (x1b, x2b) \<Longrightarrow>
   nfoldli (succs x2c) (\<lambda>(_, _, b). \<not> b) (\<lambda>v' (P, ST, _). dfs' (P, ST, v')) (x1b, x2c # x1c, False)
   \<le> \<Down> (Id \<times>\<^sub>r br id (\<lambda>xs. set xs \<subseteq> {x. V x}) \<times>\<^sub>r bool_rel)
       (FOREACHcd {v'. x2a \<rightarrow> v'} (\<lambda>(_, _, b). \<not> b)
          (\<lambda>v' (P, ST, _). dfsa (P, ST, v')) (x1, x2a # x1a, False))"
  apply (subgoal_tac "(succs x2c, succs x2a) \<in> \<langle>br id V\<rangle>list_rel")

  unfolding FOREACHcd_def
   apply refine_rcg
   apply (rule rhs_step_bind_SPEC)
    apply (rule succs_correct)
    apply (auto simp: br_def; fail)
   apply (erule nfoldli_refine)
     apply (auto simp: br_def; fail)
    apply (auto simp: br_def; fail)
   apply (auto simp: br_def; fail)
  unfolding br_def list_rel_def
  by (simp, rule list.rel_refl_strong, auto intro: G.E'_V2 simp: succs_correct)

lemma dfs1_dfs_ref[refine]:
  "dfs1 P \<le> \<Down> Id (dfs P)" if "V a\<^sub>0"
  using that unfolding dfs1_def dfs_def
  apply refine_rcg
            apply (auto simp: br_def; fail)+
     apply (rule refine_loop; assumption)
  by (auto simp: br_def)

end (* Liveness Search Space *)

end (* Theory *)
