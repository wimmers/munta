theory Simulation_Graphs
  imports
    TA_Library.CTL
    TA_Library.More_List
begin

lemmas [simp] = holds.simps

chapter \<open>Simulation Graphs\<close>

section \<open>Simulation Graphs\<close>

locale Simulation_Graph_Defs = Graph_Defs C for C :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes A :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"
begin

sublocale Steps: Graph_Defs A .

abbreviation "Steps \<equiv> Steps.steps"
abbreviation "Run \<equiv> Steps.run"

lemmas Steps_appendD1 = Steps.steps_appendD1

lemmas Steps_appendD2 = Steps.steps_appendD2

lemmas steps_alt_induct = Steps.steps_alt_induct

lemmas Steps_appendI = Steps.steps_appendI

lemmas Steps_cases = Steps.steps.cases

end (* Simulation Graph *)

locale Simulation_Graph_Poststable = Simulation_Graph_Defs +
  assumes poststable: "A S T \<Longrightarrow> \<forall> s' \<in> T. \<exists> s \<in> S. C s s'"

locale Simulation_Graph_Prestable = Simulation_Graph_Defs +
  assumes prestable: "A S T \<Longrightarrow> \<forall> s \<in> S. \<exists> s' \<in> T. C s s'"

locale Double_Simulation_Defs =
  fixes C :: "'a \<Rightarrow> 'a \<Rightarrow> bool" \<comment> \<open>Concrete step relation\<close>
    and A1 :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" \<comment> \<open>Step relation for the first abstraction layer\<close>
    and P1 :: "'a set \<Rightarrow> bool" \<comment> \<open>Valid states of the first abstraction layer\<close>
    and A2 :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" \<comment> \<open>Step relation for the second abstraction layer\<close>
    and P2 :: "'a set \<Rightarrow> bool" \<comment> \<open>Valid states of the second abstraction layer\<close>
begin

sublocale Simulation_Graph_Defs C A2 .

sublocale pre_defs: Simulation_Graph_Defs C A1 .

definition "closure a = {x. P1 x \<and> a \<inter> x \<noteq> {}}"

definition "A2' a b \<equiv> \<exists> x y. a = closure x \<and> b = closure y \<and> A2 x y"

sublocale post_defs: Simulation_Graph_Defs A1 A2' .

lemma closure_mono:
  "closure a \<subseteq> closure b" if "a \<subseteq> b"
  using that unfolding closure_def by auto

lemma closure_intD:
  "x \<in> closure a \<and> x \<in> closure b" if "x \<in> closure (a \<inter> b)"
  using that closure_mono by blast

end (* Double Simulation Graph Defs *)

locale Double_Simulation = Double_Simulation_Defs +
  assumes prestable: "A1 S T \<Longrightarrow> \<forall> s \<in> S. \<exists> s' \<in> T. C s s'"
      and closure_poststable: "s' \<in> closure y \<Longrightarrow> A2 x y \<Longrightarrow> \<exists>s\<in>closure x. A1 s s'"
      and P1_distinct: "P1 x \<Longrightarrow> P1 y \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<inter> y = {}"
      and P1_finite: "finite {x. P1 x}"
      and P2_cover: "P2 a \<Longrightarrow> \<exists> x. P1 x \<and> x \<inter> a \<noteq> {}"
begin

sublocale post: Simulation_Graph_Poststable A1 A2'
  unfolding A2'_def by standard (auto dest: closure_poststable)

sublocale pre: Simulation_Graph_Prestable C A1
  by standard (rule prestable)

end (* Double Simulation *)

locale Finite_Graph = Graph_Defs +
  fixes x\<^sub>0
  assumes finite_reachable: "finite {x. E\<^sup>*\<^sup>* x\<^sub>0 x}"

locale Simulation_Graph_Complete_Defs =
  Simulation_Graph_Defs C A for C :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and A :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" +
  fixes P :: "'a set \<Rightarrow> bool" \<comment> \<open>well-formed abstractions\<close>

locale Simulation_Graph_Complete = Simulation_Graph_Complete_Defs +
  simulation: Simulation_Invariant C A "(\<in>)" "\<lambda> _. True" P
begin

lemmas complete = simulation.A_B_step
lemmas P_invariant = simulation.B_invariant

end

locale Simulation_Graph_Finite_Complete = Simulation_Graph_Complete +
  fixes a\<^sub>0
  assumes finite_abstract_reachable: "finite {a. A\<^sup>*\<^sup>* a\<^sub>0 a}"
begin

sublocale Steps_finite: Finite_Graph A a\<^sub>0
  by standard (rule finite_abstract_reachable)

end (* Simulation Graph Finite Complete *)

locale Double_Simulation_Complete = Double_Simulation +
  fixes a\<^sub>0
  assumes complete: "C x y \<Longrightarrow> x \<in> S \<Longrightarrow> P2 S \<Longrightarrow> \<exists> T. A2 S T \<and> y \<in> T"
  assumes P2_invariant: "P2 a \<Longrightarrow> A2 a a' \<Longrightarrow> P2 a'"
      and P2_a\<^sub>0: "P2 a\<^sub>0"
begin

sublocale Simulation_Graph_Complete C A2 P2
  by standard (blast intro: complete P2_invariant)+

sublocale P2_invariant: Graph_Invariant_Start A2 a\<^sub>0 P2
  by (standard; blast intro: P2_invariant P2_a\<^sub>0)

end (* Double Simulation Finite Complete *)

locale Double_Simulation_Finite_Complete = Double_Simulation_Complete +
  assumes finite_abstract_reachable: "finite {a. A2\<^sup>*\<^sup>* a\<^sub>0 a}"
begin

sublocale Simulation_Graph_Finite_Complete C A2 P2 a\<^sub>0
  by standard (blast intro: complete finite_abstract_reachable P2_invariant)+

end (* Double Simulation Finite Complete *)

locale Simulation_Graph_Complete_Prestable = Simulation_Graph_Complete + Simulation_Graph_Prestable
begin

sublocale Graph_Invariant A P by standard (rule P_invariant)

end (* Simulation Graph Complete Prestable *)

locale Double_Simulation_Complete_Bisim = Double_Simulation_Complete +
assumes A1_complete: "C x y \<Longrightarrow> P1 S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists> T. A1 S T \<and> y \<in> T"
      and P1_invariant: "P1 S \<Longrightarrow> A1 S T \<Longrightarrow> P1 T"
begin

sublocale bisim: Simulation_Graph_Complete_Prestable C A1 P1
  by standard (blast intro: A1_complete P1_invariant)+

end (* Double Simulation Finite Complete Bisim *)

locale Double_Simulation_Finite_Complete_Bisim =
  Double_Simulation_Finite_Complete + Double_Simulation_Complete_Bisim

locale Double_Simulation_Complete_Bisim_Cover = Double_Simulation_Complete_Bisim +
  assumes P2_P1_cover: "P2 a \<Longrightarrow> x \<in> a \<Longrightarrow> \<exists> a'. a \<inter> a' \<noteq> {} \<and> P1 a' \<and> x \<in> a'"

locale Double_Simulation_Finite_Complete_Bisim_Cover =
  Double_Simulation_Finite_Complete_Bisim + Double_Simulation_Complete_Bisim_Cover

locale Double_Simulation_Complete_Abstraction_Prop =
  Double_Simulation_Complete +
  fixes \<phi> :: "'a \<Rightarrow> bool" \<comment> \<open>The property we want to check\<close>
  assumes \<phi>_A1_compatible: "A1 a b \<Longrightarrow> b \<subseteq> {x. \<phi> x} \<or> b \<inter> {x. \<phi> x} = {}"
      and \<phi>_P2_compatible: "P2 a \<Longrightarrow> a \<inter> {x. \<phi> x} \<noteq> {} \<Longrightarrow> P2 (a \<inter> {x. \<phi> x})"
      and \<phi>_A2_compatible: "A2\<^sup>*\<^sup>* a\<^sub>0 a \<Longrightarrow> a \<inter> {x. \<phi> x} \<noteq> {} \<Longrightarrow> A2\<^sup>*\<^sup>* a\<^sub>0 (a \<inter> {x. \<phi> x})"
      and P2_non_empty: "P2 a \<Longrightarrow> a \<noteq> {}"

locale Double_Simulation_Complete_Abstraction_Prop_Bisim =
  Double_Simulation_Complete_Abstraction_Prop + Double_Simulation_Complete_Bisim

locale Double_Simulation_Finite_Complete_Abstraction_Prop =
  Double_Simulation_Complete_Abstraction_Prop + Double_Simulation_Finite_Complete

locale Double_Simulation_Finite_Complete_Abstraction_Prop_Bisim =
  Double_Simulation_Finite_Complete_Abstraction_Prop + Double_Simulation_Finite_Complete_Bisim

section \<open>Poststability\<close>

context Simulation_Graph_Poststable
begin

lemma Steps_poststable:
  "\<exists> xs. steps xs \<and> list_all2 (\<in>) xs as \<and> last xs = x" if "Steps as" "x \<in> last as"
  using that
proof induction
  case (Single a)
  then show ?case by auto
next
  case (Cons a b as)
  then guess xs by clarsimp
  then have "hd xs \<in> b" by (cases xs) auto
  with poststable[OF \<open>A a b\<close>] obtain y where "y \<in> a" "C y (hd xs)" by auto
  with \<open>list_all2 _ _ _\<close> \<open>steps _\<close> \<open>x = _\<close> show ?case by (cases xs) auto
qed

lemma reaches_poststable:
  "\<exists> x \<in> a. reaches x y" if "Steps.reaches a b" "y \<in> b"
  using that unfolding reaches_steps_iff Steps.reaches_steps_iff
  apply clarify
  apply (drule Steps_poststable, assumption)
  apply clarify
  subgoal for as xs
    apply (cases "xs = []")
     apply force
    apply (rule bexI[where x = "hd xs"])
    using list.rel_sel by (auto dest: Graph_Defs.steps_non_empty')
  done    

lemma Steps_steps_cycle:
  "\<exists> x xs. steps (x # xs @ [x]) \<and> (\<forall> x \<in> set xs. \<exists> a \<in> set as \<union> {a}. x \<in> a) \<and> x \<in> a"
  if assms: "Steps (a # as @ [a])" "finite a" "a \<noteq> {}"
proof -
  define E where
    "E x y = (\<exists> xs. steps (x # xs @ [y]) \<and> (\<forall> x \<in> set xs \<union> {x, y}. \<exists> a \<in> set as \<union> {a}. x \<in> a))"
    for x y
  from assms(2-) have "\<exists> x. E x y \<and> x \<in> a" if "y \<in> a" for y
    using that unfolding E_def
    apply simp
    apply (drule Steps_poststable[OF assms(1), simplified])
    apply clarify
    subgoal for xs
      apply (inst_existentials "hd xs" "tl (butlast xs)")
      subgoal by (cases xs) auto
      subgoal by (auto elim: steps.cases dest!: list_all2_set1)
      subgoal by (drule list_all2_set1) (cases xs, auto dest: in_set_butlastD)
      by (cases xs) auto
    done
  with \<open>finite a\<close> \<open>a \<noteq> {}\<close> obtain x y where cycle: "E x y" "E\<^sup>*\<^sup>* y x" "x \<in> a"
    by (force dest!: directed_graph_indegree_ge_1_cycle'[where E = E])
  have trans[intro]: "E x z" if "E x y" "E y z" for x y z
    using that unfolding E_def
    apply safe
    subgoal for xs ys
      apply (inst_existentials "xs @ y # ys")
       apply (drule steps_append, assumption; simp; fail)
      by (cases ys, auto dest: list.set_sel(2)[rotated] elim: steps.cases)
    done
  have "E x z" if "E\<^sup>*\<^sup>* y z" "E x y" "x \<in> a" for x y z
  using that proof induction
    case base
    then show ?case unfolding E_def by force
  next
    case (step y z)
    then show ?case by auto
  qed
  with cycle have "E x x" by blast
  with \<open>x \<in> a\<close> show ?thesis unfolding E_def by auto
qed

end (* Simulation Graph Poststable *)

section \<open>Prestability\<close>

context Simulation_Graph_Prestable
begin

lemma Steps_prestable:
  "\<exists> xs. steps (x # xs) \<and> list_all2 (\<in>) (x # xs) as" if "Steps as" "x \<in> hd as"
  using that
proof (induction arbitrary: x)
  case (Single a)
  then show ?case by auto
next
  case (Cons a b as)
  from prestable[OF \<open>A a b\<close>] \<open>x \<in> _\<close> obtain y where "y \<in> b" "C x y" by auto
  with Cons.IH[of y] guess xs by clarsimp
  with \<open>x \<in> _\<close> show ?case by auto
qed

lemma reaches_prestable:
  "\<exists> y. reaches x y \<and> y \<in> b" if "Steps.reaches a b" "x \<in> a"
  using that unfolding reaches_steps_iff Steps.reaches_steps_iff
  by (force simp: hd_map last_map dest: list_all2_last dest!: Steps_prestable)

text \<open>Abstract cycles lead to concrete infinite runs.\<close>
lemma Steps_run_cycle_buechi:
  "\<exists> xs. run (x ## xs) \<and> stream_all2 (\<in>) xs (cycle (as @ [a]))"
  if assms: "Steps (a # as @ [a])" "x \<in> a"
proof -
  note C = Steps_prestable[OF assms(1), simplified]
  define P where "P \<equiv> \<lambda> x xs. steps (last x # xs) \<and> list_all2 (\<in>) xs (as @ [a])"
  define f where "f \<equiv> \<lambda> x. SOME xs. P x xs"
  from Steps_prestable[OF assms(1)] \<open>x \<in> a\<close> obtain ys where ys:
    "steps (x # ys)" "list_all2 (\<in>) (x # ys) (a # as @ [a])"
    by auto
  define xs where "xs = flat (siterate f ys)"
  from ys have "P [x] ys" unfolding P_def by auto
  from \<open>P _ _\<close> have *: "\<exists> xs. P xs ys" by blast
  have P_1[intro]:"ys \<noteq> []" if "P xs ys" for xs ys using that unfolding P_def by (cases ys) auto
  have P_2[intro]: "last ys \<in> a" if "P xs ys" for xs ys
    using that P_1[OF that] unfolding P_def by (auto dest:  list_all2_last)
  from * have "stream_all2 (\<in>) xs (cycle (as @ [a]))"
    unfolding xs_def proof (coinduction arbitrary: ys rule: stream_rel_coinduct_shift)
    case prems: stream_rel
    then have "ys \<noteq> []" "last ys \<in> a" by (blast dest: P_1 P_2)+
    from \<open>ys \<noteq> []\<close> C[OF \<open>last ys \<in> a\<close>] have "\<exists> xs. P ys xs" unfolding P_def by auto
    from someI_ex[OF this] have "P ys (f ys)" unfolding f_def .
    with \<open>ys \<noteq> []\<close> prems show ?case
      apply (inst_existentials ys "flat (siterate f (f ys))" "as @ [a]" "cycle (as @ [a])")
           apply (subst siterate.ctr; simp; fail)
          apply (subst cycle_decomp; simp; fail)
       by (auto simp: P_def)
  qed
  from * have "run xs"
    unfolding xs_def proof (coinduction arbitrary: ys rule: run_flat_coinduct)
    case prems: (run_shift xs ws xss ys)
    then have "ys \<noteq> []" "last ys \<in> a" by (blast dest: P_1 P_2)+
    from \<open>ys \<noteq> []\<close> C[OF \<open>last ys \<in> a\<close>] have "\<exists> xs. P ys xs" unfolding P_def by auto
    from someI_ex[OF this] have "P ys (f ys)" unfolding f_def .
    with \<open>ys \<noteq> []\<close> prems show ?case by (auto elim: steps.cases simp: P_def)
  qed
  with P_1[OF \<open>P _ _\<close>] \<open>steps (x # ys)\<close> have "run (x ## xs)"
    unfolding xs_def
    by (subst siterate.ctr, subst (asm) siterate.ctr) (cases ys; auto elim: steps.cases)
  with \<open>stream_all2 _ _ _\<close> show ?thesis by blast
qed

lemma Steps_run_cycle_buechi'':
  "\<exists> xs. run (x ## xs) \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> a) \<and> infs (\<lambda>x. x \<in> b) (x ## xs)"
  if assms: "Steps (a # as @ [a])" "x \<in> a" "b \<in> set (a # as @ [a])"
  using Steps_run_cycle_buechi[OF that(1,2)] that(2,3)
  apply safe
  apply (rule exI conjI)+
   apply assumption
  apply (subst alw_ev_stl[symmetric])
  by (force dest: alw_ev_HLD_cycle[of _ _ b] stream_all2_sset1)

lemma Steps_run_cycle_buechi':
  "\<exists> xs. run (x ## xs) \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> a) \<and> infs (\<lambda>x. x \<in> a) (x ## xs)"
  if assms: "Steps (a # as @ [a])" "x \<in> a"
  using Steps_run_cycle_buechi''[OF that] \<open>x \<in> a\<close> by auto

lemma Steps_run_cycle':
  "\<exists> xs. run (x ## xs) \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> a)"
  if assms: "Steps (a # as @ [a])" "x \<in> a"
  using Steps_run_cycle_buechi'[OF assms] by auto

lemma Steps_run_cycle:
  "\<exists> xs. run xs \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> a) \<and> shd xs \<in> a"
  if assms: "Steps (a # as @ [a])" "a \<noteq> {}"
  using Steps_run_cycle'[OF assms(1)] assms(2) by force

paragraph \<open>Unused\<close>

lemma Steps_cycle_every_prestable':
  "\<exists> b y. C x y \<and> y \<in> b \<and> b \<in> set as \<union> {a}"
  if assms: "Steps (as @ [a])" "x \<in> b" "b \<in> set as"
  using assms
proof (induction "as @ [a]" arbitrary: as)
  case Single
  then show ?case by simp
next
  case (Cons a c xs)
  show ?case
  proof (cases "a = b")
    case True
    with prestable[OF \<open>A a c\<close>] \<open>x \<in> b\<close> obtain y where "y \<in> c" "C x y"
      by auto
    with \<open>a # c # _ = _\<close> show ?thesis
      apply (inst_existentials c y)
    proof (assumption+, cases as, goal_cases)
      case (2 a list)
      then show ?case by (cases list) auto
    qed simp
  next
    case False
    with Cons.hyps(3)[of "tl as"] Cons.prems Cons.hyps(1,2,4-) show ?thesis by (cases as) auto
  qed
qed

lemma Steps_cycle_first_prestable:
  "\<exists> b y. C x y \<and> x \<in> b \<and> b \<in> set as \<union> {a}" if assms: "Steps (a # as @ [a])" "x \<in> a"
proof (cases as)
  case Nil
  with assms show ?thesis by (auto elim!: Steps_cases dest: prestable)
next
  case (Cons b as)
  with assms show ?thesis by (auto 4 4 elim: Steps_cases dest: prestable)
qed

lemma Steps_cycle_every_prestable:
  "\<exists> b y. C x y \<and> y \<in> b \<and> b \<in> set as \<union> {a}"
  if assms: "Steps (a # as @ [a])" "x \<in> b" "b \<in> set as \<union> {a}"
  using assms Steps_cycle_every_prestable'[of "a # as" a] Steps_cycle_first_prestable by auto

end (* Simulation Graph Prestable *)


section \<open>Double Simulation\<close>

context Double_Simulation
begin

lemma closure_involutive:
  "closure (\<Union> (closure x)) = closure x"
  unfolding closure_def by (auto dest: P1_distinct)

lemma closure_finite:
  "finite (closure x)"
  using P1_finite unfolding closure_def by auto

lemma closure_non_empty:
  "closure x \<noteq> {}" if "P2 x"
  using that unfolding closure_def by (auto dest!: P2_cover)

lemma P1_closure_id:
  "closure R = {R}" if "P1 R" "R \<noteq> {}"
  unfolding closure_def using that P1_distinct by blast

lemma A2'_A2_closure:
  "A2' (closure x) (closure y)" if "A2 x y"
  using that unfolding A2'_def by auto

lemma Steps_Union:
  "post_defs.Steps (map closure xs)" if "Steps xs"
using that proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc y xs)
  show ?case
  proof (cases xs rule: rev_cases)
    case Nil
    then show ?thesis by auto
  next
    case (snoc ys z)
    with Steps_appendD1[OF \<open>Steps (xs @ [y])\<close>] have "Steps xs" by simp
    then have *: "post_defs.Steps (map closure xs)" by (rule snoc.IH)
    with \<open>xs = _\<close> snoc.prems have "A2 z y"
      by (metis Steps.steps_appendD3 append_Cons append_assoc append_self_conv2)
    with \<open>A2 z y\<close> have "A2' (closure z) (closure y)" by (auto dest!: A2'_A2_closure)
    with * post_defs.Steps_appendI show ?thesis
      by (simp add: \<open>xs = _\<close>)
  qed
qed

lemma closure_reaches:
  "post_defs.Steps.reaches (closure x) (closure y)" if "Steps.reaches x y"
  using that
  unfolding Steps.reaches_steps_iff post_defs.Steps.reaches_steps_iff
  apply clarify
  apply (drule Steps_Union)
  subgoal for xs
    by (cases "xs = []"; force simp: hd_map last_map)
  done

lemma post_Steps_non_empty:
  "x \<noteq> {}" if "post_defs.Steps (a # as)" "x \<in> b" "b \<in> set as"
  using that
proof (induction "a # as" arbitrary: a as)
  case Single
  then show ?case by auto
next
  case (Cons a c as)
  then show ?case by (auto simp: A2'_def closure_def)
qed

lemma Steps_run_cycle':
  "\<exists> xs. run xs \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> \<Union> a) \<and> shd xs \<in> \<Union> a"
  if assms: "post_defs.Steps (a # as @ [a])" "finite a" "a \<noteq> {}"
proof -
  from post.Steps_steps_cycle[OF assms] guess a1 as1 by safe
  note guessed = this
  from assms(1) \<open>a1 \<in> a\<close> have "a1 \<noteq> {}" by (auto dest!: post_Steps_non_empty)
  with guessed pre.Steps_run_cycle[of a1 as1] obtain xs where
    "run xs" "\<forall>x\<in>sset xs. \<exists>a\<in>set as1 \<union> {a1}. x \<in> a" "shd xs \<in> a1"
    by atomize_elim auto
  with guessed(2,3) show ?thesis
    by (inst_existentials xs) (metis Un_iff UnionI empty_iff insert_iff)+
qed

lemma Steps_run_cycle:
  "\<exists> xs. run xs \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> \<Union> (closure a)) \<and> shd xs \<in> \<Union> (closure a)"
  if assms: "Steps (a # as @ [a])" "P2 a"
proof -
  from Steps_Union[OF assms(1)] have "post_defs.Steps (closure a # map closure as @ [closure a])"
    by simp
  from Steps_run_cycle'[OF this closure_finite closure_non_empty[OF \<open>P2 a\<close>]]
    show ?thesis by (force dest: list_all2_set2)
qed

lemma Steps_run_cycle2:
  "\<exists> x xs. run (x ## xs) \<and> x \<in> \<Union> (closure a\<^sub>0)
  \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a} \<union> set bs. x \<in> \<Union> a)
  \<and> infs (\<lambda>x. x \<in> \<Union> a) (x ## xs)"
  if assms: "post_defs.Steps (closure a\<^sub>0 # as @ a # bs @ [a])" "a \<noteq> {}"
proof -
  note as1 = assms
  from
    post_defs.Steps.steps_decomp[of "closure a\<^sub>0 # as" "a # bs @ [a]"]
    as1(1)[unfolded this]
  have *:
    "post_defs.Steps (closure a\<^sub>0 # as)"
    "post_defs.Steps (a # bs @ [a])"
    "A2' (last (closure a\<^sub>0 # as)) (a)"
    by (simp split: if_split_asm add: last_map)+
  then have "finite a"
    unfolding A2'_def by (metis closure_finite)
  from post.Steps_steps_cycle[OF *(2) \<open>finite a\<close> \<open>a \<noteq> {}\<close>] guess a1 as1
    by safe
  note as1 = this
  with post.poststable[OF *(3)] obtain a2 where "a2 \<in> last (closure a\<^sub>0 # as)" "A1 a2 a1"
    by auto
  with post.Steps_poststable[OF *(1), of a2] obtain as2 where as2:
    "pre_defs.Steps as2" "list_all2 (\<in>) as2 (closure a\<^sub>0 # as)" "last as2 = a2"
    by (auto split: if_split_asm simp: last_map)
  from as2(2) have "hd as2 \<in> closure a\<^sub>0" by (cases as2) auto
  then have "hd as2 \<noteq> {}" unfolding closure_def by auto
  then obtain x\<^sub>0 where "x\<^sub>0 \<in> hd as2" by auto
  from pre.Steps_prestable[OF as2(1) \<open>x\<^sub>0 \<in> _\<close>] obtain xs where xs:
    "steps (x\<^sub>0 # xs)" "list_all2 (\<in>) (x\<^sub>0 # xs) as2"
    by auto
  with \<open>last as2 = a2\<close> have "last (x\<^sub>0 # xs) \<in> a2"
    unfolding list_all2_Cons1 by (auto intro: list_all2_last)
  with pre.prestable[OF \<open>A1 a2 a1\<close>] obtain y where "C (last (x\<^sub>0 # xs)) y" "y \<in> a1" by auto
  from pre.Steps_run_cycle_buechi'[OF as1(1) \<open>y \<in> a1\<close>] obtain ys where ys:
    "run (y ## ys)" "\<forall>x\<in>sset ys. \<exists>a\<in>set as1 \<union> {a1}. x \<in> a" "infs (\<lambda>x. x \<in> a1) (y ## ys)"
    by auto
  from ys(3) \<open>a1 \<in> a\<close> have "infs (\<lambda>x. x \<in> \<Union> a) (y ## ys)"
    by (auto simp: HLD_iff elim!: alw_ev_mono)
  from extend_run[OF xs(1) \<open>C _ _\<close> \<open>run (y ## ys)\<close>] have "run ((x\<^sub>0 # xs) @- y ## ys)" by simp
  then show ?thesis
    apply (inst_existentials x\<^sub>0 "xs @- y ## ys")
      apply (simp; fail)
    using \<open>x\<^sub>0 \<in> _\<close> \<open>hd as2 \<in> _\<close> apply (auto; fail)
    using xs(2) as2(2) *(2) \<open>y \<in> a1\<close> \<open>a1 \<in> _\<close> ys(2) as1(2)
    unfolding list_all2_op_map_iff list_all2_Cons1 list_all2_Cons2
      apply auto
       apply (fastforce dest!: list_all2_set1)
     apply blast
    using \<open>infs (\<lambda>x. x \<in> \<Union> a) (y ## ys)\<close>
    by (simp add: sdrop_shift)
qed

lemma Steps_run_cycle'':
  "\<exists> x xs. run (x ## xs) \<and> x \<in> \<Union> (closure a\<^sub>0)
  \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a} \<union> set bs. x \<in> \<Union> (closure a))
  \<and> infs (\<lambda>x. x \<in> \<Union> (closure a)) (x ## xs)"
  if assms: "Steps (a\<^sub>0 # as @ a # bs @ [a])" "P2 a"
proof -
  from Steps_Union[OF assms(1)] have "post_defs.Steps (map closure (a\<^sub>0 # as @ a # bs @ [a]))"
    by simp
  from Steps_run_cycle2[OF this[simplified] closure_non_empty[OF \<open>P2 a\<close>]] show ?thesis
    by clarify (auto simp: image_def intro!: exI conjI)
qed

paragraph \<open>Unused\<close>

lemma post_Steps_P1:
  "P1 x" if "post_defs.Steps (a # as)" "x \<in> b" "b \<in> set as"
  using that
proof (induction "a # as" arbitrary: a as)
  case Single
  then show ?case by auto
next
  case (Cons a c as)
  then show ?case by (auto simp: A2'_def closure_def)
qed

lemma strong_compatibility_impl_weak:
  fixes \<phi> :: "'a \<Rightarrow> bool" \<comment> \<open>The property we want to check\<close>
  assumes \<phi>_closure_compatible: "\<And> x a. x \<in> a \<Longrightarrow> \<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union> (closure a). \<phi> x)"
  shows "\<phi> x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> \<phi> y"
  by (auto simp: closure_def dest: \<phi>_closure_compatible)

end (* Double Simulation Graph *)


section \<open>Finite Graphs\<close>

context Finite_Graph
begin

subsection \<open>Infinite Büchi Runs Correspond to Finite Cycles\<close>

lemma run_finite_state_set:
  assumes "run (x\<^sub>0 ## xs)"
  shows "finite (sset (x\<^sub>0 ## xs))"
proof -
  let ?S = "{x. E\<^sup>*\<^sup>* x\<^sub>0 x}"
  from run_reachable[OF assms] have "sset xs \<subseteq> ?S" unfolding stream.pred_set by auto
  moreover have "finite ?S" using finite_reachable by auto
  ultimately show ?thesis by (auto intro: finite_subset)
qed

lemma run_finite_state_set_cycle:
  assumes "run (x\<^sub>0 ## xs)"
  shows
    "\<exists> ys zs. run (x\<^sub>0 ## ys @- cycle zs) \<and> set ys \<union> set zs \<subseteq> {x\<^sub>0} \<union> sset xs \<and> zs \<noteq> []"
proof -
  from run_finite_state_set[OF assms] have "finite (sset (x\<^sub>0 ## xs))" .
  with sdistinct_infinite_sset[of "x\<^sub>0 ## xs"] not_sdistinct_decomp[of "x\<^sub>0 ## xs"] obtain x ws ys zs
    where "x\<^sub>0 ## xs = ws @- x ## ys @- x ## zs"
    by force
  then have decomp: "x\<^sub>0 ## xs = (ws @ [x]) @- ys @- x ## zs" by simp
  from run_decomp[OF assms[unfolded decomp]] guess by auto
  note decomp_first = this
  from run_sdrop[OF assms, of "length (ws @ [x])"] guess by simp
  moreover from decomp have "sdrop (length ws) xs = ys @- x ## zs"
    by (cases ws; simp add: sdrop_shift)
  ultimately have "run ((ys @ [x]) @- zs)" by simp
  from run_decomp[OF this] guess by clarsimp
  from run_cycle[OF this(1)] decomp_first have
    "run (cycle (ys @ [x]))"
    by (force split: if_split_asm)
  with
    extend_run[of "(ws @ [x])" "if ys = [] then shd (x ## zs) else hd ys" "stl (cycle (ys @ [x]))"]
    decomp_first
  have
    "run ((ws @ [x]) @- cycle (ys @ [x]))"
    apply (simp split: if_split_asm)
    subgoal
      using cycle_Cons[of x "[]", simplified] by auto
    apply (cases ys)
     apply (simp; fail)
    by (simp add: cycle_Cons)
  with decomp show ?thesis
    apply (inst_existentials "tl (ws @ [x])" "(ys @ [x])")
    by (cases ws; force)+
qed

(* XXX Duplication *)
lemma buechi_run_finite_state_set_cycle:
  assumes "run (x\<^sub>0 ## xs)" "alw (ev (holds \<phi>)) (x\<^sub>0 ## xs)"
  shows
  "\<exists> ys zs.
    run (x\<^sub>0 ## ys @- cycle zs) \<and> set ys \<union> set zs \<subseteq> {x\<^sub>0} \<union> sset xs
    \<and> zs \<noteq> [] \<and> (\<exists> x \<in> set zs. \<phi> x)"
proof -
  from run_finite_state_set[OF assms(1)] have "finite (sset (x\<^sub>0 ## xs))" .
  with sset_sfilter[OF \<open>alw (ev _) _\<close>] have "finite (sset (sfilter \<phi> (x\<^sub>0 ## xs)))"
    by (rule finite_subset)
  from finite_sset_sfilter_decomp[OF this assms(2)] obtain x ws ys zs where
    decomp: "x\<^sub>0 ## xs = (ws @ [x]) @- ys @- x ## zs" and "\<phi> x"
    by simp metis
  from run_decomp[OF assms(1)[unfolded decomp]] guess by auto
  note decomp_first = this
  from run_sdrop[OF assms(1), of "length (ws @ [x])"] guess by simp
  moreover from decomp have "sdrop (length ws) xs = ys @- x ## zs"
    by (cases ws; simp add: sdrop_shift)
  ultimately have "run ((ys @ [x]) @- zs)" by simp
  from run_decomp[OF this] guess by clarsimp
  from run_cycle[OF this(1)] decomp_first have
    "run (cycle (ys @ [x]))"
    by (force split: if_split_asm)
  with
    extend_run[of "(ws @ [x])" "if ys = [] then shd (x ## zs) else hd ys" "stl (cycle (ys @ [x]))"]
    decomp_first
  have
    "run ((ws @ [x]) @- cycle (ys @ [x]))"
    apply (simp split: if_split_asm)
    subgoal
      using cycle_Cons[of x "[]", simplified] by auto
    apply (cases ys)
     apply (simp; fail)
    by (simp add: cycle_Cons)
  with decomp \<open>\<phi> x\<close> show ?thesis
    apply (inst_existentials "tl (ws @ [x])" "(ys @ [x])")
    by (cases ws; force)+
qed

lemma run_finite_state_set_cycle_steps:
  assumes "run (x\<^sub>0 ## xs)"
  shows "\<exists> x ys zs. steps (x\<^sub>0 # ys @ x # zs @ [x]) \<and> {x} \<union> set ys \<union> set zs \<subseteq> {x\<^sub>0} \<union> sset xs"
proof -
  from run_finite_state_set_cycle[OF assms] guess ys zs by safe
  note guessed = this
  from \<open>zs \<noteq> []\<close> have "cycle zs = (hd zs # tl zs @ [hd zs]) @- cycle (tl zs @ [hd zs])"
    apply (cases zs)
     apply (simp; fail)
    apply simp
    apply (subst cycle_Cons[symmetric])
    apply (subst cycle_decomp)
    by simp+
  from guessed(1)[unfolded this] have
    "run ((x\<^sub>0 # ys @ hd zs # tl zs @ [hd zs]) @- cycle (tl zs @ [hd zs]))"
    by simp
  from run_decomp[OF this] guessed(2,3) show ?thesis
    by (inst_existentials "hd zs" ys "tl zs") (auto dest: list.set_sel)
qed

(* XXX Duplication *)
lemma buechi_run_finite_state_set_cycle_steps:
  assumes "run (x\<^sub>0 ## xs)" "alw (ev (holds \<phi>)) (x\<^sub>0 ## xs)"
  shows
  "\<exists> x ys zs.
    steps (x\<^sub>0 # ys @ x # zs @ [x]) \<and> {x} \<union> set ys \<union> set zs \<subseteq> {x\<^sub>0} \<union> sset xs
    \<and> (\<exists> y \<in> set (x # zs). \<phi> y)"
proof -
  from buechi_run_finite_state_set_cycle[OF assms] guess ys zs x by safe
  note guessed = this
  from \<open>zs \<noteq> []\<close> have "cycle zs = (hd zs # tl zs @ [hd zs]) @- cycle (tl zs @ [hd zs])"
    apply (cases zs)
     apply (simp; fail)
    apply simp
    apply (subst cycle_Cons[symmetric])
    apply (subst cycle_decomp)
    by simp+
  from guessed(1)[unfolded this] have
    "run ((x\<^sub>0 # ys @ hd zs # tl zs @ [hd zs]) @- cycle (tl zs @ [hd zs]))"
    by simp
  from run_decomp[OF this] guessed(2,3,4,5) show ?thesis
    by (inst_existentials "hd zs" ys "tl zs") (auto 4 4 dest: list.set_sel)
qed

lemma cycle_steps_run:
  assumes "steps (x\<^sub>0 # ys @ x # zs @ [x])"
  shows "\<exists> xs. run (x\<^sub>0 ## xs) \<and> sset xs = {x} \<union> set ys \<union> set zs"
proof -
  from assms have "steps (x\<^sub>0 # ys @ [x])" "steps (x # zs @ [x])"
    (* apply (smt Graph_Defs.stepsI append_eq_append_conv2 append_is_Nil_conv hd_append2 list.inject list.sel(1) list.simps(3) steps.cases steps_append_single steps_decomp) *)
     apply (metis Graph_Defs.steps_appendD1 append.assoc append_Cons append_Nil snoc_eq_iff_butlast)
    by (metis Graph_Defs.steps_appendD2 append_Cons assms snoc_eq_iff_butlast)
    
  (*
  proof -
    have f1: "\<forall>as asa asb p. ((asb::'a list) @ asa = [] \<or> Graph_Defs.steps p (asb @ asa)) \<or> \<not> Graph_Defs.steps p (asb @ asa @ as)"
      by (metis (no_types) Graph_Defs.steps_appendD1 append.assoc)
    have f2: "\<forall>as a. [a::'a] @ as = a # as"
      by simp
    have f3: "steps ((x\<^sub>0 # ys) @ (x # zs) @ [x])"
      using assms by fastforce
    have "(x\<^sub>0 # ys) @ x # zs \<noteq> []"
      by force
    then have "steps ((x\<^sub>0 # ys) @ [x])"
      using f3 f2 f1 by (metis snoc_eq_iff_butlast)
    then show "steps (x\<^sub>0 # ys @ [x])"
      by auto
  *)
  from this(2) have "x \<rightarrow> hd (zs @ [x])" "steps (zs @ [x])"
     apply (metis Graph_Defs.steps_decomp last_snoc list.sel(1) list.sel(3) snoc_eq_iff_butlast steps_ConsD steps_append')
    by (meson steps_ConsD \<open>steps (x # zs @ [x])\<close> snoc_eq_iff_butlast)
  from run_cycle[OF this(2)] this(1) have "run (cycle (zs @ [x]))" by auto
  with extend_run[OF \<open>steps (x\<^sub>0 # ys @ [x])\<close>, of "hd (zs @ [x])" "stl (cycle (zs @ [x]))"] \<open>x \<rightarrow> _\<close>
  have "run (x\<^sub>0 ## ys @- x ## cycle (zs @ [x]))"
    by simp (metis cycle.ctr)
  then show ?thesis
    by auto
qed

lemma buechi_run_lasso:
  assumes "run (x\<^sub>0 ## xs)" "alw (ev (holds \<phi>)) (x\<^sub>0 ## xs)"
  obtains x where "reaches x\<^sub>0 x" "reaches1 x x" "\<phi> x"
proof -
  from buechi_run_finite_state_set_cycle_steps[OF assms] obtain x ys zs y where
    "steps (x\<^sub>0 # ys @ x # zs @ [x])" "y \<in> set (x # zs)" "\<phi> y"
    by safe
  from \<open>y \<in> _\<close> consider "y = x" | as bs where "zs = as @ y # bs"
    by (meson set_ConsD split_list)
  then have "\<exists> as bs. steps (x\<^sub>0 # as @ [y]) \<and> steps (y # bs @ [y])"
  proof cases
    case 1
    (* XXX Decision procedure *)
    with \<open>steps _\<close> show ?thesis
      by simp (metis Graph_Defs.steps_appendD2 append.assoc append_Cons list.distinct(1))
next
  case 2
  with \<open>steps _\<close> show ?thesis
    by simp (metis (no_types)
        reaches1_steps steps_reaches append_Cons last_appendR list.distinct(1) list.sel(1)
        reaches1_reaches_iff2 reaches1_steps_append steps_decomp)
qed
  with \<open>\<phi> y\<close> show ?thesis
    including graph_automation by (intro that[of y]) (auto intro: steps_reaches1)
qed

end (* Finite Graph *)


section \<open>Complete Simulation Graphs\<close>

context Simulation_Graph_Defs
begin

definition "abstract_run x xs = x ## sscan (\<lambda> y a. SOME b. A a b \<and> y \<in> b) xs x"

lemma abstract_run_ctr:
  "abstract_run x xs = x ## abstract_run (SOME b. A x b \<and> shd xs \<in> b) (stl xs)"
  unfolding abstract_run_def by (subst sscan.ctr) (rule HOL.refl)

end

context Simulation_Graph_Complete
begin

lemma steps_complete:
  "\<exists> as. Steps (a # as) \<and> list_all2 (\<in>) xs as" if "steps (x # xs)" "x \<in> a" "P a"
  using that by (induction xs arbitrary: x a) (erule steps.cases; fastforce dest!: complete)+

lemma abstract_run_Run:
  "Run (abstract_run a xs)" if "run (x ## xs)" "x \<in> a" "P a"
  using that
proof (coinduction arbitrary: a x xs)
  case (run a x xs)
  obtain y ys where "xs = y ## ys" by (metis stream.collapse)
  with run have "C x y" "run (y ## ys)" by (auto elim: run.cases)
  from complete[OF \<open>C x y\<close> _ \<open>P a\<close> \<open>x \<in> a\<close>] obtain b where "A a b \<and> y \<in> b" by auto
  then have "A a (SOME b. A a b \<and> y \<in> b) \<and> y \<in> (SOME b. A a b \<and> y \<in> b)" by (rule someI)
  moreover with \<open>P a\<close> have "P (SOME b. A a b \<and> y \<in> b)" by (blast intro: P_invariant)
  ultimately show ?case using \<open>run (y ## ys)\<close> unfolding \<open>xs = _\<close>
    apply (subst abstract_run_ctr, simp)
    apply (subst abstract_run_ctr, simp)
    by (auto simp: abstract_run_ctr[symmetric])
qed

lemma abstract_run_abstract:
  "stream_all2 (\<in>) (x ## xs) (abstract_run a xs)" if "run (x ## xs)" "x \<in> a" "P a"
using that proof (coinduction arbitrary: a x xs)
  case run: (stream_rel x' u b' v a x xs)
  obtain y ys where "xs = y ## ys" by (metis stream.collapse)
  with run have "C x y" "run (y ## ys)" by (auto elim: run.cases)
  from complete[OF \<open>C x y\<close> _ \<open>P a\<close> \<open>x \<in> a\<close>] obtain b where "A a b \<and> y \<in> b" by auto
  then have "A a (SOME b. A a b \<and> y \<in> b) \<and> y \<in> (SOME b. A a b \<and> y \<in> b)" by (rule someI)
  with \<open>run (y ## ys)\<close> \<open>x \<in> a\<close> \<open>P a\<close> run(1,2) \<open>xs = _\<close> show ?case
    by (subst (asm) abstract_run_ctr) (auto intro: P_invariant)
qed

lemma run_complete:
  "\<exists> as. Run (a ## as) \<and> stream_all2 (\<in>) xs as" if "run (x ## xs)" "x \<in> a" "P a"
  using abstract_run_Run[OF that] abstract_run_abstract[OF that]
  apply (subst (asm) abstract_run_ctr)
  apply (subst (asm) (2) abstract_run_ctr)
  by auto

end (* Simulation Graph Complete Abstraction *)


subsection \<open>Runs in Finite Complete Graphs\<close>

context Simulation_Graph_Finite_Complete
begin

lemma run_finite_state_set_cycle_steps:
  assumes "run (x\<^sub>0 ## xs)" "x\<^sub>0 \<in> a\<^sub>0" "P a\<^sub>0"
  shows "\<exists> x ys zs.
    Steps (a\<^sub>0 # ys @ x # zs @ [x]) \<and> (\<forall> a \<in> {x} \<union> set ys \<union> set zs. \<exists> x \<in> {x\<^sub>0} \<union> sset xs. x \<in> a)"
  using run_complete[OF assms]
  apply safe
  apply (drule Steps_finite.run_finite_state_set_cycle_steps)
  apply safe
  subgoal for as x ys zs
    apply (inst_existentials x ys zs)
    using assms(2) by (auto dest: stream_all2_sset2)
  done

lemma buechi_run_finite_state_set_cycle_steps:
  assumes "run (x\<^sub>0 ## xs)" "x\<^sub>0 \<in> a\<^sub>0" "P a\<^sub>0" "alw (ev (holds \<phi>)) (x\<^sub>0 ## xs)"
  shows "\<exists> x ys zs.
    Steps (a\<^sub>0 # ys @ x # zs @ [x])
    \<and> (\<forall> a \<in> {x} \<union> set ys \<union> set zs. \<exists> x \<in> {x\<^sub>0} \<union> sset xs. x \<in> a)
    \<and> (\<exists> y \<in> set (x # zs). \<exists> a \<in> y. \<phi> a)"
  using run_complete[OF assms(1-3)]
  apply safe
  apply (drule Steps_finite.buechi_run_finite_state_set_cycle_steps[where \<phi> = "\<lambda> S. \<exists> x \<in> S. \<phi> x"])
  subgoal for as
    using assms(4)
    apply (subst alw_ev_stl[symmetric], simp)
    apply (erule alw_stream_all2_mono[where Q = "ev (holds \<phi>)"], fastforce)
    by (metis (mono_tags, lifting) ev_holds_sset stream_all2_sset1)
  apply safe
  subgoal for as x ys zs y a
    apply (inst_existentials x ys zs)
    using assms(2) by (auto dest: stream_all2_sset2)
  done

lemma buechi_run_finite_state_set_cycle_lasso:
  assumes "run (x\<^sub>0 ## xs)" "x\<^sub>0 \<in> a\<^sub>0" "P a\<^sub>0" "alw (ev (holds \<phi>)) (x\<^sub>0 ## xs)"
  shows "\<exists>a. Steps.reaches a\<^sub>0 a \<and> Steps.reaches1 a a \<and> (\<exists>y \<in> a. \<phi> y)"
proof -
  from buechi_run_finite_state_set_cycle_steps[OF assms] obtain b as bs a y where lasso:
    "Steps (a\<^sub>0 # as @ b # bs @ [b])" "a \<in> set (b # bs)" "y \<in> a" "\<phi> y"
    by safe
  from \<open>a \<in> set _\<close> consider "b = a" | bs1 bs2 where "bs = bs1 @ a # bs2"
    using split_list by fastforce
  then have "Steps.reaches a\<^sub>0 a \<and> Steps.reaches1 a a"
    using \<open>Steps _\<close>
    apply cases
     apply safe
    subgoal
      by (simp add: Steps.steps_reaches')
    subgoal
      by (blast dest: Steps.stepsD intro: Steps.steps_reaches1)
    subgoal for bs1 bs2
      by (subgoal_tac "Steps ((a\<^sub>0 # as @ b # bs1 @ [a]) @ (bs2 @ [b]))")
        (drule Steps.stepsD, auto elim: Steps.steps_reaches')
    subgoal
      by (metis (no_types)
          Steps.steps_reaches1 Steps.steps_rotate Steps_appendD2 append_Cons append_eq_append_conv2
          list.distinct(1))
    done
  with lasso show ?thesis
    by auto
qed

end (* Simulation Graph Finite Complete Abstraction *)

section \<open>Finite Complete Double Simulations\<close>

context Double_Simulation
begin

lemma Run_closure:
  "post_defs.Run (smap closure xs)" if "Run xs"
using that proof (coinduction arbitrary: xs)
  case prems: run
  then obtain x y ys where "xs = x ## y ## ys" "A2 x y" "Run (y ## ys)"
    by (auto elim: Steps.run.cases)
  with A2'_A2_closure[OF \<open>A2 x y\<close>] show ?case
    by force
qed

lemma closure_set_finite:
  "finite (closure ` UNIV)" (is "finite ?S")
proof -
  have "?S \<subseteq> {x. x \<subseteq> {x. P1 x}}"
    unfolding closure_def by auto
  also have "finite \<dots>"
    using P1_finite by auto
  finally show ?thesis .
qed

lemma A2'_empty_step:
  "b = {}" if "A2' a b" "a = {}"
  using that closure_poststable unfolding A2'_def by auto

lemma A2'_empty_invariant:
  "Graph_Invariant A2' (\<lambda> x. x = {})"
  by standard (rule A2'_empty_step)

end (* Double Simulation *)

context Double_Simulation_Complete
begin

lemmas P2_invariant_Steps = P2_invariant.invariant_steps

interpretation Steps_finite: Finite_Graph A2' "closure a\<^sub>0"
proof
  have "{x. post_defs.Steps.reaches (closure a\<^sub>0) x} \<subseteq> closure ` UNIV"
    by (auto 4 3 simp: A2'_def elim: rtranclp.cases)
  also have "finite \<dots>"
    by (fact closure_set_finite)
  finally show "finite {x. post_defs.Steps.reaches (closure a\<^sub>0) x}" .
qed

theorem infinite_run_cycle_iff':
  assumes "\<And> x xs. run (x ## xs) \<Longrightarrow> x \<in> \<Union>(closure a\<^sub>0) \<Longrightarrow> \<exists> y ys. y \<in> a\<^sub>0 \<and> run (y ## ys)"
  shows
    "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> \<Union> (closure a\<^sub>0) \<and> run (x\<^sub>0 ## xs)) \<longleftrightarrow>
     (\<exists> as a bs. post_defs.Steps (closure a\<^sub>0 # as @ a # bs @ [a]) \<and> a \<noteq> {})"
proof (safe, goal_cases)
  case prems: (1 x\<^sub>0 X xs)
  from assms[OF prems(1)] prems(2,3) obtain y ys where "y \<in> a\<^sub>0" "run (y ## ys)"
    by auto
  from run_complete[OF this(2,1) P2_a\<^sub>0] obtain as where "Run (a\<^sub>0 ## as)" "stream_all2 (\<in>) ys as"
    by auto
  from P2_invariant.invariant_run[OF \<open>Run _\<close>] have *: "\<forall> a \<in> sset (a\<^sub>0 ## as). P2 a"
    unfolding stream.pred_set by auto
  from Steps_finite.run_finite_state_set_cycle_steps[OF Run_closure[OF \<open>Run _\<close>, simplified]] show ?case
    using \<open>stream_all2 _ _ _\<close> \<open>y \<in> _\<close>  * closure_non_empty by force+
next
  case prems: (2 as a bs x)
  with post_defs.Steps.steps_decomp[of "closure a\<^sub>0 # as @ [a]" "bs @ [a]"] have
    "post_defs.Steps (closure a\<^sub>0 # as @ [a])" "post_defs.Steps (bs @ [a])" "A2' a (hd (bs @ [a]))"
    by auto
  from prems(2,3) Steps_run_cycle2[OF prems(1)] show ?case
    by auto
qed

corollary infinite_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs)) \<longleftrightarrow>
   (\<exists> as a bs. post_defs.Steps (closure a\<^sub>0 # as @ a # bs @ [a]) \<and> a \<noteq> {})"
  if "\<Union>(closure a\<^sub>0) = a\<^sub>0" "P2 a\<^sub>0"
  by (subst \<open>_ = a\<^sub>0\<close>[symmetric]) (rule infinite_run_cycle_iff', auto simp: that)

context
  fixes \<phi> :: "'a \<Rightarrow> bool" \<comment> \<open>The property we want to check\<close>
  assumes \<phi>_closure_compatible: "P2 a \<Longrightarrow> x \<in> \<Union> (closure a) \<Longrightarrow> \<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union> (closure a). \<phi> x)"
begin

text \<open>
  We need the condition \<open>a \<noteq> {}\<close> in the following theorem because we cannot prove a lemma like this:
\<close>

lemma
  "\<exists> bs. Steps bs \<and> closure a # as = map closure bs" if "post_defs.Steps (closure a # as)"
  using that
  oops

text \<open>One possible fix would be to add the stronger assumption \<open>A2 a b \<Longrightarrow> P2 b\<close>.\<close>

theorem infinite_buechi_run_cycle_iff_closure:
  assumes
    "\<And> x xs. run (x ## xs) \<Longrightarrow> x \<in> \<Union>(closure a\<^sub>0) \<Longrightarrow> alw (ev (holds \<phi>)) xs
      \<Longrightarrow> \<exists> y ys. y \<in> a\<^sub>0 \<and> run (y ## ys) \<and> alw (ev (holds \<phi>)) ys"
      and "\<And> a. P2 a \<Longrightarrow> a \<subseteq> \<Union> (closure a)"
  shows
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> \<Union> (closure a\<^sub>0) \<and> run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as a bs. a \<noteq> {} \<and> post_defs.Steps (closure a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall> x \<in> \<Union> a. \<phi> x))"
proof (safe, goal_cases)
  case prems: (1 x\<^sub>0 xs)
  from assms(1)[OF prems(3)] prems(1,2,4) obtain y ys where
    "y \<in> a\<^sub>0" "run (y ## ys)" "alw (ev (holds \<phi>)) ys"
    by auto
  from run_complete[OF this(2,1) P2_a\<^sub>0] obtain as where "Run (a\<^sub>0 ## as)" "stream_all2 (\<in>) ys as"
    by auto
  from P2_invariant.invariant_run[OF \<open>Run _\<close>] have "pred_stream P2 (a\<^sub>0 ## as)"
    by auto
  from Run_closure[OF \<open>Run _\<close>] have "post_defs.Run (closure a\<^sub>0 ## smap closure as)"
    by simp
  from \<open>alw (ev (holds \<phi>)) ys\<close> \<open>stream_all2 _ _ _\<close> have "alw (ev (holds (\<lambda> a. \<exists> x \<in> a. \<phi> x))) as"
    by (rule alw_ev_lockstep) auto
  then have "alw (ev (holds (\<lambda> a. \<exists> x \<in> \<Union> a. \<phi> x))) (closure a\<^sub>0 ## smap closure as)"
    apply -
    apply rule
    apply (rule alw_ev_lockstep[where Q = "\<lambda> a b. b = closure a \<and> P2 a"], assumption)
    subgoal
      using \<open>Run (a\<^sub>0 ## as)\<close>
      by - (rule stream_all2_combine[where P = "eq_onp P2" and Q = "\<lambda> a b. b = closure a"],
            subst stream.pred_rel[symmetric],
            auto dest: P2_invariant.invariant_run simp: stream.rel_refl eq_onp_def
           )
    subgoal for a x
      by (auto dest!: assms(2))
    done
  from Steps_finite.buechi_run_finite_state_set_cycle_steps[OF \<open>post_defs.Run (_ ## _)\<close> this]
  guess a ys zs
    by clarsimp
  note guessed = this
  from guessed(5) show ?case
  proof (standard, goal_cases)
    case prems: 1
    from guessed(1) have "post_defs.Steps (closure a\<^sub>0 # ys @ [a])"
      by (metis
          Graph_Defs.graphI(3) Graph_Defs.steps_decomp append.simps(2) list.sel(1) list.simps(3)
         )
    from \<open>pred_stream _ _\<close> guessed(2) obtain a' where "a = closure a'" "P2 a'"
      by (auto simp: stream.pred_set)
    from prems obtain x R where "x \<in> R" "R \<in> a" "\<phi> x" by auto
    with \<open>P2 a'\<close> have "\<forall> x \<in> \<Union> a. \<phi> x"
      unfolding \<open>a = _\<close> by (subst \<phi>_closure_compatible[symmetric]) auto
    with guessed(1,2) show ?case
      using \<open>R \<in> a\<close> by blast
  next
    case prems: 2
    then obtain R b x where *: "x \<in> R" "R \<in> b" "b \<in> set zs" "\<phi> x"
      by auto
    from \<open>b \<in> set zs\<close> obtain zs1 zs2 where "zs = zs1 @ b # zs2" by (force simp: split_list)
    with guessed(1) have "post_defs.Steps ((closure a\<^sub>0 # ys @ a # zs1 @ [b]) @ zs2 @ [a])"
      by simp
    with guessed(1) have "post_defs.Steps (closure a\<^sub>0 # ys @ a # zs1 @ [b])"
      by - (drule Graph_Defs.steps_decomp, auto)
    from \<open>pred_stream _ _\<close> guessed(4) \<open>zs = _\<close> obtain b' where "b = closure b'" "P2 b'"
      by (auto simp: stream.pred_set)
    with * have *: "\<forall> x \<in> \<Union> b. \<phi> x"
      unfolding \<open>b = _\<close> by (subst \<phi>_closure_compatible[symmetric]) auto
    from \<open>zs = _\<close> guessed(1) have "post_defs.Steps ((closure a\<^sub>0 # ys) @ (a # zs1 @ [b]) @ zs2 @ [a])"
      by simp
    then have "post_defs.Steps (a # zs1 @ [b])" by (blast dest!: post_defs.Steps.steps_decomp)
    with \<open>zs = _\<close> guessed * show ?case
      using
        \<open>R \<in> b\<close>
        post_defs.Steps.steps_append[of "closure a\<^sub>0 # ys @ a # zs1 @ b # zs2 @ [a]" "a # zs1 @ [b]"]
      by (inst_existentials "ys @ a # zs1" b "zs2 @ a # zs1") auto
  qed
next
  case prems: (2 as a bs x)
  then have "a \<noteq> {}"
    by auto
  from prems post_defs.Steps.steps_decomp[of "closure a\<^sub>0 # as @ [a]" "bs @ [a]"] have
    "post_defs.Steps (closure a\<^sub>0 # as @ [a])"
    by auto
  with Steps_run_cycle2[OF prems(1) \<open>a \<noteq> {}\<close>] prems show ?case
    unfolding HLD_iff by clarify (drule alw_ev_mono[where \<psi> = "holds \<phi>"], auto)
qed

end (* Context for Fixed Formula *)

end (* Double Simulation Finite Complete Abstraction *)

context Double_Simulation_Finite_Complete
begin

lemmas P2_invariant_Steps = P2_invariant.invariant_steps

theorem infinite_run_cycle_iff':
  assumes "P2 a\<^sub>0" "\<And> x xs. run (x ## xs) \<Longrightarrow> x \<in> \<Union>(closure a\<^sub>0) \<Longrightarrow> \<exists> y ys. y \<in> a\<^sub>0 \<and> run (y ## ys)"
  shows "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs)) \<longleftrightarrow> (\<exists> as a bs. Steps (a\<^sub>0 # as @ a # bs @ [a]))"
proof (safe, goal_cases)
  case (1 x\<^sub>0 xs)
  from run_finite_state_set_cycle_steps[OF this(2,1)] \<open>P2 a\<^sub>0\<close> show ?case by auto
next
  case prems: (2 as a bs)
  with Steps.steps_decomp[of "a\<^sub>0 # as @ [a]" "bs @ [a]"] have "Steps (a\<^sub>0 # as @ [a])" by auto
  from P2_invariant_Steps[OF this] have "P2 a" by auto
  from Steps_run_cycle''[OF prems this] assms(2) show ?case by auto
qed

corollary infinite_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs)) \<longleftrightarrow> (\<exists> as a bs. Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "\<Union>(closure a\<^sub>0) = a\<^sub>0" "P2 a\<^sub>0"
  by (rule infinite_run_cycle_iff', auto simp: that)

context
  fixes \<phi> :: "'a \<Rightarrow> bool" \<comment> \<open>The property we want to check\<close>
  assumes \<phi>_closure_compatible: "x \<in> a \<Longrightarrow> \<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union>(closure a). \<phi> x)"
begin

theorem infinite_buechi_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as a bs. Steps (a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall> x \<in> \<Union>(closure a). \<phi> x))"
  if "\<Union>(closure a\<^sub>0) = a\<^sub>0"
proof (safe, goal_cases)
  case (1 x\<^sub>0 xs)
  from buechi_run_finite_state_set_cycle_steps[OF this(2,1) P2_a\<^sub>0, of \<phi>] this(3) guess a ys zs
    by clarsimp
  note guessed = this(2-)
  from guessed(4) show ?case
  proof (standard, goal_cases)
    case 1
    then obtain x where "x \<in> a" "\<phi> x" by auto
    with \<phi>_closure_compatible have "\<forall> x \<in> \<Union>(closure a). \<phi> x" by blast
    with guessed(1,2) show ?case by auto
  next
    case 2
    then obtain b x where "x \<in> b" "b \<in> set zs" "\<phi> x" by auto
    with \<phi>_closure_compatible have *: "\<forall> x \<in> \<Union>(closure b). \<phi> x" by blast
    from \<open>b \<in> set zs\<close> obtain zs1 zs2 where "zs = zs1 @ b # zs2" by (force simp: split_list)
    with guessed(1) have "Steps ((a\<^sub>0 # ys) @ (a # zs1 @ [b]) @ zs2 @ [a])" by simp
    then have "Steps (a # zs1 @ [b])" by (blast dest!: Steps.steps_decomp)
    with \<open>zs = _\<close> guessed * show ?case
      apply (inst_existentials "ys @ a # zs1" b "zs2 @ a # zs1")
      using Steps.steps_append[of "a\<^sub>0 # ys @ a # zs1 @ b # zs2 @ [a]" "a # zs1 @ [b]"]
      by auto
  qed
next
  case prems: (2 as a bs)
  with Steps.steps_decomp[of "a\<^sub>0 # as @ [a]" "bs @ [a]"] have "Steps (a\<^sub>0 # as @ [a])" by auto
  from P2_invariant_Steps[OF this] have "P2 a" by auto
  from Steps_run_cycle''[OF prems(1) this] prems this that show ?case
    apply safe
    subgoal for x xs b
      by (inst_existentials x xs) (auto elim!: alw_ev_mono)
    done
qed

end (* Context for Fixed Formula *)

end (* Double Simulation Finite Complete Abstraction *)


section \<open>Encoding of Properties in Runs\<close>

text \<open>
  This approach only works if we assume strong compatibility of the property.
  For weak compatibility, encoding in the automaton is likely the right way.
\<close>

context Double_Simulation_Complete_Abstraction_Prop
begin

definition "C_\<phi> x y \<equiv> C x y \<and> \<phi> y"
definition "A1_\<phi> a b \<equiv> A1 a b \<and> b \<subseteq> {x. \<phi> x}"
definition "A2_\<phi> S S' \<equiv> \<exists> S''. A2 S S'' \<and> S'' \<inter> {x. \<phi> x} = S' \<and> S' \<noteq> {}"

lemma A2_\<phi>_P2_invariant:
  "P2 a" if "A2_\<phi>\<^sup>*\<^sup>* a\<^sub>0 a"
proof -
  interpret invariant: Graph_Invariant_Start A2_\<phi> a\<^sub>0 P2
    by standard (auto intro: \<phi>_P2_compatible P2_invariant P2_a\<^sub>0 simp: A2_\<phi>_def)
  from invariant.invariant_reaches[OF that] show ?thesis .
qed

sublocale phi: Double_Simulation_Complete C_\<phi> A1_\<phi> P1 A2_\<phi> P2 a\<^sub>0
proof (standard, goal_cases)
  case (1 S T)
  then show ?case unfolding A1_\<phi>_def C_\<phi>_def by (auto 4 4 dest: \<phi>_A1_compatible prestable)
next
  case (2 y b a)
  then obtain c where "A2 a c" "c \<inter> {x. \<phi> x} = b" unfolding A2_\<phi>_def by auto
  with \<open>y \<in> _\<close> have "y \<in> closure c" by (auto dest: closure_intD)
  moreover have "y \<subseteq> {x. \<phi> x}"
    by (smt "2"(1) \<phi>_A1_compatible \<open>A2 a c\<close> \<open>c \<inter> {x. \<phi> x} = b\<close> \<open>y \<in> closure c\<close> closure_def
        closure_poststable inf_assoc inf_bot_right inf_commute mem_Collect_eq)
  ultimately show ?case using \<open>A2 a c\<close> unfolding A1_\<phi>_def A2_\<phi>_def
    by (auto dest: closure_poststable)
next
  case (3 x y)
  then show ?case by (rule P1_distinct)
next
  case 4
  then show ?case by (rule P1_finite)
next
  case (5 a)
  then show ?case by (rule P2_cover)
next
  case (6 x y S)
  then show ?case unfolding C_\<phi>_def A2_\<phi>_def by (auto dest!: complete)
next
  case (7 a a')
  then show ?case unfolding A2_\<phi>_def by (auto intro: P2_invariant \<phi>_P2_compatible)
next
  case 8
  then show ?case by (rule P2_a\<^sub>0)
qed

lemma phi_run_iff:
  "phi.run (x ## xs) \<and> \<phi> x \<longleftrightarrow> run (x ## xs) \<and> pred_stream \<phi> (x ## xs)"
proof -
  have "phi.run xs" if "run xs" "pred_stream \<phi> xs" for xs
    using that by (coinduction arbitrary: xs) (auto elim: run.cases simp: C_\<phi>_def)
  moreover have "run xs" if "phi.run xs" for xs
    using that by (coinduction arbitrary: xs) (auto elim: phi.run.cases simp: C_\<phi>_def)
  moreover have "pred_stream \<phi> xs" if "phi.run (x ## xs)" "\<phi> x"
    using that by (coinduction arbitrary: xs x) (auto 4 3 elim: phi.run.cases simp: C_\<phi>_def)
  ultimately show ?thesis by auto
qed

end (* Double Simulation Complete Abstraction Prop *)

context Double_Simulation_Finite_Complete_Abstraction_Prop
begin

sublocale phi: Double_Simulation_Finite_Complete C_\<phi> A1_\<phi> P1 A2_\<phi> P2 a\<^sub>0
proof (standard, goal_cases)
  case 1
  have "{a. A2_\<phi>\<^sup>*\<^sup>* a\<^sub>0 a} \<subseteq> {a. Steps.reaches a\<^sub>0 a}"
    apply safe
    subgoal premises prems for x
        using prems
        proof (induction x1 \<equiv> a\<^sub>0 x rule: rtranclp.induct)
          case rtrancl_refl
          then show ?case by blast
        next
          case prems: (rtrancl_into_rtrancl b c)
          then have "c \<noteq> {}"
            by - (rule P2_non_empty, auto intro: A2_\<phi>_P2_invariant)
          from \<open>A2_\<phi> b c\<close> obtain S'' x where
            "A2 b S''" "c = S'' \<inter> {x. \<phi> x}" "x \<in> S''" "\<phi> x"
            unfolding A2_\<phi>_def by auto
          with prems \<open>c \<noteq> {}\<close> \<phi>_A2_compatible[of S''] show ?case
            including graph_automation_aggressive by auto
        qed
    done
  then show ?case (is "finite ?S") using finite_abstract_reachable by (rule finite_subset)
qed

corollary infinite_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs) \<and> pred_stream \<phi> (x\<^sub>0 ## xs)) \<longleftrightarrow>
   (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "\<Union>(closure a\<^sub>0) = a\<^sub>0" "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding phi.infinite_run_cycle_iff[OF that(1) P2_a\<^sub>0, symmetric] phi_run_iff[symmetric]
  using that(2) by auto

theorem Alw_ev_mc:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev (Not o \<phi>) x\<^sub>0) \<longleftrightarrow> \<not> (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "\<Union>(closure a\<^sub>0) = a\<^sub>0" "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding Alw_ev alw_holds_pred_stream_iff infinite_run_cycle_iff[OF that, symmetric]
  by (auto simp: comp_def)

end (* Double Simulation Finite Complete Abstraction Prop *)

context Simulation_Graph_Defs
begin

definition "represent_run x as = x ## sscan (\<lambda> b x. SOME y. C x y \<and> y \<in> b) as x"

lemma represent_run_ctr:
  "represent_run x as = x ## represent_run (SOME y. C x y \<and> y \<in> shd as) (stl as)"
  unfolding represent_run_def by (subst sscan.ctr) (rule HOL.refl)

end (* Simulation Graph Defs *)

context Simulation_Graph_Prestable
begin

lemma represent_run_Run:
  "run (represent_run x as)" if "Run (a ## as)" "x \<in> a"
using that
proof (coinduction arbitrary: a x as)
  case (run a x as)
  obtain b bs where "as = b ## bs" by (metis stream.collapse)
  with run have "A a b" "Run (b ## bs)" by (auto elim: Steps.run.cases)
  from prestable[OF \<open>A a b\<close>] \<open>x \<in> a\<close> obtain y where "C x y \<and> y \<in> b" by auto
  then have "C x (SOME y. C x y \<and> y \<in> b) \<and> (SOME y. C x y \<and> y \<in> b) \<in> b" by (rule someI)
  then show ?case using \<open>Run (b ## bs)\<close> unfolding \<open>as = _\<close>
    apply (subst represent_run_ctr, simp)
    apply (subst represent_run_ctr, simp)
    by (auto simp: represent_run_ctr[symmetric])
qed

lemma represent_run_represent:
  "stream_all2 (\<in>) (represent_run x as) (a ## as)" if "Run (a ## as)" "x \<in> a"
using that
proof (coinduction arbitrary: a x as)
  case (stream_rel x' xs a' as' a x as)
  obtain b bs where "as = b ## bs" by (metis stream.collapse)
  with stream_rel have "A a b" "Run (b ## bs)" by (auto elim: Steps.run.cases)
  from prestable[OF \<open>A a b\<close>] \<open>x \<in> a\<close> obtain y where "C x y \<and> y \<in> b" by auto
  then have "C x (SOME y. C x y \<and> y \<in> b) \<and> (SOME y. C x y \<and> y \<in> b) \<in> b" by (rule someI)
  with \<open>x' ## xs = _\<close> \<open>a' ## as' = _\<close> \<open>x \<in> a\<close> \<open>Run (b ## bs)\<close> show ?case unfolding \<open>as = _\<close>
    by (subst (asm) represent_run_ctr) auto
qed

end (* Simulation Graph Prestable *)

context Simulation_Graph_Complete_Prestable
begin

lemma step_bisim:
  "\<exists>y'. C x' y' \<and> (\<exists>a. P a \<and> y \<in> a \<and> y' \<in> a)" if "C x y" "x \<in> a" "x' \<in> a" "P a"
proof -
  from complete[OF \<open>C x y\<close> _ \<open>P a\<close> \<open>x \<in> a\<close>] obtain b' where "A a b'" "y \<in> b'"
    by auto
  from prestable[OF \<open>A a b'\<close>] \<open>x' \<in> a\<close> obtain y' where "y' \<in> b'" "C x' y'"
    by auto
  with \<open>P a\<close> \<open>A a b'\<close> \<open>y \<in> b'\<close> show ?thesis
    by auto
qed

sublocale steps_bisim:
  Bisimulation_Invariant C C "\<lambda> x y. \<exists> a. P a \<and> x \<in> a \<and> y \<in> a" "\<lambda> _. True" "\<lambda> _. True"
  by (standard; meson step_bisim)

lemma runs_bisim:
  "\<exists> ys. run (y ## ys) \<and> stream_all2 (\<lambda> x y. \<exists> a. x \<in> a \<and> y \<in> a \<and> P a) xs ys"
  if "run (x ## xs)" "x \<in> a" "y \<in> a" "P a"
  using that
  by - (drule steps_bisim.bisim.A_B.simulation_run[of _ _ y],
        auto elim!: stream_all2_weaken simp: steps_bisim.equiv'_def
       )

lemma runs_bisim':
  "\<exists> ys. run (y ## ys)" if "run (x ## xs)" "x \<in> a" "y \<in> a" "P a"
  using runs_bisim[OF that] by blast

context
  fixes Q :: "'a \<Rightarrow> bool"
  assumes compatible: "Q x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P a \<Longrightarrow> Q y"
begin

lemma Alw_ev_compatible':
  assumes "\<forall>xs. run (x ## xs) \<longrightarrow> ev (holds Q) (x ## xs)" "run (y ## xs)" "x \<in> a" "y \<in> a" "P a"
  shows "ev (holds Q) (y ## xs)"
proof -
  from assms obtain ys where "run (x ## ys)" "stream_all2 steps_bisim.equiv' xs ys"
    by (auto 4 3 simp: steps_bisim.equiv'_def dest: steps_bisim.bisim.A_B.simulation_run)
  with assms(1) have "ev (holds Q) (x ## ys)"
    by auto
  from \<open>stream_all2 _ _ _\<close> assms have "stream_all2 steps_bisim.B_A.equiv' (x ## ys) (y ## xs)"
    by (fastforce
          simp: steps_bisim.equiv'_def steps_bisim.A_B.equiv'_def
          intro: steps_bisim.stream_all2_rotate_2
       )
  then show ?thesis
    by - (rule steps_bisim.ev_\<psi>_\<phi>[OF _ _ \<open>ev _ _\<close>],
          auto dest: compatible simp: steps_bisim.A_B.equiv'_def
         )
qed

lemma Alw_ev_compatible:
  "Alw_ev Q x \<longleftrightarrow> Alw_ev Q y" if "x \<in> a" "y \<in> a" "P a"
  unfolding Alw_ev_def using that by (auto intro: Alw_ev_compatible')

end (* Context for Compatibility *)

lemma steps_bisim:
  "\<exists> ys. steps (y # ys) \<and> list_all2 (\<lambda> x y. \<exists> a. x \<in> a \<and> y \<in> a \<and> P a) xs ys"
  if "steps (x # xs)" "x \<in> a" "y \<in> a" "P a"
  using that
  by (auto 4 4
      dest: steps_bisim.bisim.A_B.simulation_steps
      intro: list_all2_mono simp: steps_bisim.equiv'_def
     )

end (* Simulation Graph Complete Prestable *)

context Subgraph_Node_Defs
begin

lemma subgraph_runD:
  "run xs" if "G'.run xs"
  by (metis G'.run.cases run.coinduct subgraph that)

lemma subgraph_V_all:
  "pred_stream V xs" if "G'.run xs"
  by (metis (no_types, lifting) G'.run.simps Subgraph_Node_Defs.E'_V1 stream.inject stream_pred_coinduct that)

lemma subgraph_runI:
  "G'.run xs" if "pred_stream V xs" "run xs"
  using that 
  by (coinduction arbitrary: xs) (metis Subgraph_Node_Defs.E'_def run.cases stream.pred_inject)

lemma subgraph_run_iff:
  "G'.run xs \<longleftrightarrow> pred_stream V xs \<and> run xs"
  using subgraph_V_all subgraph_runD subgraph_runI by blast

end

context Double_Simulation_Finite_Complete_Abstraction_Prop_Bisim
begin

sublocale sim_complete: Simulation_Graph_Complete_Prestable C_\<phi> A1_\<phi> P1
  by (standard; force dest: P1_invariant \<phi>_A1_compatible A1_complete simp: C_\<phi>_def A1_\<phi>_def)

lemma runs_closure_bisim:
  "\<exists>y ys. y \<in> a\<^sub>0 \<and> phi.run (y ## ys)" if "phi.run (x ## xs)" "x \<in> \<Union>(phi.closure a\<^sub>0)"
  using that(2) sim_complete.runs_bisim'[OF that(1)] unfolding phi.closure_def by auto

lemma infinite_run_cycle_iff':
  "(\<exists>x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> phi.run (x\<^sub>0 ## xs)) = (\<exists>as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  by (intro phi.infinite_run_cycle_iff' P2_a\<^sub>0 runs_closure_bisim)

corollary infinite_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs) \<and> pred_stream \<phi> (x\<^sub>0 ## xs)) \<longleftrightarrow>
   (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding infinite_run_cycle_iff'[symmetric] phi_run_iff[symmetric] using that by auto

theorem Alw_ev_mc:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev (Not o \<phi>) x\<^sub>0) \<longleftrightarrow> \<not> (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding Alw_ev alw_holds_pred_stream_iff infinite_run_cycle_iff[OF that, symmetric]
  by (auto simp: comp_def)

(* XXX Move? *)
lemma phi_Steps_Alw_ev:
  "\<not> (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a])) \<longleftrightarrow> phi.Steps.Alw_ev (\<lambda> _. False) a\<^sub>0"
  unfolding phi.Steps.Alw_ev
  by (auto 4 3 dest:
      sdrop_wait phi.Steps_finite.run_finite_state_set_cycle_steps phi.Steps_finite.cycle_steps_run
      simp: not_alw_iff comp_def
     )

theorem Alw_ev_mc':
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev (Not o \<phi>) x\<^sub>0) \<longleftrightarrow> phi.Steps.Alw_ev (\<lambda> _. False) a\<^sub>0"
  if "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding Alw_ev_mc[OF that] phi_Steps_Alw_ev[symmetric] ..

end (* Double Simulation Finite Complete Abstraction Prop *)

context Graph_Start_Defs
begin

interpretation Bisimulation_Invariant E E "(=)" reachable reachable
  including graph_automation by standard auto

lemma Alw_alw_iff_default:
  "Alw_alw \<phi> x \<longleftrightarrow> Alw_alw \<psi> x" if "\<And> x. reachable x \<Longrightarrow> \<phi> x \<longleftrightarrow> \<psi> x" "reachable x"
  by (rule Alw_alw_iff_strong) (auto simp: that A_B.equiv'_def)

lemma Alw_ev_iff_default:
  "Alw_ev \<phi> x \<longleftrightarrow> Alw_ev \<psi> x" if "\<And> x. reachable x \<Longrightarrow> \<phi> x \<longleftrightarrow> \<psi> x" "reachable x"
  by (rule Alw_ev_iff) (auto simp: that A_B.equiv'_def)

end (* Graph Start Defs *)

context Double_Simulation_Complete_Bisim_Cover
begin

lemma P2_closure_subs:
  "a \<subseteq> \<Union>(closure a)" if "P2 a"
  using P2_P1_cover[OF that] unfolding closure_def by fastforce

lemma (in Double_Simulation_Complete) P2_Steps_last:
  "P2 (last as)" if "Steps as" "a\<^sub>0 = hd as"
  using that by - (cases as, auto dest!: P2_invariant_Steps simp: list_all_iff P2_a\<^sub>0)

lemma (in Double_Simulation) compatible_closure:
  assumes compatible: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
      and "\<forall> x \<in> a. P x"
    shows "\<forall> x \<in> \<Union>(closure a). P x"
  unfolding closure_def using assms(2) by (auto dest: compatible)

lemma compatible_closure_all_iff:
  assumes compatible: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y" and "P2 a"
  shows "(\<forall> x \<in> a. P x) \<longleftrightarrow> (\<forall> x \<in> \<Union>(closure a). P x)"
  using \<open>P2 a\<close> by (auto dest!: P2_closure_subs dest: compatible simp: closure_def)

lemma compatible_closure_ex_iff:
  assumes compatible: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y" and "P2 a"
  shows "(\<exists> x \<in> a. P x) \<longleftrightarrow> (\<exists> x \<in> \<Union>(closure a). P x)"
  using \<open>P2 a\<close> by (auto 4 3 dest!: P2_closure_subs dest: compatible P2_cover simp: closure_def)

lemma (in Double_Simulation_Complete_Bisim) no_deadlock_closureI:
  "\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). \<not> deadlock x\<^sub>0" if "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0"
  using that by - (rule compatible_closure, simp, rule bisim.steps_bisim.deadlock_iff, auto)

context
  fixes P
  assumes P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
begin

lemma reaches_all_1:
  fixes b :: "'a set" and y :: "'a" and as :: "'a set list"
  assumes A: "\<forall>y. (\<exists>x\<^sub>0\<in>\<Union>(closure (hd as)). \<exists>xs. hd xs = x\<^sub>0 \<and> last xs = y \<and> steps xs) \<longrightarrow> P y"
     and "y \<in> last as" and "a\<^sub>0 = hd as" and "Steps as"
  shows "P y"
proof -
  from assms obtain bs where [simp]: "as = a\<^sub>0 # bs" by (cases as) auto
  from Steps_Union[OF \<open>Steps _\<close>] have "post_defs.Steps (map closure as)" .
  from \<open>Steps as\<close> \<open>a\<^sub>0 = _\<close> have "P2 (last as)"
    by (rule P2_Steps_last)
  obtain b2 where b2: "y \<in> b2" "b2 \<in> last (closure a\<^sub>0 # map closure bs)"
    apply atomize_elim
    apply simp
    apply safe
    using \<open>y \<in> _\<close> P2_closure_subs[OF \<open>P2 (last as)\<close>]
    by (auto simp: last_map)
  with post.Steps_poststable[OF \<open>post_defs.Steps _\<close>, of b2] obtain as' where as':
    "pre_defs.Steps as'" "list_all2 (\<in>) as' (closure a\<^sub>0 # map closure bs)" "last as' = b2"
    by auto
  then obtain x\<^sub>0 where "x\<^sub>0 \<in> hd as'"
    by (cases as') (auto split: if_split_asm simp: closure_def)
  from pre.Steps_prestable[OF \<open>pre_defs.Steps _\<close> \<open>x\<^sub>0 \<in> _\<close>] obtain xs where
    "steps (x\<^sub>0 # xs)" "list_all2 (\<in>) (x\<^sub>0 # xs) as'"
    by auto
  from \<open>x\<^sub>0 \<in> _\<close> \<open>list_all2 (\<in>) as' _\<close> have "x\<^sub>0 \<in> \<Union>(closure a\<^sub>0)"
    by (cases as') auto
  with A \<open>steps _\<close> have "P (last (x\<^sub>0 # xs))"
    by fastforce
  from as' have "P1 b2"
    using b2 by (auto simp: closure_def last_map split: if_split_asm)
  from \<open>list_all2 (\<in>) as' _\<close> \<open>list_all2 (\<in>) _ as'\<close> \<open>_ = b2\<close> have "last (x\<^sub>0 # xs) \<in> b2"
     by (fastforce dest!: list_all2_last)
  from P1_P[OF this \<open>y \<in> b2\<close> \<open>P1 b2\<close>] \<open>P _\<close> show "P y" ..
qed

lemma reaches_all_2:
  fixes x\<^sub>0 a xs
  assumes A: "\<forall>b y. (\<exists>xs. hd xs = a\<^sub>0 \<and> last xs = b \<and> Steps xs) \<and> y \<in> b \<longrightarrow> P y"
    and "hd xs \<in> a" and "a \<in> closure a\<^sub>0" and "steps xs"
  shows "P (last xs)"
proof -
  {
    fix y x\<^sub>0 xs
    assume "hd xs \<in> a\<^sub>0" and "steps xs"
    then obtain x ys where [simp]: "xs = x # ys" "x \<in> a\<^sub>0" by (cases xs) auto
    from steps_complete[of x ys a\<^sub>0] \<open>steps xs\<close> P2_a\<^sub>0 obtain as where
      "Steps (a\<^sub>0 # as)" "list_all2 (\<in>) ys as"
      by auto
    then have "last xs \<in> last (a\<^sub>0 # as)"
      by (fastforce dest: list_all2_last)
    with A \<open>Steps _\<close> \<open>x \<in> _\<close> have "P (last xs)"
      by (force split: if_split_asm)
  } note * = this
  from \<open>a \<in> closure a\<^sub>0\<close> obtain x where x: "x \<in> a" "x \<in> a\<^sub>0" "P1 a"
    by (auto simp: closure_def)
  with \<open>hd xs \<in> a\<close> \<open>steps xs\<close> bisim.steps_bisim[of "hd xs" "tl xs" a x] obtain xs' where
    "hd xs' = x" "steps xs'" "list_all2 (\<lambda> x y. \<exists> a. x \<in> a \<and> y \<in> a \<and> P1 a) xs xs'"
    apply atomize_elim
    apply clarsimp
    subgoal for ys
      by (inst_existentials "x # ys"; force simp: list_all2_Cons2)
    done
  with *[of xs'] x have "P (last xs')"
    by auto
  from \<open>steps xs\<close> \<open>list_all2 _ xs xs'\<close> obtain b where "last xs \<in> b" "last xs' \<in> b" "P1 b"
    by atomize_elim (fastforce dest!: list_all2_last)
  from P1_P[OF this] \<open>P (last xs')\<close> show "P (last xs)" ..
qed

lemma reaches_all:
  "(\<forall> y. (\<exists> x\<^sub>0\<in>\<Union>(closure a\<^sub>0). reaches x\<^sub>0 y) \<longrightarrow> P y) \<longleftrightarrow> (\<forall> b y. Steps.reaches a\<^sub>0 b \<and> y \<in> b \<longrightarrow> P y)"
  unfolding reaches_steps_iff Steps.reaches_steps_iff using reaches_all_1 reaches_all_2 by auto

lemma reaches_all':
  "(\<forall>x\<^sub>0\<in>\<Union>(closure a\<^sub>0). \<forall>y. reaches x\<^sub>0 y \<longrightarrow> P y) = (\<forall>y. Steps.reaches a\<^sub>0 y \<longrightarrow> (\<forall>x\<in>y. P x))"
  using reaches_all by auto

lemma reaches_all'':
  "(\<forall> y. \<forall> x\<^sub>0\<in>a\<^sub>0. reaches x\<^sub>0 y \<longrightarrow> P y) \<longleftrightarrow> (\<forall> b y. Steps.reaches a\<^sub>0 b \<and> y \<in> b \<longrightarrow> P y)"
proof -
  have "(\<forall>x\<^sub>0\<in>a\<^sub>0. \<forall>y. reaches x\<^sub>0 y \<longrightarrow> P y) \<longleftrightarrow> (\<forall>x\<^sub>0\<in>\<Union>(closure a\<^sub>0). \<forall>y. reaches x\<^sub>0 y \<longrightarrow> P y)"
    apply (rule compatible_closure_all_iff[OF _ P2_a\<^sub>0])
    apply safe
    subgoal for a x y y'
      by (blast dest: P1_P bisim.steps_bisim.A_B.simulation_reaches[of _ _ x])
    subgoal for a x y y'
      by (blast dest: P1_P bisim.steps_bisim.A_B.simulation_reaches[of _ _ y])
    done
  from this[unfolded reaches_all'] show ?thesis
    by auto
qed

lemma reaches_ex:
  "(\<exists>y. \<exists>x\<^sub>0\<in>\<Union>(closure a\<^sub>0). reaches x\<^sub>0 y \<and> P y) = (\<exists>b y. Steps.reaches a\<^sub>0 b \<and> y \<in> b \<and> P y)"
proof (safe, goal_cases)
  case (1 y x\<^sub>0 X)
  then obtain x where "x \<in> X" "x \<in> a\<^sub>0" "P1 X"
    unfolding closure_def by auto
  with \<open>x\<^sub>0 \<in> _\<close> \<open>reaches _ _\<close> obtain y' Y where "reaches x y'" "P1 Y" "y' \<in> Y" "y \<in> Y"
    by (auto dest: bisim.steps_bisim.A_B.simulation_reaches[of _ _ x])
  with simulation.simulation_reaches[OF \<open>reaches x y'\<close> \<open>x \<in> a\<^sub>0\<close> _ P2_a\<^sub>0] \<open>P _\<close> show ?case
    by (auto dest: P1_P)
next
  case (2 b y)
  with \<open>y \<in> b\<close> obtain Y where "y \<in> Y" "Y \<in> closure b" "P1 Y"
    unfolding closure_def
    by (metis (mono_tags, lifting) P2_P1_cover P2_invariant.invariant_reaches mem_Collect_eq)
  from closure_reaches[OF \<open>Steps.reaches _ _\<close>] have
    "post_defs.Steps.reaches (closure a\<^sub>0) (closure b)"
    by auto
  from post.reaches_poststable[OF this \<open>Y \<in> _\<close>] obtain X where
    "X \<in> closure a\<^sub>0 " "pre_defs.Steps.reaches X Y"
    by auto
  then obtain x where "x \<in> X" "x \<in> a\<^sub>0"
    unfolding closure_def by auto
  from pre.reaches_prestable[OF \<open>pre_defs.Steps.reaches X Y\<close> \<open>x \<in> X\<close>] obtain y' where
    "reaches x y'" "y' \<in> Y"
    by auto
  with \<open>x \<in> X\<close> \<open>X \<in> _\<close> \<open>P y\<close> \<open>P1 Y\<close> \<open>y \<in> Y\<close> show ?case
    by (auto dest: P1_P)
qed

lemma reaches_ex':
  "(\<exists> y. \<exists> x\<^sub>0\<in>a\<^sub>0. reaches x\<^sub>0 y \<and> P y) \<longleftrightarrow> (\<exists> b y. Steps.reaches a\<^sub>0 b \<and> y \<in> b \<and> P y)"
proof -
  (* XXX Move this one and others *)
  have "(\<exists>x\<^sub>0\<in>a\<^sub>0. \<exists>y. reaches x\<^sub>0 y \<and> P y) \<longleftrightarrow> (\<exists>x\<^sub>0\<in>\<Union>(closure a\<^sub>0). \<exists>y. reaches x\<^sub>0 y \<and> P y)"
    apply (rule compatible_closure_ex_iff[OF _ P2_a\<^sub>0])
    apply safe
    subgoal for a x y y'
      by (blast dest: P1_P bisim.steps_bisim.A_B.simulation_reaches[of _ _ y])
    subgoal for a x y y'
      by (blast dest: P1_P bisim.steps_bisim.A_B.simulation_reaches[of _ _ x])
    done
  from this reaches_ex show ?thesis
    by auto
qed

end (* Context for Compatibility *)

lemma (in Double_Simulation_Complete_Bisim) P1_deadlocked_compatible:
  "deadlocked x = deadlocked y" if "x \<in> a" "y \<in> a" "P1 a" for x y a
  unfolding deadlocked_def using that apply auto
  subgoal
    using A1_complete prestable by blast
  subgoal using A1_complete prestable by blast
  done

lemma steps_Steps_no_deadlock:
  "\<not> Steps.deadlock a\<^sub>0"
  if no_deadlock: "\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). \<not> deadlock x\<^sub>0"
proof -
  from P1_deadlocked_compatible have
    "(\<forall>y. (\<exists>x\<^sub>0\<in>\<Union>(closure a\<^sub>0). reaches x\<^sub>0 y) \<longrightarrow> (Not \<circ> deadlocked) y) =
     (\<forall>b y. Steps.reaches a\<^sub>0 b \<and> y \<in> b \<longrightarrow> (Not \<circ> deadlocked) y)"
    using reaches_all[of "Not o deadlocked"] unfolding comp_def by blast
  then show "\<not> Steps.deadlock a\<^sub>0"
    using no_deadlock
    unfolding Steps.deadlock_def deadlock_def
    apply safe
    subgoal
      by (simp add: Graph_Defs.deadlocked_def)
         (metis  P2_cover P2_invariant.invariant_reaches disjoint_iff_not_equal simulation.A_B_step)
    subgoal 
      by auto
    done
qed

lemma steps_Steps_no_deadlock1:
  "\<not> Steps.deadlock a\<^sub>0"
  if no_deadlock: "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0" and closure_simp: "\<Union>(closure a\<^sub>0) = a\<^sub>0"
  using steps_Steps_no_deadlock[unfolded closure_simp, OF no_deadlock] .

lemma Alw_alw_iff:
  "(\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). Alw_alw P x\<^sub>0) \<longleftrightarrow> Steps.Alw_alw (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0"
  if P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and no_deadlock: "\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). \<not> deadlock x\<^sub>0"
proof -
  from steps_Steps_no_deadlock[OF no_deadlock] show ?thesis
  by (simp add: Alw_alw_iff Steps.Alw_alw_iff no_deadlock  Steps.Ex_ev Ex_ev)
     (rule reaches_all'[simplified]; erule P1_P; assumption)
qed

lemma Alw_alw_iff1:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_alw P x\<^sub>0) \<longleftrightarrow> Steps.Alw_alw (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0"
  if P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and no_deadlock: "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0" and closure_simp: "\<Union>(closure a\<^sub>0) = a\<^sub>0"
  using Alw_alw_iff[OF P1_P] no_deadlock unfolding closure_simp by auto

lemma Alw_alw_iff2:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_alw P x\<^sub>0) \<longleftrightarrow> Steps.Alw_alw (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0"
  if P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and no_deadlock: "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0"
proof -
  have "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_alw P x\<^sub>0) \<longleftrightarrow> (\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). Alw_alw P x\<^sub>0)"
    apply -
    apply (rule compatible_closure_all_iff, rule bisim.steps_bisim.Alw_alw_iff_strong)
    unfolding bisim.steps_bisim.A_B.equiv'_def
    by (blast intro: P2_a\<^sub>0 dest: P1_P)+
  also have "\<dots> \<longleftrightarrow> Steps.Alw_alw (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0"
    by (rule Alw_alw_iff[OF P1_P no_deadlock_closureI[OF no_deadlock]])
  finally show ?thesis .
qed

lemma Steps_all_Alw_ev:
  "\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev P x\<^sub>0" if "Steps.Alw_ev (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0"
  using that unfolding Alw_ev_def Steps.Alw_ev_def
  apply safe
  apply (drule run_complete[OF _ _ P2_a\<^sub>0], assumption)
  apply safe
  apply (elim allE impE, assumption)
  subgoal premises prems for x xs as
    using prems(4,3,1)
    by (induction "a\<^sub>0 ## as" arbitrary: a\<^sub>0 as x xs rule: ev.induct)
       (auto 4 3 elim: stream.rel_cases intro: ev_Stream)
  done

lemma closure_compatible_Steps_all_ex_iff:
  "Steps.Alw_ev (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0 \<longleftrightarrow> Steps.Alw_ev (\<lambda> a. \<exists> c \<in> a. P c) a\<^sub>0"
  if closure_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
proof -
  interpret Bisimulation_Invariant A2 A2 "(=)" P2 P2
    by standard auto
  show ?thesis
    using P2_a\<^sub>0
    by - (rule Alw_ev_iff, unfold A_B.equiv'_def; meson P2_cover closure_P disjoint_iff_not_equal)
qed

lemma (in -) compatible_imp:
  assumes "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
      and "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> Q x \<longleftrightarrow> Q y"
    shows "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> (Q x \<longrightarrow> P x) \<longleftrightarrow> (Q y \<longrightarrow> P y)"
  using assms by metis

lemma Leadsto_iff:
  "(\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). leadsto P Q x\<^sub>0) \<longleftrightarrow> Steps.Alw_alw (\<lambda>a. \<forall>c\<in>a. P c \<longrightarrow> Alw_ev Q c) a\<^sub>0"
  if  P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and P1_Q: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> Q x \<longleftrightarrow> Q y"
  and no_deadlock: "\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). \<not> deadlock x\<^sub>0"
  unfolding leadsto_def
  by (subst Alw_alw_iff[OF _ no_deadlock],
      intro compatible_imp bisim.Alw_ev_compatible,
      (subst (asm) P1_Q; force), (assumption | intro HOL.refl P1_P)+
     )

lemma Leadsto_iff1:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. leadsto P Q x\<^sub>0) \<longleftrightarrow> Steps.Alw_alw (\<lambda>a. \<forall>c\<in>a. P c \<longrightarrow> Alw_ev Q c) a\<^sub>0"
  if  P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and P1_Q: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> Q x \<longleftrightarrow> Q y"
  and no_deadlock: "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0" and closure_simp: "\<Union>(closure a\<^sub>0) = a\<^sub>0"
  by (subst closure_simp[symmetric], rule Leadsto_iff)
     (auto simp: closure_simp no_deadlock dest: P1_Q P1_P)

lemma Leadsto_iff2:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. leadsto P Q x\<^sub>0) \<longleftrightarrow> Steps.Alw_alw (\<lambda>a. \<forall>c\<in>a. P c \<longrightarrow> Alw_ev Q c) a\<^sub>0"
  if  P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and P1_Q: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> Q x \<longleftrightarrow> Q y"
  and no_deadlock: "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0"
proof -
  have "(\<forall> x\<^sub>0 \<in> a\<^sub>0. leadsto P Q x\<^sub>0) \<longleftrightarrow> (\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). leadsto P Q x\<^sub>0)"
    apply -
    apply (rule compatible_closure_all_iff, rule bisim.steps_bisim.Leadsto_iff)
    unfolding bisim.steps_bisim.A_B.equiv'_def by (blast intro: P2_a\<^sub>0 dest: P1_P P1_Q)+
  also have "\<dots> \<longleftrightarrow> Steps.Alw_alw (\<lambda>a. \<forall>c\<in>a. P c \<longrightarrow> Alw_ev Q c) a\<^sub>0"
    by (rule Leadsto_iff[OF _ _ no_deadlock_closureI[OF no_deadlock]]; rule P1_P P1_Q)
  finally show ?thesis .
qed

lemma (in -) compatible_convert1:
  assumes "\<And> x y a. P x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P y"
  shows "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
    by (auto intro: assms)

lemma (in -) compatible_convert2:
  assumes "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  shows "\<And> x y a. P x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P y"
  using assms by meson

lemma (in Double_Simulation_Defs)
  assumes compatible: "\<And> x y a. P x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P y"
    and that: "\<forall> x \<in> a. P x"
  shows "\<forall> x \<in> \<Union>(closure a). P x"
  using that unfolding closure_def by (auto dest: compatible)

end (* Double Simulation Finite Complete Bisim *)

context Double_Simulation_Finite_Complete_Bisim_Cover
begin

lemma Alw_ev_Steps_ex:
  "(\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). Alw_ev P x\<^sub>0) \<longrightarrow> Steps.Alw_ev (\<lambda> a. \<exists> c \<in> a. P c) a\<^sub>0"
  if closure_P: "\<And> a x y. x \<in> \<Union>(closure a) \<Longrightarrow> y \<in> \<Union>(closure a) \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  unfolding Alw_ev Steps.Alw_ev
  apply safe
  apply (frule Steps_finite.run_finite_state_set_cycle_steps)
  apply clarify
  apply (frule Steps_run_cycle'')
   apply (auto dest!: P2_invariant.invariant_run simp: stream.pred_set; fail)
  unfolding that
   apply clarify
  subgoal premises prems for xs x ys zs x' xs' R
  proof -
    from \<open>x' \<in> R\<close> \<open>R \<in> _\<close> that have \<open>x' \<in> \<Union>(closure a\<^sub>0)\<close>
      by auto
    with prems(5,9) have
      "\<forall> c \<in> {x'} \<union> sset xs'. \<exists> y \<in> {a\<^sub>0} \<union> sset xs. c \<in> \<Union>(closure y)"
      by fast
    with prems(3) have *:
      "\<forall> c \<in> {x'} \<union> sset xs'. \<exists> y \<in> {a\<^sub>0} \<union> sset xs. c \<in> \<Union>(closure y) \<and> (\<forall> c \<in> y. \<not> P c)"
      unfolding alw_holds_sset by simp
    from \<open>Run _\<close> have **: "P2 y" if "y \<in> {a\<^sub>0} \<union> sset xs" for y
      using that by (auto dest!: P2_invariant.invariant_run simp: stream.pred_set)
    have ***: "\<not> P c" if "c \<in> \<Union>(closure y)" "\<forall> d \<in> y. \<not> P d" "P2 y" for c y
    proof -
      from that P2_cover[OF \<open>P2 y\<close>] obtain d where "d \<in> y" "d \<in> \<Union>(closure y)"
        by (fastforce dest!: P2_closure_subs)
      with that closure_P show ?thesis
        by blast
    qed
    from * have "\<forall> c \<in> {x'} \<union> sset xs'. \<not> P c"
      by (fastforce intro: ** dest!: ***[rotated])
    with prems(1) \<open>run _\<close> \<open>x' \<in> \<Union>(closure _)\<close> show ?thesis
      unfolding alw_holds_sset by auto
  qed
  done

lemma Alw_ev_Steps_ex2:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev P x\<^sub>0) \<longrightarrow> Steps.Alw_ev (\<lambda> a. \<exists> c \<in> a. P c) a\<^sub>0"
  if  closure_P: "\<And> a x y. x \<in> \<Union>(closure a) \<Longrightarrow> y \<in> \<Union>(closure a) \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
proof -
  have "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev P x\<^sub>0) \<longleftrightarrow> (\<forall> x\<^sub>0 \<in> \<Union>(closure a\<^sub>0). Alw_ev P x\<^sub>0)"
    by (intro compatible_closure_all_iff bisim.Alw_ev_compatible; auto dest: P1_P simp: P2_a\<^sub>0)
  also have "\<dots> \<longrightarrow> Steps.Alw_ev (\<lambda> a. \<exists> c \<in> a. P c) a\<^sub>0"
    by (intro Alw_ev_Steps_ex that)
  finally show ?thesis .
qed

lemma Alw_ev_Steps_ex1:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev P x\<^sub>0) \<longrightarrow> Steps.Alw_ev (\<lambda> a. \<exists> c \<in> a. P c) a\<^sub>0" if "\<Union>(closure a\<^sub>0) = a\<^sub>0"
  and closure_P: "\<And> a x y. x \<in> \<Union>(closure a) \<Longrightarrow> y \<in> \<Union>(closure a) \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  by (subst that(1)[symmetric]) (intro Alw_ev_Steps_ex closure_P; assumption)

lemma closure_compatible_Alw_ev_Steps_iff:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev P x\<^sub>0) \<longleftrightarrow> Steps.Alw_ev (\<lambda> a. \<forall> c \<in> a. P c) a\<^sub>0"
  if closure_P: "\<And> a x y. x \<in> \<Union>(closure a) \<Longrightarrow> y \<in> \<Union>(closure a) \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
    and P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  apply standard
  subgoal
    apply (subst closure_compatible_Steps_all_ex_iff[OF closure_P])
       prefer 4
       apply (rule Alw_ev_Steps_ex2[OF that, rule_format])
    by (auto dest!: P2_closure_subs)
  by (rule Steps_all_Alw_ev) (auto dest: P2_closure_subs)

lemma Leadsto_iff':
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. leadsto P Q x\<^sub>0)
   \<longleftrightarrow> Steps.Alw_alw (\<lambda> a. (\<forall> c \<in> a. P c) \<longrightarrow> Steps.Alw_ev (\<lambda> a. \<forall> c \<in> a. Q c) a) a\<^sub>0"
  if  P1_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P x \<longleftrightarrow> P y"
    and P1_Q: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> Q x \<longleftrightarrow> Q y"
    and closure_Q: "\<And> a x y. x \<in> \<Union>(closure a) \<Longrightarrow> y \<in> \<Union>(closure a) \<Longrightarrow> P2 a \<Longrightarrow> Q x \<longleftrightarrow> Q y"
    and closure_P: "\<And> a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
    and no_deadlock: "\<forall> x\<^sub>0 \<in> a\<^sub>0. \<not> deadlock x\<^sub>0" and closure_simp: "\<Union>(closure a\<^sub>0) = a\<^sub>0"
  apply (subst Leadsto_iff1, (rule that; assumption)+)
  subgoal
    apply (rule P2_invariant.Alw_alw_iff_default)
    subgoal premises prems for a
    proof -
      have "P2 a"
        by (rule P2_invariant.invariant_reaches[OF prems[unfolded Graph_Start_Defs.reachable_def]])
      interpret a: Double_Simulation_Finite_Complete_Bisim_Cover C A1 P1 A2 P2 a
        apply standard
              apply (rule complete; assumption; fail)
             apply (rule P2_invariant; assumption)
        subgoal
          by (fact \<open>P2 a\<close>)
        subgoal
        proof -
          have "{b. Steps.reaches a b} \<subseteq> {b. Steps.reaches a\<^sub>0 b}"
            by (blast intro: rtranclp_trans prems[unfolded Graph_Start_Defs.reachable_def])
          with finite_abstract_reachable show ?thesis
            by - (rule finite_subset)
        qed

          apply (rule A1_complete; assumption)
         apply (rule P1_invariant; assumption)
        apply (rule P2_P1_cover; assumption)
        done
      from \<open>P2 a\<close> show ?thesis
        by - (subst a.closure_compatible_Alw_ev_Steps_iff[symmetric], (rule that; assumption)+,
            auto dest: closure_P intro: that
            )
    qed
    ..
  done

context
  fixes P :: "'a \<Rightarrow> bool" \<comment> \<open>The property we want to check\<close>
  assumes closure_P: "\<And> a x y. x \<in> \<Union>(closure a) \<Longrightarrow> y \<in> \<Union>(closure a) \<Longrightarrow> P2 a \<Longrightarrow> P x \<longleftrightarrow> P y"
  and P1_P: "\<And> a x y. P x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> P y"
begin

lemma run_alw_ev_bisim:
  "run (x ## xs) \<Longrightarrow> x \<in> \<Union>(closure a\<^sub>0) \<Longrightarrow> alw (ev (holds P)) xs
      \<Longrightarrow> \<exists> y ys. y \<in> a\<^sub>0 \<and> run (y ## ys) \<and> alw (ev (holds P)) ys"
  unfolding closure_def
  apply safe
  apply (rotate_tac 3)
  apply (drule bisim.runs_bisim, assumption+)
  apply (auto elim: P1_P dest: alw_ev_lockstep[of P _ _ _ P])
  done

lemma \<phi>_closure_compatible:
  "P2 a \<Longrightarrow> x \<in> \<Union>(closure a) \<Longrightarrow> P x \<longleftrightarrow> (\<forall> x \<in> \<Union>(closure a). P x)"
  using closure_P by blast

theorem infinite_buechi_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> \<Union>(closure a\<^sub>0) \<and> run (x\<^sub>0 ## xs) \<and> alw (ev (holds P)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as a bs. a \<noteq> {} \<and> post_defs.Steps (closure a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall> x \<in> \<Union> a. P x))"
  by (rule
      infinite_buechi_run_cycle_iff_closure[OF
        \<phi>_closure_compatible run_alw_ev_bisim P2_closure_subs
        ]
      )
end (* Property *)

end (* Double Simulation Finite Complete Bisim Cover *)

text \<open>Possible Solution\<close>
context Graph_Invariant
begin

definition "E_inv x y \<equiv> E x y \<and> P x \<and> P y"

lemma bisim_E_inv:
  "Bisimulation_Invariant E E_inv (=) P P"
  by standard (auto intro: invariant simp: E_inv_def)

interpretation G_inv: Graph_Defs E_inv .

lemma steps_G_inv_steps:
  "steps (x # xs) \<longleftrightarrow> G_inv.steps (x # xs)" if "P x"
proof -
  interpret Bisimulation_Invariant E E_inv "(=)" P P
    by (rule bisim_E_inv)
  from \<open>P x\<close> show ?thesis
    by (auto 4 3 simp: equiv'_def list.rel_eq
        dest: bisim.A_B.simulation_steps bisim.B_A.simulation_steps
          list_all2_mono[of _ _ _ "(=)"]
       )
qed

end (* Graph Invariant *)

paragraph \<open>\<open>R_of\<close>/\<open>from_R\<close>\<close>

definition "R_of lR = snd ` lR"

definition "from_R l R = {(l, u) | u. u \<in> R}"

lemma from_R_fst:
  "\<forall>x\<in>from_R l R. fst x = l"
  unfolding from_R_def by auto

lemma R_of_from_R [simp]:
  "R_of (from_R l R) = R"
  unfolding R_of_def from_R_def image_def by auto

lemma from_R_loc:
  "l' = l" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

lemma from_R_val:
  "u \<in> Z" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

lemma from_R_R_of:
  "from_R l (R_of S) = S" if "\<forall> x \<in> S. fst x = l"
  using that unfolding from_R_def R_of_def by force

lemma R_ofI[intro]:
  "Z \<in> R_of S" if "(l, Z) \<in> S"
  using that unfolding R_of_def by force

lemma from_R_I[intro]:
  "(l', u') \<in> from_R l' Z'" if "u' \<in> Z'"
  using that unfolding from_R_def by auto

lemma R_of_non_emptyD:
  "a \<noteq> {}" if "R_of a \<noteq> {}"
  using that unfolding R_of_def by simp

lemma R_of_empty[simp]:
  "R_of {} = {}"
  using R_of_non_emptyD by metis

lemma fst_simp:
  "x = l" if "\<forall>x\<in>a. fst x = l" "(x, y) \<in> a"
  using that by auto

lemma from_R_D:
  "u \<in> Z" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

locale Double_Simulation_paired_Defs =
  fixes C :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" \<comment> \<open>Concrete step relation\<close>
    and A1 :: "('a \<times> 'b set) \<Rightarrow> ('a \<times> 'b set) \<Rightarrow> bool"
    \<comment> \<open>Step relation for the first abstraction layer\<close>
    and P1 :: "('a \<times> 'b set) \<Rightarrow> bool" \<comment> \<open>Valid states of the first abstraction layer\<close>
    and A2 :: "('a \<times> 'b set) \<Rightarrow> ('a \<times> 'b set) \<Rightarrow> bool"
    \<comment> \<open>Step relation for the second abstraction layer\<close>
    and P2 :: "('a \<times> 'b set) \<Rightarrow> bool" \<comment> \<open>Valid states of the second abstraction layer\<close>
begin

definition
  "A1' = (\<lambda> lR lR'. \<exists> l l'. (\<forall> x \<in> lR. fst x = l) \<and> (\<forall> x \<in> lR'. fst x = l')
    \<and> P1 (l, R_of lR) \<and> A1 (l, R_of lR) (l', R_of lR')
    )"

definition
  "A2' = (\<lambda> lR lR'. \<exists> l l'. (\<forall> x \<in> lR. fst x = l) \<and> (\<forall> x \<in> lR'. fst x = l')
    \<and> P2 (l, R_of lR) \<and> A2 (l, R_of lR) (l', R_of lR')
    )"

definition
  "P1' = (\<lambda> lR. \<exists> l. (\<forall> x \<in> lR. fst x = l) \<and> P1 (l, R_of lR))"

definition
  "P2' = (\<lambda> lR. \<exists> l. (\<forall> x \<in> lR. fst x = l) \<and> P2 (l, R_of lR))"

definition "closure' l a = {x. P1 (l, x) \<and> a \<inter> x \<noteq> {}}"

sublocale sim: Double_Simulation_Defs C A1' P1' A2' P2' .

end

locale Double_Simulation_paired = Double_Simulation_paired_Defs +
  assumes prestable: "P1 (l, S) \<Longrightarrow> A1 (l, S) (l', T) \<Longrightarrow> \<forall> s \<in> S. \<exists> s' \<in> T. C (l, s) (l', s')"
      and closure_poststable:
        "s' \<in> closure' l' y \<Longrightarrow> P2 (l, x) \<Longrightarrow> A2 (l, x) (l', y)
        \<Longrightarrow> \<exists>s\<in>closure' l x. A1 (l, s) (l', s')"
      and P1_distinct: "P1 (l, x) \<Longrightarrow> P1 (l, y) \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<inter> y = {}"
      and P1_finite: "finite {(l, x). P1 (l, x)}"
      and P2_cover: "P2 (l, a) \<Longrightarrow> \<exists> x. P1 (l, x) \<and> x \<inter> a \<noteq> {}"
begin

sublocale sim: Double_Simulation C A1' P1' A2' P2'
proof (standard, goal_cases)
  case (1 S T)
  then show ?case
    unfolding A1'_def by (metis from_R_I from_R_R_of from_R_val prestable prod.collapse)
next
  case (2 s' y x)
  then show ?case
    unfolding A2'_def A1'_def sim.closure_def
    unfolding P1'_def
    apply clarify
    subgoal premises prems for l l1 l2
    proof -
      from prems have "l2 = l1"
        by force
      from prems have "R_of s' \<in> closure' l1 (R_of y)"
        unfolding closure'_def by auto
      with \<open>A2 _ _\<close> \<open>P2 _\<close> closure_poststable[of "R_of s'" l1 "R_of y" l "R_of x"] obtain s where
        "s \<in> closure' l (R_of x)" "A1 (l, s) (l1, R_of s')"
        by auto
      with prems from_R_fst R_of_from_R show ?thesis
        apply -
        unfolding \<open>l2 = l1\<close>
        apply (rule bexI[where x = "from_R l s"])
         apply (inst_existentials l l1)
            apply (simp add: from_R_fst; fail)+
        subgoal
          unfolding closure'_def by auto
         apply (simp; fail)
        unfolding closure'_def
        apply (intro CollectI conjI exI)
          apply fastforce
         apply fastforce
        apply (fastforce simp: R_of_def from_R_def)
        done
    qed
    done
next
  case (3 x y)
  then show ?case
    unfolding P1'_def using P1_distinct
    by (smt disjoint_iff_not_equal eq_fst_iff from_R_R_of from_R_val)
next
  case 4
  have "{x. \<exists>l. (\<forall>x\<in>x. fst x = l) \<and> P1 (l, R_of x)} \<subseteq> (\<lambda> (l, x). from_R l x) ` {(l, x). P1 (l, x)}"
    using from_R_R_of image_iff by fastforce
  with P1_finite show ?case
    unfolding P1'_def by (auto elim: finite_subset)
next
  case (5 a)
  then show ?case
    unfolding P1'_def P2'_def
    apply clarify
    apply (frule P2_cover)
    apply clarify
    subgoal for l x
      apply (inst_existentials "from_R l x" l, (simp add: from_R_fst)+)
      using R_of_def by (fastforce simp: from_R_fst)
    done
qed

context
  assumes P2_invariant: "P2 a \<Longrightarrow> A2 a a' \<Longrightarrow> P2 a'"
begin

(* This lemma could be more general by adding non-emptiness as an invariant
  (see use of double_sim.P2_cover below )
*)
lemma A2_A2'_bisim: "Bisimulation_Invariant A2 A2' (\<lambda> (l, Z) b. b = from_R l Z) P2 P2'"
  apply standard
  subgoal A2_A2' for a b a'
    unfolding P2'_def
    apply clarify
    apply (inst_existentials "from_R (fst b) (snd b)")
    subgoal for x y l
      unfolding A2'_def
      apply simp
      apply (inst_existentials l)
      by (auto dest!: P2_cover simp: from_R_def)
    by clarsimp
  subgoal A2'_A2 for a a' b'
    using from_R_fst by (fastforce dest: sim.P2_cover simp: from_R_R_of A2'_def)
  subgoal P2_invariant for a b
    by (fact P2_invariant)
  subgoal P2'_invariant for a b
    unfolding P2'_def A2'_def using P2_invariant by blast
  done

end (* Context for invariance of P2 *)

end (* Double Simulation paired *)

locale Double_Simulation_Complete_paired = Double_Simulation_paired +
  fixes l\<^sub>0 a\<^sub>0
  assumes complete: "C (l, x) (l', y) \<Longrightarrow> x \<in> S \<Longrightarrow> P2 (l, S) \<Longrightarrow> \<exists> T. A2 (l, S) (l', T) \<and> y \<in> T"
  assumes P2_invariant: "P2 a \<Longrightarrow> A2 a a' \<Longrightarrow> P2 a'"
      and P2_a\<^sub>0': "P2 (l\<^sub>0, a\<^sub>0)"
begin

interpretation Bisimulation_Invariant A2 A2' "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  by (rule A2_A2'_bisim[OF P2_invariant])

sublocale Double_Simulation_Complete C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0"
proof (standard, goal_cases)
  case prems: (1 x y S) \<comment> \<open>complete\<close>
  then show ?case
    unfolding A2'_def P2'_def using from_R_fst
    by (clarify; cases x; cases y; simp; fastforce dest!: complete[of _ _ _ _ "R_of S"])
next
  case prems: (2 a a') \<comment> \<open>P2 invariant\<close>
  then show ?case
    by (meson A2'_def P2'_def P2_invariant)
next
  case prems: 3 \<comment> \<open>P2 start\<close>
  then show ?case
    using P2'_def P2_a\<^sub>0' from_R_fst by fastforce
qed

sublocale P2_invariant': Graph_Invariant_Start A2 "(l\<^sub>0, a\<^sub>0)" P2
  by (standard; rule P2_a\<^sub>0')

end (* Double Simulation Complete paired *)

locale Double_Simulation_Finite_Complete_paired = Double_Simulation_Complete_paired +
  assumes finite_abstract_reachable: "finite {(l, a). A2\<^sup>*\<^sup>* (l\<^sub>0, a\<^sub>0) (l, a) \<and> P2 (l, a)}"
begin

interpretation Bisimulation_Invariant A2 A2' "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  by (rule A2_A2'_bisim[OF P2_invariant])

sublocale Double_Simulation_Finite_Complete C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0"
proof (standard, goal_cases)
  case prems: 1 \<comment> \<open>The set of abstract reachable states is finite.\<close>
  have *: "\<exists> l. x = from_R l (R_of x) \<and> A2\<^sup>*\<^sup>* (l\<^sub>0, a\<^sub>0) (l, R_of x)"
    if "sim.Steps.reaches (from_R l\<^sub>0 a\<^sub>0) x" for x
    using bisim.B_A_reaches[OF that, of "(l\<^sub>0, a\<^sub>0)"] P2_a\<^sub>0' P2'_def equiv'_def from_R_fst by fastforce 
  have "{a. sim.Steps.reaches (from_R l\<^sub>0 a\<^sub>0) a}
    \<subseteq> (\<lambda> (l, R). from_R l R) ` {(l, a). A2\<^sup>*\<^sup>* (l\<^sub>0, a\<^sub>0) (l, a) \<and> P2 (l, a)}"
    using P2_a\<^sub>0' by (fastforce dest: * intro: P2_invariant'.invariant_reaches)
  then show ?case
    using finite_abstract_reachable by (auto elim!: finite_subset)
qed

end (* Double Simulation Finite Complete paired *)

locale Double_Simulation_Complete_Bisim_paired = Double_Simulation_Complete_paired +
  assumes A1_complete: "C (l, x) (l', y) \<Longrightarrow> P1 (l,S) \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists> T. A1 (l, S) (l', T) \<and> y \<in> T"
      and P1_invariant: "P1 (l, S) \<Longrightarrow> A1 (l, S) (l', T) \<Longrightarrow> P1 (l', T)"
begin

sublocale Double_Simulation_Complete_Bisim C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0"
proof (standard, goal_cases)
case (1 x y S)
  then show ?case
    unfolding A1'_def P1'_def
    apply (cases x; cases y; simp)
    apply (drule A1_complete[where S = "R_of S"])
      apply fastforce
     apply fastforce
    apply clarify
    subgoal for a b l' ba l T
      by (inst_existentials "from_R l' T" l l') (auto simp: from_R_fst)
    done
next
  case (2 S T)
  then show ?case
    unfolding A1'_def P1'_def by (auto intro: P1_invariant)
qed

end (* Double Simulation Complete Bisim paired *)

locale Double_Simulation_Finite_Complete_Bisim_paired = Double_Simulation_Finite_Complete_paired +
  Double_Simulation_Complete_Bisim_paired
begin

sublocale Double_Simulation_Finite_Complete_Bisim C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0" ..

end (* Double Simulation Finite Complete Bisim paired *)

locale Double_Simulation_Complete_Bisim_Cover_paired =
  Double_Simulation_Complete_Bisim_paired +
  assumes P2_P1_cover: "P2 (l, a) \<Longrightarrow> x \<in> a \<Longrightarrow> \<exists> a'. a \<inter> a' \<noteq> {} \<and> P1 (l, a') \<and> x \<in> a'"
begin

sublocale Double_Simulation_Complete_Bisim_Cover C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0"
  apply standard
  unfolding P2'_def P1'_def
  apply clarify
  apply (drule P2_P1_cover, force)
  apply clarify
  subgoal for a aa b l a'
    by (inst_existentials "from_R l a'") (fastforce simp: from_R_fst)+
  done

end (* Double Simulation Complete Bisim Cover paired *)

locale Double_Simulation_Finite_Complete_Bisim_Cover_paired =
  Double_Simulation_Complete_Bisim_Cover_paired +
  Double_Simulation_Finite_Complete_Bisim_paired
begin

sublocale Double_Simulation_Finite_Complete_Bisim_Cover C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0" ..

end (* Double Simulation Finite Complete Bisim Cover paired *)

locale Double_Simulation_Complete_Abstraction_Prop_paired =
  Double_Simulation_Complete_paired +
  fixes P :: "'a \<Rightarrow> bool" \<comment> \<open>The property we want to check\<close>
  assumes P2_non_empty: "P2 (l, a) \<Longrightarrow> a \<noteq> {}"
begin

definition "\<phi> = P o fst"

lemma P2_\<phi>:
  "a \<inter> Collect \<phi> = a" if "P2' a" "a \<inter> Collect \<phi> \<noteq> {}"
  using that unfolding \<phi>_def P2'_def by (auto simp del: fst_conv)

sublocale Double_Simulation_Complete_Abstraction_Prop C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0" \<phi>
proof (standard, goal_cases)
  case (1 a b)
  then obtain l where "\<forall>x\<in>b. fst x = l"
    unfolding A1'_def by fast
  then show ?case
    unfolding \<phi>_def by (auto simp del: fst_conv)
next
  case (2 a)
  then show ?case
    by - (frule P2_\<phi>, auto)
next
  case prems: (3 a)
  then have "P2' a"
    by (simp add: P2_invariant.invariant_reaches)
  from P2_\<phi>[OF this] prems show ?case
    by simp
next
  case (4 a)
  then show ?case
    unfolding P2'_def by (auto dest!: P2_non_empty)
qed

end (* Double Simulation Complete Abstraction Prop paired *)

locale Double_Simulation_Finite_Complete_Abstraction_Prop_paired =
  Double_Simulation_Complete_Abstraction_Prop_paired +
  Double_Simulation_Finite_Complete_paired
begin

sublocale Double_Simulation_Finite_Complete_Abstraction_Prop C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0" \<phi> ..

end (* Double Simulation Finite Complete Abstraction Prop paired *)

locale Double_Simulation_Complete_Abstraction_Prop_Bisim_paired =
  Double_Simulation_Complete_Abstraction_Prop_paired +
  Double_Simulation_Complete_Bisim_paired
begin

interpretation bisim: Bisimulation_Invariant A2 A2' "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  by (rule A2_A2'_bisim[OF P2_invariant])

sublocale Double_Simulation_Complete_Abstraction_Prop_Bisim
  C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0" \<phi> ..

lemma P2'_non_empty:
  "P2' a \<Longrightarrow> a \<noteq> {}"
  using P2_non_empty unfolding P2'_def by force

lemma from_R_int_\<phi>[simp]:
  "from_R l R \<inter> Collect \<phi> = from_R l R" if "P l"
  using from_R_fst that unfolding \<phi>_def by fastforce

interpretation G\<^sub>\<phi>: Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). A2 (l, Z) (l', Z') \<and> P l'" "(l\<^sub>0, a\<^sub>0)" .

interpretation Bisimulation_Invariant "\<lambda> (l, Z) (l', Z'). A2 (l, Z) (l', Z') \<and> P l'"
  A2_\<phi> "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  apply standard
  unfolding A2_\<phi>_def
     apply clarify
  subgoal for l a l' a'
    apply (drule bisim.A_B_step)
    prefer 3
       apply assumption
      apply safe
    apply (frule P_invariant, assumption+)
    using from_R_fst by (fastforce simp: \<phi>_def P2'_def dest!: P2'_non_empty)+
  subgoal for a a' b'
    apply clarify
    apply (drule bisim.B_A_step)
       prefer 2
       apply assumption
      apply safe
    apply (frule P2_invariant, assumption+)
    apply (subst (asm) (3) \<phi>_def)
    apply simp
    apply (elim allE impE, assumption)
    using from_R_fst apply force
    apply (subst (asm) (2) from_R_int_\<phi>)
    using from_R_fst by fastforce+
  subgoal
    by blast
  subgoal
    using \<phi>_P2_compatible by blast
  done

lemma from_R_subs_\<phi>:
  "from_R l a \<subseteq> Collect \<phi>" if "P l"
  using that unfolding \<phi>_def from_R_def by auto

lemma P2'_from_R:
  "\<exists> l' Z'. x = from_R l' Z'" if "P2' x"
  using that unfolding P2'_def by (fastforce dest: from_R_R_of)

lemma P2_from_R_list':
  "\<exists> as'. map (\<lambda>(x, y). from_R x y) as' = as" if "list_all P2' as"
  by (rule list_all_map[OF _ that]) (auto dest!: P2'_from_R)

end (* Double Simulation Complete Abstraction Prop Bisim paired *)

locale Double_Simulation_Finite_Complete_Abstraction_Prop_Bisim_paired =
  Double_Simulation_Complete_Abstraction_Prop_Bisim_paired +
  Double_Simulation_Finite_Complete_Bisim_paired
begin

interpretation bisim: Bisimulation_Invariant A2 A2' "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  by (rule A2_A2'_bisim[OF P2_invariant])

sublocale Double_Simulation_Finite_Complete_Abstraction_Prop_Bisim
  C A1' P1' A2' P2' "from_R l\<^sub>0 a\<^sub>0" \<phi> ..

interpretation G\<^sub>\<phi>: Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). A2 (l, Z) (l', Z') \<and> P l'" "(l\<^sub>0, a\<^sub>0)" .

interpretation Bisimulation_Invariant "\<lambda> (l, Z) (l', Z'). A2 (l, Z) (l', Z') \<and> P l'"
  A2_\<phi> "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  apply standard
  unfolding A2_\<phi>_def
     apply clarify
  subgoal for l a l' a'
    apply (drule bisim.A_B_step)
    prefer 3
       apply assumption
      apply safe
    apply (frule P_invariant, assumption+)
    using from_R_fst by (fastforce simp: \<phi>_def P2'_def dest!: P2'_non_empty)+
  subgoal for a a' b'
    apply clarify
    apply (drule bisim.B_A_step)
       prefer 2
       apply assumption
      apply safe
    apply (frule P2_invariant, assumption+)
    apply (subst (asm) (3) \<phi>_def)
    apply simp
    apply (elim allE impE, assumption)
    using from_R_fst apply force
    apply (subst (asm) (2) from_R_int_\<phi>)
    using from_R_fst by fastforce+
  subgoal
    by blast
  subgoal
    using \<phi>_P2_compatible by blast
  done

theorem Alw_ev_mc:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) (l\<^sub>0, x\<^sub>0)) \<longleftrightarrow>
    \<not> P l\<^sub>0 \<or> (\<nexists>as a bs. G\<^sub>\<phi>.steps ((l\<^sub>0, a\<^sub>0) # as @ a # bs @ [a]))"
  apply (subst steps_map_equiv[of "\<lambda> (l, Z). from_R l Z" _ "from_R l\<^sub>0 a\<^sub>0"])
       apply force
      apply (clarsimp simp: from_R_def)
  subgoal
    by (fastforce dest!: P2'_non_empty)
     apply (simp; fail)
    apply (rule P2_a\<^sub>0'; fail)
   apply (rule phi.P2_a\<^sub>0; fail)
proof (cases "P l\<^sub>0", goal_cases)
  case 1
  have *: "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) (l\<^sub>0, x\<^sub>0)) \<longleftrightarrow> (\<forall>x\<^sub>0\<in>from_R l\<^sub>0 a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) x\<^sub>0)"
    unfolding from_R_def by auto
  from \<open>P _\<close> show ?case
    unfolding *
    apply (subst Alw_ev_mc[OF from_R_subs_\<phi>], assumption)
    apply (auto simp del: map_map)
    apply (frule phi.P2_invariant.invariant_steps)
    apply (auto dest!: P2'_from_R P2_from_R_list')
    done
next
  case 2
  then have "\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) (l\<^sub>0, x\<^sub>0)"
    unfolding sim.Alw_ev_def by (force simp: \<phi>_def)
  with \<open>\<not> P l\<^sub>0\<close> show ?case
    by auto
qed

theorem Alw_ev_mc1:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) (l\<^sub>0, x\<^sub>0)) \<longleftrightarrow> \<not> (P l\<^sub>0 \<and> (\<exists>a. G\<^sub>\<phi>.reachable a \<and> G\<^sub>\<phi>.reaches1 a a))"
  unfolding Alw_ev_mc using G\<^sub>\<phi>.reachable_cycle_iff by auto

end (* Double Simulation Finite Complete Abstraction Prop Bisim paired *)

context Double_Simulation_Complete_Bisim_Cover_paired
begin

interpretation bisim: Bisimulation_Invariant A2 A2' "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  by (rule A2_A2'_bisim[OF P2_invariant])

interpretation Start: Double_Simulation_Complete_Abstraction_Prop_Bisim_paired
  C A1 P1 A2 P2 l\<^sub>0 a\<^sub>0 "\<lambda> _. True"
  using P2_cover by - (standard, blast)

lemma sim_reaches_equiv:
  "P2_invariant'.reaches (l, Z) (l', Z') \<longleftrightarrow> sim.Steps.reaches (from_R l Z) (from_R l' Z')"
  if "P2 (l, Z)"
  apply (subst bisim.reaches_equiv[of "\<lambda> (l, Z). from_R l Z"])
      apply force
     apply clarsimp
  subgoal
    by (metis Int_emptyI R_of_from_R from_R_fst sim.P2_cover)
    apply (rule that)
  subgoal
    apply clarsimp
    using P2'_def from_R_fst that by force
  by auto

lemma reaches_all:
  assumes
    "\<And> u u' R l. u \<in> R \<Longrightarrow> u' \<in> R \<Longrightarrow> P1 (l, R) \<Longrightarrow> P l u \<longleftrightarrow> P l u'"
  shows
    "(\<forall> u. (\<exists> x\<^sub>0\<in>\<Union>(sim.closure (from_R l\<^sub>0 a\<^sub>0)). sim.reaches x\<^sub>0 (l, u)) \<longrightarrow> P l u) \<longleftrightarrow>
     (\<forall> Z u. P2_invariant'.reaches (l\<^sub>0, a\<^sub>0) (l, Z) \<and> u \<in> Z \<longrightarrow> P l u)"
proof -
  let ?P = "\<lambda> (l, u). P l u"
  have *: "\<And>a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1' a \<Longrightarrow> ?P x = ?P y"
    unfolding P1'_def by clarsimp (subst assms[rotated 2], force+, metis fst_conv)+
  let ?P = "\<lambda> (l', u). l' = l \<longrightarrow> P l u"
  have *: "x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1' a \<Longrightarrow> ?P x = ?P y" for a x y
    by (frule *[of x a y], assumption+; auto simp: P1'_def; metis fst_conv)
  have
    "(\<forall>b. (\<exists>y\<in>sim.closure (from_R l\<^sub>0 a\<^sub>0). \<exists>x\<^sub>0\<in>y. sim.reaches x\<^sub>0 (l, b)) \<longrightarrow> P l b) \<longleftrightarrow>
     (\<forall>b ba. sim.Steps.reaches (from_R l\<^sub>0 a\<^sub>0) b \<and> (l, ba) \<in> b \<longrightarrow> P l ba)"
    unfolding sim.reaches_steps_iff sim.Steps.reaches_steps_iff
    apply safe
    subgoal for b b' xs
      apply (rule reaches_all_1[of ?P xs "(l, b')", simplified])
          apply (erule *; assumption; fail)
         apply (simp; fail)+
      done

    subgoal premises prems for b y a b' xs
      apply (rule
          reaches_all_2[of ?P xs y, unfolded \<open>last xs = (l, b)\<close>, simplified]
          )
          apply (erule *; assumption; fail)
      using prems by auto
    done
  then show ?thesis
    unfolding sim_reaches_equiv[OF P2_a\<^sub>0']
    apply simp
    subgoal premises prems
      apply safe
      subgoal for Z u
        unfolding from_R_def by auto
      subgoal for a u
        apply (frule P2_invariant.invariant_reaches)
        apply (auto dest!: Start.P2'_from_R simp: from_R_def)
        done
      done
    done
qed

context
  fixes P Q :: "'a \<Rightarrow> bool" \<comment> \<open>The state properties we want to check\<close>
begin

definition "\<phi>' = P o fst"

definition "\<psi> = Q o fst"

lemma \<psi>_closure_compatible:
  "\<psi> (l, x) \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 (l, a) \<Longrightarrow> \<psi> (l, y)"
  unfolding \<phi>'_def \<psi>_def by auto

lemma \<psi>_closure_compatible':
  "(Not o \<psi>) (l, x) \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 (l, a) \<Longrightarrow> (Not o \<psi>) (l, y)"
  by (auto dest: \<psi>_closure_compatible)

lemma P1_P1':
  "R \<noteq> {} \<Longrightarrow> P1 (l, R) \<Longrightarrow> P1' (from_R l R)"
  using P1'_def from_R_fst by fastforce

lemma \<psi>_Alw_ev_compatible:
  assumes "u \<in> R" "u' \<in> R" "P1 (l, R)"
  shows "sim.Alw_ev (Not \<circ> \<psi>) (l, u) = sim.Alw_ev (Not \<circ> \<psi>) (l, u')"
  apply (rule bisim.Alw_ev_compatible[of _ _ "from_R l R"])
  subgoal for x a y
    using \<psi>_closure_compatible unfolding P1'_def by (metis \<psi>_def comp_def)
  using assms by (auto intro: P1_P1')

interpretation Graph_Start_Defs A2 "(l\<^sub>0, a\<^sub>0)" .

interpretation G\<^sub>\<psi>: Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). A2 (l, Z) (l', Z') \<and> Q l'" "(l\<^sub>0, a\<^sub>0)" .

end (* State *)

end (* Double Simulation Complete Bisim Cover paired *)

context Double_Simulation_Finite_Complete_Bisim_Cover_paired
begin

interpretation bisim: Bisimulation_Invariant A2 A2' "\<lambda> (l, Z) b. b = from_R l Z" P2 P2'
  by (rule A2_A2'_bisim[OF P2_invariant])

context
  fixes P Q :: "'a \<Rightarrow> bool" \<comment> \<open>The state properties we want to check\<close>
begin

interpretation Graph_Start_Defs A2 "(l\<^sub>0, a\<^sub>0)" .

interpretation G\<^sub>\<psi>: Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). A2 (l, Z) (l', Z') \<and> Q l'" "(l\<^sub>0, a\<^sub>0)" .

lemma Alw_ev_mc1:
  "(\<forall>x\<^sub>0\<in>from_R l Z. sim.Alw_ev (Not \<circ> \<psi> Q) x\<^sub>0) \<longleftrightarrow>
      \<not> (Q l \<and> (\<exists>a. G\<^sub>\<psi>.reaches (l, Z) a \<and> G\<^sub>\<psi>.reaches1 a a))"
  if "P2_invariant'.reachable (l, Z)" for l Z
proof -
  from that have "P2 (l, Z)"
    using P2_invariant'.invariant_reaches unfolding P2_invariant'.reachable_def by auto
  interpret Start': Double_Simulation_Finite_Complete_Abstraction_Prop_Bisim_paired
    C A1 P1 A2 P2 l Z Q
    apply standard
    subgoal
      by (fact complete)
    subgoal
      by (fact P2_invariant)
    subgoal
      by (fact \<open>P2 (l, Z)\<close>)
    subgoal
      using P2_cover by blast
    subgoal
      by (fact A1_complete)
    subgoal
      by (fact P1_invariant)
    subgoal
    proof -
      have "{(l', a). A2\<^sup>*\<^sup>* (l,Z) (l',a) \<and> P2 (l',a)} \<subseteq> {(l, a). A2\<^sup>*\<^sup>* (l\<^sub>0,a\<^sub>0) (l,a) \<and> P2 (l,a)}"
        using that unfolding P2_invariant'.reachable_def by auto
      with finite_abstract_reachable show ?thesis
        by - (erule finite_subset)
    qed
    done
  show ?thesis
    using Start'.Alw_ev_mc1[unfolded Start'.\<phi>_def]
    unfolding \<psi>_def Graph_Start_Defs.reachable_def from_R_def by auto
qed

theorem leadsto_mc1:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.leadsto (\<phi>' P) (Not \<circ> \<psi> Q) (l\<^sub>0, x\<^sub>0)) \<longleftrightarrow>
   (\<nexists>x. P2_invariant'.reaches (l\<^sub>0, a\<^sub>0) x \<and> P (fst x) \<and> Q (fst x)
      \<and> (\<exists>a. G\<^sub>\<psi>.reaches x a \<and> G\<^sub>\<psi>.reaches1 a a)
   )"
  if  no_deadlock: "\<forall>x\<^sub>0\<in>a\<^sub>0. \<not> sim.deadlock (l\<^sub>0, x\<^sub>0)"
proof -
  from steps_Steps_no_deadlock[OF no_deadlock_closureI] no_deadlock have
    "\<not> sim.Steps.deadlock (from_R l\<^sub>0 a\<^sub>0)"
    unfolding from_R_def by auto
  then have no_deadlock': "\<not> P2_invariant'.deadlock (l\<^sub>0, a\<^sub>0)"
    by (subst bisim.deadlock_iff) (auto simp: P2_a\<^sub>0' from_R_fst P2'_def)
  have "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.leadsto (\<phi>' P) (Not \<circ> \<psi> Q) (l\<^sub>0, x\<^sub>0)) \<longleftrightarrow>
    (\<forall>x\<^sub>0\<in>from_R l\<^sub>0 a\<^sub>0. sim.leadsto (\<phi>' P) (Not \<circ> \<psi> Q) x\<^sub>0)
    "
    unfolding from_R_def by auto
  also have "\<dots> \<longleftrightarrow> sim.Steps.Alw_alw (\<lambda>a. \<forall>c\<in>a. \<phi>' P c \<longrightarrow> sim.Alw_ev (Not \<circ> \<psi> Q) c) (from_R l\<^sub>0 a\<^sub>0)"
    apply (rule Leadsto_iff2[OF _ _ _])
    subgoal for a x y
      unfolding P1'_def \<phi>'_def by (auto dest: fst_simp)
    subgoal for a x y
      unfolding P1'_def \<psi>_def by (auto dest: fst_simp)
    subgoal
      using no_deadlock unfolding from_R_def by auto
    done
  also have
    "\<dots>\<longleftrightarrow> P2_invariant'.Alw_alw (\<lambda>(l,Z).\<forall>c\<in>from_R l Z. \<phi>' P c \<longrightarrow> sim.Alw_ev (Not \<circ> \<psi> Q) c) (l\<^sub>0,a\<^sub>0)"
    by (auto simp: bisim.A_B.equiv'_def P2_a\<^sub>0 P2_a\<^sub>0' intro!: bisim.Alw_alw_iff_strong[symmetric])
  also have
    "\<dots> \<longleftrightarrow> P2_invariant'.Alw_alw
      (\<lambda>(l, Z). P l \<longrightarrow> \<not> (Q l \<and> (\<exists>a. G\<^sub>\<psi>.reaches (l, Z) a \<and> G\<^sub>\<psi>.reaches1 a a))) (l\<^sub>0, a\<^sub>0)"
    by (rule P2_invariant'.Alw_alw_iff_default)
       (auto simp: \<phi>'_def from_R_def dest: Alw_ev_mc1[symmetric])
  also have
    "\<dots> \<longleftrightarrow> (\<nexists>x. P2_invariant'.reaches (l\<^sub>0,a\<^sub>0) x \<and> P (fst x) \<and> Q (fst x)
      \<and> (\<exists>a. G\<^sub>\<psi>.reaches x a \<and> G\<^sub>\<psi>.reaches1 a a))"
    unfolding P2_invariant'.Alw_alw_iff by (auto simp: P2_invariant'.Ex_ev no_deadlock')
  finally show ?thesis .
qed

end (* State *)

end (* Double Simulation Finite Complete Bisim Cover paired *)

paragraph \<open>The second bisimulation property in prestable and complete simulation graphs.\<close>

context Simulation_Graph_Complete_Prestable
begin

lemma C_A_bisim:
  "Bisimulation_Invariant C A (\<lambda> x a. x \<in> a) (\<lambda>_. True) P"
  by (standard; blast intro: complete dest: prestable)

interpretation Bisimulation_Invariant C A "\<lambda> x a. x \<in> a" "\<lambda> _. True" P
  by (rule C_A_bisim)

lemma C_A_Leadsto_iff:
  fixes \<phi> \<psi> :: "'a \<Rightarrow> bool"
  assumes \<phi>_compatible: "\<And> x y a. \<phi> x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P a \<Longrightarrow> \<phi> y"
      and \<psi>_compatible: "\<And> x y a. \<psi> x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P a \<Longrightarrow> \<psi> y"
      and "x \<in> a" "P a"
    shows "leadsto \<phi> \<psi> x = Steps.leadsto (\<lambda> a. \<forall> x \<in> a. \<phi> x) (\<lambda> a. \<forall> x \<in> a. \<psi> x) a"
  by (rule Leadsto_iff)
     (auto intro: \<phi>_compatible \<psi>_compatible simp: \<open>x \<in> a\<close> \<open>P a\<close> simulation.equiv'_def)

end (* Simulation Graph Complete Prestable *)

section \<open>Comments\<close>

text \<open>
\<^item> Pre-stability can easily be extended to infinite runs (see construction with @{term sscan} above)
\<^item> Post-stability can not
\<^item> Pre-stability + Completeness means that for every two concrete states in the same abstract class,
  there are equivalent runs
\<^item> For Büchi properties, the predicate has to be compatible with whole closures instead of single
  \<open>P1\<close>-states. This is because for a finite graph where every node has at least indegree one,
  we cannot necessarily conclude that there is a cycle through \<^emph>\<open>every\<close> node.
\<^item> Can offer representation view via suitable locale instantiations?
\<^item> Abstractions view?
\<^item> \<open>\<phi>\<close>-construction can be done on an automaton too (also for disjunctions)
\<^item> Büchi properties are nothing but \<open>\<box>\<diamond>\<close>-properties (@{term \<open>alw (ev \<phi>)\<close>}
\<close>


locale Graph_Abstraction =
  Graph_Defs A for A :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" +
fixes \<alpha> :: "'a set \<Rightarrow> 'a set"
assumes idempotent: "\<alpha>(\<alpha>(x)) = \<alpha>(x)"
assumes enlarging: "x \<subseteq> \<alpha>(x)"
assumes \<alpha>_mono: "x \<subseteq> y \<Longrightarrow> \<alpha>(x) \<subseteq> \<alpha>(y)"
assumes mono: "a \<subseteq> a' \<Longrightarrow> A a b \<Longrightarrow> \<exists>b'. b \<subseteq> b' \<and> A a' b'"
assumes finite_abstraction: "finite (\<alpha> ` UNIV)"
begin

definition E where "E a b \<equiv> \<exists>b'. A a b' \<and> b = \<alpha>(b')"

interpretation sim1: Simulation_Invariant A E "\<lambda>a b. \<alpha>(a) \<subseteq> b" "\<lambda>_. True" "\<lambda>_. True"
  apply standard
  unfolding E_def
    apply auto
  apply (frule mono[rotated])
   apply (erule order.trans[rotated], rule enlarging)
  apply (auto intro!: \<alpha>_mono)
  done

interpretation sim2: Simulation_Invariant A E "\<lambda>a b. a \<subseteq> b" "\<lambda>_. True" "\<lambda>x. \<alpha>(x) = x"
  apply standard
  subgoal
    unfolding E_def
    apply auto
    apply (drule (1) mono)
    apply safe
    apply (intro conjI exI)
      apply assumption
     apply (rule HOL.refl)
    apply (erule order.trans, rule enlarging)
    done
   apply assumption
  unfolding E_def
  apply (elim exE conjE)
  apply (simp add: idempotent)
  done

text \<open>This variant needs the least assumptions.\<close>
interpretation sim3: Simulation_Invariant A E "\<lambda>a b. a \<subseteq> b" "\<lambda>_. True" "\<lambda>_. True"
  apply standard
  unfolding E_def
    apply auto
  apply (drule (1) mono)
  apply safe
  apply (intro conjI exI)
    apply assumption
   apply (rule HOL.refl)
  apply (erule order.trans, rule enlarging)
  done

interpretation sim4: Simulation_Invariant A E "\<lambda>a b. a \<subseteq> b" "\<lambda>_. True" "\<lambda>a. \<exists>a'. \<alpha> a' = a"
  apply standard
  unfolding E_def
    apply auto
  apply (drule (1) mono)
  apply safe
  apply (intro conjI exI)
    apply assumption
   apply (rule HOL.refl)
  apply (erule order.trans, rule enlarging)
  done

end (* Abstraction Operators *)

lemmas [simp del] = holds.simps

end (* Theory *)
