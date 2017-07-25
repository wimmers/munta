(* Author: Simon Wimmer *)
theory Graphs
  imports
    More_List Stream_More
    "~~/src/HOL/Library/Rewrite"
    Instantiate_Existentials
begin

chapter \<open>Graphs\<close>

section \<open>Basic Definitions and Theorems\<close>

locale Graph_Defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

inductive steps where
  Single: "steps [x]" |
  Cons: "steps (x # y # xs)" if "E x y" "steps (y # xs)"

lemmas [intro] = steps.intros

lemma steps_append:
  "steps (xs @ tl ys)" if "steps xs" "steps ys" "last xs = hd ys"
  using that by induction (auto 4 4 elim: steps.cases)

lemma steps_append':
  "steps xs" if "steps as" "steps bs" "last as = hd bs" "as @ tl bs = xs"
  using steps_append that by blast

coinductive run where
  "run (x ## y ## xs)" if "E x y" "run (y ## xs)"

lemmas [intro] = run.intros

lemma steps_appendD1:
  "steps xs" if "steps (xs @ ys)" "xs \<noteq> []"
  using that proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by - (cases xs; auto elim: steps.cases)
qed

lemma steps_appendD2:
  "steps ys" if "steps (xs @ ys)" "ys \<noteq> []"
  using that by (induction xs) (auto elim: steps.cases)

lemma steps_appendD3:
  "steps (xs @ [x]) \<and> E x y" if "steps (xs @ [x, y])"
  using that proof (induction xs)
  case Nil
  then show ?case by (auto elim!: steps.cases)
next
  case prems: (Cons a xs)
  then show ?case by (cases xs) (auto elim: steps.cases)
qed

lemma steps_ConsD:
  "steps xs" if "steps (x # xs)" "xs \<noteq> []"
  using that by (auto elim: steps.cases)

lemmas stepsD = steps_ConsD steps_appendD1 steps_appendD2

lemma steps_alt_induct[consumes 1, case_names Single Snoc]:
  assumes
    "steps x" "(\<And>x. P [x])"
    "\<And>y x xs. E y x \<Longrightarrow> steps (xs @ [y]) \<Longrightarrow> P (xs @ [y]) \<Longrightarrow> P (xs @ [y,x])"
  shows "P x"
  using assms(1)
  proof (induction rule: rev_induct)
    case Nil
    then show ?case by (auto elim: steps.cases)
  next
    case prems: (snoc x xs)
    then show ?case by (cases xs rule: rev_cases) (auto intro: assms(2,3) dest!: steps_appendD3)
  qed

lemma steps_appendI:
  "steps (xs @ [x, y])" if "steps (xs @ [x])" "E x y"
  using that
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by (cases xs; auto elim: steps.cases)
qed

lemma steps_append_single:
  assumes
    "steps xs" "E (last xs) x" "xs \<noteq> []"
  shows "steps (xs @ [x])"
  using assms(3,1,2) by (induction xs rule: list_nonempty_induct) (auto 4 4 elim: steps.cases)

lemma extend_run:
  assumes
    "steps xs" "E (last xs) x" "run (x ## ys)" "xs \<noteq> []"
  shows "run (xs @- x ## ys)"
  using assms(4,1-3) by (induction xs rule: list_nonempty_induct) (auto 4 3 elim: steps.cases)

lemma run_cycle:
  assumes "steps xs" "E (last xs) (hd xs)" "xs \<noteq> []"
  shows "run (cycle xs)"
  using assms proof (coinduction arbitrary: xs)
  case run
  then show ?case
    apply (rewrite at \<open>cycle xs\<close> stream.collapse[symmetric])
    apply (rewrite at \<open>stl (cycle xs)\<close> stream.collapse[symmetric])
    apply clarsimp
    apply (erule steps.cases)
    subgoal for x
      apply (rule conjI)
       apply (simp; fail)
      apply (rule disjI1)
      apply (inst_existentials xs)
         apply (simp, metis cycle_Cons[of x "[]", simplified])
      by auto
    subgoal for x y xs'
      apply (rule conjI)
       apply (simp; fail)
      apply (rule disjI1)
      apply (inst_existentials "y # xs' @ [x]")
      using steps_append_single[of "y # xs'" x]
         apply (auto elim: steps.cases split: if_split_asm)
       apply (subst (2) cycle_Cons, simp) (* XXX Automate forward reasoning *)
      apply (subst cycle_Cons, simp)
      done
    done
qed

lemma run_stl:
  "run (stl xs)" if "run xs"
  using that by (auto elim: run.cases)

lemma run_sdrop:
  "run (sdrop n xs)" if "run xs"
  using that by (induction n arbitrary: xs) (auto intro: run_stl)

lemma run_reachable':
  assumes "run (x ## xs)" "E\<^sup>*\<^sup>* x\<^sub>0 x"
  shows "pred_stream (\<lambda> x. E\<^sup>*\<^sup>* x\<^sub>0 x) xs"
  using assms by (coinduction arbitrary: x xs) (auto 4 3 elim: run.cases)

lemma run_reachable:
  assumes "run (x\<^sub>0 ## xs)"
  shows "pred_stream (\<lambda> x. E\<^sup>*\<^sup>* x\<^sub>0 x) xs"
  by (rule run_reachable'[OF assms]) blast

lemma run_decomp:
  assumes "run (xs @- ys)" "xs \<noteq> []"
  shows "steps xs \<and> run ys \<and> E (last xs) (shd ys)"
using assms(2,1) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: run.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: run.cases)
qed

lemma steps_decomp:
  assumes "steps (xs @ ys)" "xs \<noteq> []" "ys \<noteq> []"
  shows "steps xs \<and> steps ys \<and> E (last xs) (hd ys)"
using assms(2,1,3) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: steps.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: steps.cases)
qed

lemma steps_rotate:
  assumes "steps (x # xs @ y # ys @ [x])"
  shows "steps (y # ys @ x # xs @ [y])"
proof -
  from steps_decomp[of "x # xs" "y # ys @ [x]"] assms have
    "steps (x # xs)" "steps (y # ys @ [x])" "E (last (x # xs)) y"
    by auto
  then have "steps ((x # xs) @ [y])" by (blast intro: steps_append_single)
  from steps_append[OF \<open>steps (y # ys @ [x])\<close> this] show ?thesis by auto
qed

lemma run_shift_coinduct[case_names run_shift, consumes 1]:
  assumes "R w"
      and "\<And> w. R w \<Longrightarrow> \<exists> u v x y. w = u @- x ## y ## v \<and> steps (u @ [x]) \<and> E x y \<and> R (y ## v)"
  shows "run w"
  using assms(2)[OF \<open>R w\<close>] proof (coinduction arbitrary: w)
  case (run w)
  then obtain u v x y where "w = u @- x ## y ## v" "steps (u @ [x])" "E x y" "R (y ## v)"
    by auto
  then show ?case
    apply -
    apply (drule assms(2))
    apply (cases u)
     apply force
    subgoal for z zs
      apply (cases zs)
      subgoal
        apply simp
        apply safe
         apply (force elim: steps.cases)
        subgoal for u' v' x' y'
          by (inst_existentials "x # u'") (cases u'; auto)
        done
      subgoal for a as
        apply simp
        apply safe
         apply (force elim: steps.cases)
        subgoal for u' v' x' y'
          apply (inst_existentials "a # as @ x # u'")
          using steps_append[of "a # as @ [x, y]" "u' @ [x']"]
          apply simp
          apply (drule steps_appendI[of "a # as" x, rotated])
          by (cases u'; force elim: steps.cases)+
        done
      done
    done
qed

lemma run_flat_coinduct[case_names run_shift, consumes 1]:
  assumes "R xss"
    and
    "\<And> xs ys xss.
    R (xs ## ys ## xss) \<Longrightarrow> xs \<noteq> [] \<and> steps xs \<and> E (last xs) (hd ys) \<and> R (ys ## xss)"
  shows "run (flat xss)"
proof -
  obtain xs ys xss' where "xss = xs ## ys ## xss'" by (metis stream.collapse)
  with assms(2)[OF assms(1)[unfolded this]] show ?thesis
  proof (coinduction arbitrary: xs ys xss' xss rule: run_shift_coinduct)
    case (run_shift xs ys xss' xss)
    from run_shift show ?case
      apply (cases xss')
      apply clarify
      apply (drule assms(2))
      apply (inst_existentials "butlast xs" "tl ys @- flat xss'" "last xs" "hd ys")
         apply (cases ys)
          apply (simp; fail)
      subgoal premises prems for x1 x2 z zs
      proof (cases "xs = []")
        case True
        with prems show ?thesis
          by auto
      next
        case False
        then have "xs = butlast xs @ [last xs]" by auto
        then have "butlast xs @- last xs ## tail = xs @- tail" for tail
          by (metis shift.simps(1,2) shift_append)
        with prems show ?thesis by simp
      qed
        apply (simp; fail)
       apply assumption
      subgoal for ws wss
        by (inst_existentials ys ws wss) (cases ys, auto)
      done
  qed
qed

lemma steps_non_empty[simp]:
  "\<not> steps []"
  by (auto elim: steps.cases)

lemma steps_non_empty'[simp]:
  "xs \<noteq> []" if "steps xs"
  using that by auto

(* XXX Generalize *)
lemma steps_replicate:
  "steps (hd xs # concat (replicate n (tl xs)))" if "last xs = hd xs" "steps xs" "n > 0"
  using that
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    with Suc.prems show ?thesis by (cases xs; auto)
  next
    case prems: (Suc nat)
    from Suc.prems have [simp]: "hd xs # tl xs @ ys = xs @ ys" for ys
      by (cases xs; auto)
    from Suc.prems have **: "tl xs @ ys = tl (xs @ ys)" for ys
      by (cases xs; auto)
    from prems Suc show ?thesis
      by (fastforce intro: steps_append')
  qed
qed

notation E ("_ \<rightarrow> _" [100, 100] 40)

abbreviation reaches ("_ \<rightarrow>* _" [100, 100] 40) where "reaches x y \<equiv> E\<^sup>*\<^sup>* x y"

abbreviation reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40) where "reaches1 x y \<equiv> E\<^sup>+\<^sup>+ x y"

lemma steps_reaches:
  "hd xs \<rightarrow>* last xs" if "steps xs"
  using that by (induction xs) auto

lemma steps_reaches':
  "x \<rightarrow>* y" if "steps xs" "hd xs = x" "last xs = y"
  using that steps_reaches by auto

lemma reaches_steps:
  "\<exists> xs. hd xs = x \<and> last xs = y \<and> steps xs" if "x \<rightarrow>* y"
  using that
  apply (induction)
   apply force
  apply clarsimp
  subgoal for z xs
    by (inst_existentials "xs @ [z]", (cases xs; simp), auto intro: steps_append_single)
  done

lemma reaches_steps_iff:
  "x \<rightarrow>* y \<longleftrightarrow> (\<exists> xs. hd xs = x \<and> last xs = y \<and> steps xs)"
  using steps_reaches reaches_steps by fast

lemma steps_reaches1:
  "x \<rightarrow>\<^sup>+ y" if "steps (x # xs @ [y])"
  by (metis list.sel(1,3) rtranclp_into_tranclp2 snoc_eq_iff_butlast steps.cases steps_reaches that)

lemma stepsI:
  "steps (x # xs)" if "x \<rightarrow> hd xs" "steps xs"
  using that by (cases xs) auto

lemma reaches1_steps:
  "\<exists> xs. steps (x # xs @ [y])" if "x \<rightarrow>\<^sup>+ y"
proof -
  from that obtain z where "x \<rightarrow> z" "z \<rightarrow>* y"
    by atomize_elim (simp add: tranclpD)
  from reaches_steps[OF this(2)] obtain xs where *: "hd xs = z" "last xs = y" "steps xs"
    by auto
  then obtain xs' where [simp]: "xs = xs' @ [y]"
    by atomize_elim (auto 4 3 intro: append_butlast_last_id[symmetric])
  with \<open>x \<rightarrow> z\<close> * show ?thesis
    by (auto intro: stepsI)
qed

lemma reaches1_steps_iff:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> xs. steps (x # xs @ [y]))"
  using steps_reaches1 reaches1_steps by fast

lemma reaches1_reaches_iff1:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> z. x \<rightarrow> z \<and> z \<rightarrow>* y)"
  by (auto dest: tranclpD)

lemma reaches1_reaches_iff2:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> z. x \<rightarrow>* z \<and> z \<rightarrow> y)"
  apply safe
   apply (metis Nitpick.rtranclp_unfold tranclp.cases)
  by auto

lemma
  "x \<rightarrow>\<^sup>+ z" if "x \<rightarrow>* y" "y \<rightarrow>\<^sup>+ z"
  using that by auto

lemma
  "x \<rightarrow>\<^sup>+ z" if "x \<rightarrow>\<^sup>+ y" "y \<rightarrow>* z"
  using that by auto

lemma steps_append2:
  "steps (xs @ x # ys)" if "steps (xs @ [x])" "steps (x # ys)"
  using that by (auto dest: steps_append)

lemma reaches1_steps_append:
  assumes "a \<rightarrow>\<^sup>+ b" "steps xs" "hd xs = b"
  shows "\<exists> ys. steps (a # ys @ xs)"
  using assms by (fastforce intro: steps_append' dest: reaches1_steps)

lemma steps_last_step:
  "\<exists> a. a \<rightarrow> last xs" if "steps xs" "length xs > 1"
  using that by induction auto

lemmas graphI =
  steps.intros
  steps_append_single
  steps_reaches'
  stepsI

end (* Graph Defs *)


section \<open>Graphs with a Start Node\<close>

locale Graph_Start_Defs = Graph_Defs +
  fixes s\<^sub>0 :: 'a
begin

definition reachable where
  "reachable = E\<^sup>*\<^sup>* s\<^sub>0"

lemma start_reachable[intro!, simp]:
  "reachable s\<^sub>0"
  unfolding reachable_def by auto

lemma reachable_step:
  "reachable b" if "reachable a" "E a b"
  using that unfolding reachable_def by auto

lemma reachable_reaches:
  "reachable b" if "reachable a" "a \<rightarrow>* b"
  using that(2,1) by induction (auto intro: reachable_step)

lemma reachable_steps_append:
  assumes "reachable a" "steps xs" "hd xs = a" "last xs = b"
  shows "reachable b"
  using assms by (auto intro: graphI reachable_reaches)

lemmas steps_reachable = reachable_steps_append[of s\<^sub>0, simplified]

lemma reachable_steps_elem:
  "reachable y" if "reachable x" "steps xs" "y \<in> set xs" "hd xs = x"
proof -
  from \<open>y \<in> set xs\<close> obtain as bs where [simp]: "xs = as @ y # bs"
    by (auto simp: in_set_conv_decomp)
  show ?thesis
  proof (cases "as = []")
    case True
    with that show ?thesis
      by simp
  next
    case False
    (* XXX *)
    from \<open>steps xs\<close> have "steps (as @ [y])"
      by (auto intro: stepsD)
    with \<open>as \<noteq> []\<close> \<open>hd xs = x\<close> \<open>reachable x\<close> show ?thesis
      by (auto 4 3 intro: reachable_reaches graphI)
  qed
qed

lemma reachable_steps:
  "\<exists> xs. steps xs \<and> hd xs = s\<^sub>0 \<and> last xs = x" if "reachable x"
  using that unfolding reachable_def
proof induction
  case base
  then show ?case by (inst_existentials "[s\<^sub>0]"; force)
next
  case (step y z)
  from step.IH guess xs by clarify
  with step.hyps show ?case
    apply (inst_existentials "xs @ [z]")
    apply (force intro: graphI)
    by (cases xs; auto)+
qed

lemma reachable_cycle_iff:
  "reachable x \<and> x \<rightarrow>\<^sup>+ x \<longleftrightarrow> (\<exists> ws xs. steps (s\<^sub>0 # ws @ [x] @ xs @ [x]))"
proof (safe, goal_cases)
  case (2 ws)
  then show ?case
    by (auto intro: steps_reachable stepsD)
next
  case (3 ws xs)
  then show ?case
    by (auto intro: stepsD steps_reaches1)
next
  case prems: 1
  from \<open>reachable x\<close> prems(2) have "s\<^sub>0 \<rightarrow>\<^sup>+ x"
    unfolding reachable_def by auto
  with \<open>x \<rightarrow>\<^sup>+ x\<close> show ?case
    by (fastforce intro: steps_append' dest: reaches1_steps)
qed

lemma reachable_induct[consumes 1, case_names start step, induct pred: reachable]:
  assumes "reachable x"
    and "P s\<^sub>0"
    and "\<And> a b. reachable a \<Longrightarrow> P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> P b"
  shows "P x"
  using assms(1) unfolding reachable_def
  by induction (auto intro: assms(2-)[unfolded reachable_def])

lemmas graphI_aggressive =
  tranclp_into_rtranclp
  rtranclp.rtrancl_into_rtrancl
  tranclp.trancl_into_trancl
  rtranclp_into_tranclp2

lemmas graphI_aggressive1 =
  graphI_aggressive
  steps_append'

lemmas graphI_aggressive2 =
  graphI_aggressive
  stepsD
  steps_reaches1
  steps_reachable

lemmas graphD =
  reaches1_steps

lemmas graphD_aggressive =
  tranclpD

lemmas graph_startI =
  reachable_reaches

end (* Graph Start Defs *)


section \<open>Subgraphs\<close>

locale Subgraph_Defs = G: Graph_Defs +
  fixes E' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale G': Graph_Defs E' .

end (* Subgrap Defs *)

locale Subgraph_Start_Defs = G: Graph_Start_Defs +
  fixes E' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale G': Graph_Start_Defs E' s\<^sub>0 .

end (* Subgrap Start Defs *)

locale Subgraph = Subgraph_Defs +
  assumes subgraph[intro]: "E' a b \<Longrightarrow> E a b"
begin

lemma non_subgraph_cycle_decomp:
  "\<exists> c d. G.reaches a c \<and> E c d \<and> \<not> E' c d \<and> G.reaches d b" if
  "G.reaches1 a b" "\<not> G'.reaches1 a b" for a b
    using that
  proof induction
    case (base y)
    then show ?case
      by auto
  next
    case (step y z)
    show ?case
    proof (cases "E' y z")
      case True
      with step have "\<not> G'.reaches1 a y"
        by (auto intro: tranclp.trancl_into_trancl) (* XXX *)
      with step obtain c d where
        "G.reaches a c" "E c d" "\<not> E' c d" "G.reaches d y"
        by auto
      with \<open>E' y z\<close> show ?thesis
        by (blast intro: rtranclp.rtrancl_into_rtrancl) (* XXX *)
    next
      case False
      with step show ?thesis
        by (intro exI conjI) auto
    qed
  qed

end (* Subgraph *)

locale Subgraph_Start = Subgraph_Start_Defs + Subgraph
begin

lemma reachable_subgraph[intro]: "G.reachable b" if \<open>G.reachable a\<close> \<open>G'.reaches a b\<close> for a b
  using that
  by (auto 4 3 intro: G.graph_startI mono_rtranclp[rule_format, of E'])

end (* Subgraph Start *)


section \<open>Bundles\<close>

bundle graph_automation
begin

lemmas [intro] = Graph_Defs.graphI Graph_Start_Defs.graph_startI
lemmas [dest]  = Graph_Start_Defs.graphD

end (* Bundle *)

bundle reaches_steps_iff =
  Graph_Defs.reaches1_steps_iff [iff]
  Graph_Defs.reaches_steps_iff  [iff]

bundle graph_automation_aggressive
begin

unbundle graph_automation

lemmas [intro] = Graph_Start_Defs.graphI_aggressive
lemmas [dest]  = Graph_Start_Defs.graphD_aggressive

end (* Bundle *)


section \<open>Simulations and Bisimulations\<close>

locale Graph_Invariant = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> P b"
begin

lemma invariant_steps:
  "list_all P as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma invariant_reaches:
  "P b" if "a \<rightarrow>* b" "P a"
  using that by (induction; blast intro: invariant)

lemma invariant_run:
  assumes run: "run (x ## xs)" and P: "P x"
  shows "pred_stream P (x ## xs)"
  using run P by (coinduction arbitrary: x xs) (auto 4 3 elim: invariant run.cases)

end (* Graph Invariant *)

locale Graph_Invariant_Start = Graph_Start_Defs + Graph_Invariant +
  assumes P_s\<^sub>0: "P s\<^sub>0"
begin

lemma invariant_steps:
  "list_all P as" if "steps (s\<^sub>0 # as)"
  using that P_s\<^sub>0 by (rule invariant_steps)

lemma invariant_reaches:
  "P b" if "s\<^sub>0 \<rightarrow>* b"
  using invariant_reaches[OF that P_s\<^sub>0] .

lemmas invariant_run = invariant_run[OF _ P_s\<^sub>0]

end (* Graph Invariant Start *)

locale Graph_Invariant_Strong = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "a \<rightarrow> b \<Longrightarrow> P b"
begin

sublocale inv: Graph_Invariant by standard (rule invariant)

lemma P_invariant_steps:
  "list_all P as" if "steps (a # as)"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma steps_last_invariant:
  "P (last xs)" if "steps (x # xs)" "xs \<noteq> []"
  using steps_last_step[of "x # xs"] that by (auto intro: invariant)

lemmas invariant_reaches = inv.invariant_reaches

lemma invariant_reaches1:
  "P b" if "a \<rightarrow>\<^sup>+ b"
  using that by (induction; blast intro: invariant)

end (* Graph Invariant *)

locale Simulation_Defs =
  fixes A :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and sim :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "\<sim>" 60)
begin

sublocale A: Graph_Defs A .

sublocale B: Graph_Defs B .

end (* Simulation Defs *)

locale Simulation = Simulation_Defs +
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
begin

lemma simulation_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b"
  using that by (induction rule: rtranclp_induct) (auto intro: rtranclp.intros(2) dest: A_B_step)

lemma simulation_steps:
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs" if "A.steps (a # as)" "a \<sim> b"
  using that
  apply (induction "a # as" arbitrary: a b as)
   apply force
  apply (frule A_B_step, auto)
  done

end (* Simulation *)

locale Simulation_Invariants = Simulation_Defs +
  fixes PA :: "'a \<Rightarrow> bool" and PB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a b \<Longrightarrow> PA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a b \<Longrightarrow> PB b"
begin

definition "equiv' \<equiv> \<lambda> a b. a \<sim> b \<and> PA a \<and> PB b"

sublocale Simulation A B equiv' by standard (auto dest: A_B_step simp: equiv'_def)

sublocale PA_invariant: Graph_Invariant A PA by standard blast

lemma simulation_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b' \<and> PA a' \<and> PB b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b" "PA a" "PB b"
  using simulation_reaches[of a a' b] that unfolding equiv'_def by simp

lemma simulation_steps:
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b \<and> PA a \<and> PB b) as bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
  using simulation_steps[of a as b] that unfolding equiv'_def by simp

lemma simulation_steps':
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs \<and> list_all PA as \<and> list_all PB bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
  using simulation_steps[OF that]
  by (force dest: list_all2_set1 list_all2_set2 simp: list_all_iff elim: list_all2_mono)

context
  fixes f
  assumes eq: "a \<sim> b \<Longrightarrow> b = f a"
begin

lemma simulation_steps'_map:
  "\<exists> bs.
    B.steps (b # bs) \<and> bs = map f as
    \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs
    \<and> list_all PA as \<and> list_all PB bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
proof -
  from simulation_steps'[OF that] guess bs by clarify
  note guessed = this
  from this(2) have "bs = map f as"
    by (induction; simp add: eq)
  with guessed show ?thesis
    by auto
qed

end (* Context for Equality Relation *)

end (* Simulation *)

locale Bisimulation = Simulation_Defs +
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> a a' b'. B a' b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b. A a b \<and> b \<sim> b')"
begin

sublocale A_B: Simulation A B "op \<sim>" by standard (rule A_B_step)

sublocale B_A: Simulation B A "\<lambda> x y. y \<sim> x" by standard (rule B_A_step)

lemma A_B_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b"
  using A_B.simulation_reaches[OF that] .

lemma B_A_reaches:
  "\<exists> b'. A\<^sup>*\<^sup>* b b' \<and> b' \<sim> a'" if "B\<^sup>*\<^sup>* a a'" "b \<sim> a"
  using B_A.simulation_reaches[OF that] .

end (* Bisim *)

locale Bisimulation_Invariants = Simulation_Defs +
  fixes PA :: "'a \<Rightarrow> bool" and PB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> a a' b'. B a' b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b. A a b \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a b \<Longrightarrow> PA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a b \<Longrightarrow> PB b"
begin

sublocale PA_invariant: Graph_Invariant A PA by standard blast

sublocale PB_invariant: Graph_Invariant B PB by standard blast

lemmas B_steps_invariant[intro] = PB_invariant.invariant_reaches

definition "equiv' \<equiv> \<lambda> a b. a \<sim> b \<and> PA a \<and> PB b"

sublocale bisim: Bisimulation A B equiv'
  by standard (clarsimp simp add: equiv'_def, frule A_B_step B_A_step, assumption; auto)+

sublocale A_B: Simulation_Invariants A B "op \<sim>" PA PB
  by (standard; blast intro: A_B_step B_A_step)

sublocale B_A: Simulation_Invariants B A "\<lambda> x y. y \<sim> x" PB PA
  by (standard; blast intro: A_B_step B_A_step)

context
  fixes f
  assumes eq: "a \<sim> b \<longleftrightarrow> b = f a"
    and inj: "\<forall> a b. PB (f a) \<and> PA b \<and> f a = f b \<longrightarrow> a = b"
begin

lemma list_all2_inj_map_eq:
  "as = bs" if "list_all2 (\<lambda>a b. a = f b) (map f as) bs" "list_all PB (map f as)" "list_all PA bs"
  using that inj
  by (induction "map f as" bs arbitrary: as rule: list_all2_induct) (auto simp: inj_on_def)

lemma steps_map_equiv:
  "A.steps (a # as) \<longleftrightarrow> B.steps (b # map f as)" if "a \<sim> b" "PA a" "PB b"
  using A_B.simulation_steps'_map[of f a as b] B_A.simulation_steps'[of b "map f as" a] that eq
  by (auto dest: list_all2_inj_map_eq)

lemma steps_map:
  "\<exists> as. bs = map f as" if "B.steps (f a # bs)" "PA a" "PB (f a)"
proof -
  have "a \<sim> f a" unfolding eq ..
  from B_A.simulation_steps'[OF that(1) this \<open>PB _\<close> \<open>PA _\<close>] guess as by clarify
  from this(2) show ?thesis
    unfolding eq by (inst_existentials as, induction rule: list_all2_induct, auto)
qed

lemma reaches_equiv:
  "A.reaches a a' \<longleftrightarrow> B.reaches (f a) (f a')" if "PA a" "PB (f a)"
  apply safe
   apply (drule A_B.simulation_reaches[of a a' "f a"]; simp add: eq that)
  apply (drule B_A.simulation_reaches)
     defer
     apply (rule that | clarsimp simp: eq | metis inj)+
  done

end (* Context for Equality Relation *)

end (* Bisim Invariants *)

end (* Theory *)