theory Simulation_Graphs
  imports
    "library/Graphs"
    "library/More_List"
    Normalized_Zone_Semantics
begin

chapter \<open>Simulation Graphs\<close>

paragraph \<open>Misc\<close>

text \<open>
  A directed graph where every node has at least one ingoing edge, contains a directed cycle.
\<close>
lemma directed_graph_indegree_ge_1_cycle:
  assumes "finite S" "S \<noteq> {}" "\<forall> y \<in> S. \<exists> x \<in> S. E x y"
  shows "\<exists> x \<in> S. \<exists> y. E x y \<and> E\<^sup>*\<^sup>* y x"
  using assms
proof (induction arbitrary: E rule: finite_ne_induct)
  case (singleton x)
  then show ?case by auto
next
  case (insert x S E)
  from insert.prems obtain y where "y \<in> insert x S" "E y x"
    by auto
  show ?case
  proof (cases "y = x")
    case True
    with \<open>E y x\<close> show ?thesis by auto
  next
    case False
    with \<open>y \<in> _\<close> have "y \<in> S" by auto
    define E' where "E' a b \<equiv> E a b \<or> (a = y \<and> E x b)" for a b
    have E'_E: "\<exists> c. E a c \<and> E\<^sup>*\<^sup>* c b" if "E' a b" for a b
      using that \<open>E y x\<close> unfolding E'_def by auto
    have [intro]: "E\<^sup>*\<^sup>* a b" if "E' a b" for a b
      using that \<open>E y x\<close> unfolding E'_def by auto
    have [intro]: "E\<^sup>*\<^sup>* a b" if "E'\<^sup>*\<^sup>* a b" for a b
      using that by (induction; blast intro: rtranclp_trans)
    have "\<forall>y\<in>S. \<exists>x\<in>S. E' x y"
    proof (rule ballI)
      fix b assume "b \<in> S"
      with insert.prems obtain a where "a \<in> insert x S" "E a b"
        by auto
      show "\<exists>a\<in>S. E' a b"
      proof (cases "a = x")
        case True
        with \<open>E a b\<close> have "E' y b" unfolding E'_def by simp
        with \<open>y \<in> S\<close> show ?thesis ..
      next
        case False
        with \<open>a \<in> _\<close> \<open>E a b\<close> show ?thesis unfolding E'_def by auto
      qed
    qed
    from insert.IH[OF this] guess x y by safe
    then show ?thesis by (blast intro: rtranclp_trans dest: E'_E)
    qed
  qed

(* XXX Move? *)
lemma prod_set_fst_id:
  "x = y" if "\<forall> a \<in> x. fst a = b" "\<forall> a \<in> y. fst a = b" "snd ` x = snd ` y"
  using that by (auto 4 6 simp: fst_def snd_def image_def split: prod.splits)


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


section \<open>Poststability\<close>

locale Simulation_Graph_Poststable = Simulation_Graph_Defs +
  assumes poststable: "A S T \<Longrightarrow> \<forall> s' \<in> T. \<exists> s \<in> S. C s s'"
begin

lemma Steps_poststable:
  "\<exists> xs. steps xs \<and> list_all2 (op \<in>) xs as \<and> last xs = x" if "Steps as" "x \<in> last as"
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
    by (force dest!: directed_graph_indegree_ge_1_cycle[where E = E])
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

(* XXX Unused *)
lemma Steps_steps_cycle':
  "\<exists> xs. steps xs \<and> hd xs = last xs \<and> (\<forall> x \<in> set xs. \<exists> a \<in> set as. x \<in> a) \<and> hd xs \<in> hd as"
  if assms: "Steps as" "hd as = last as" "finite (hd as)" "hd as \<noteq> {}"
proof -
  define E where
    "E x y = (\<exists> xs. steps xs \<and> hd xs = x \<and> last xs = y \<and> (\<forall> x \<in> set xs. \<exists> a \<in> set as. x \<in> a))"
    for x y
  from assms(2-) have "\<exists> x. E x y \<and> x \<in> hd as" if "y \<in> hd as" for y
    using that unfolding E_def
    apply simp
    apply (drule Steps_poststable[OF assms(1)])
    apply clarify
    subgoal for xs
      apply (inst_existentials "hd xs" xs)
        apply ((assumption | rule HOL.refl); fail)+
       apply (blast intro!: list_all2_set1)
      by (metis list.rel_sel list.simps(3) steps.cases)
    done
  with \<open>finite (hd as)\<close> \<open>hd as \<noteq> {}\<close> obtain x y where cycle: "E x y" "E\<^sup>*\<^sup>* y x" "x \<in> hd as"
    by (force dest!: directed_graph_indegree_ge_1_cycle[where E = E])
  from assms have "as \<noteq> []" by cases auto
  have trans[intro]: "E x z" if "E x y" "E y z" for x y z
    using that unfolding E_def
    apply safe
    subgoal for xs ys
      apply (inst_existentials "xs @ tl ys")
         apply (rule steps_append; assumption)
      by (cases ys, auto dest: list.set_sel(2)[rotated] elim: steps.cases)
    done
  have "E x y" if "E\<^sup>*\<^sup>* x y" "x \<in> hd as" for x y
  using that proof induction
    case base
    with \<open>as \<noteq> []\<close> show ?case unfolding E_def by force
  next
    case (step y z)
    then show ?case by auto
  qed
  with cycle have "E x x" by blast
  with \<open>x \<in> hd as\<close> show ?thesis unfolding E_def by auto
qed

end (* Simulation Graph Poststable *)


section \<open>Prestability\<close>

locale Simulation_Graph_Prestable = Simulation_Graph_Defs +
  assumes prestable: "A S T \<Longrightarrow> \<forall> s \<in> S. \<exists> s' \<in> T. C s s'"
begin

(* XXX Unused *)
lemma Steps_prestable:
  "\<exists> xs. steps (x # xs) \<and> list_all2 (op \<in>) (x # xs) as" if "Steps as" "x \<in> hd as"
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

text \<open>Abstract cycles lead to concrete infinite runs.\<close>
lemma Steps_run_cycle_buechi:
  "\<exists> xs. run (x ## xs) \<and> stream_all2 op \<in> xs (cycle (as @ [a]))"
  if assms: "Steps (a # as @ [a])" "x \<in> a"
proof -
  note C = Steps_prestable[OF assms(1), simplified]
  define P where "P \<equiv> \<lambda> x xs. steps (last x # xs) \<and> list_all2 (op \<in>) xs (as @ [a])"
  define f where "f \<equiv> \<lambda> x. SOME xs. P x xs"
  from Steps_prestable[OF assms(1)] \<open>x \<in> a\<close> obtain ys where ys:
    "steps (x # ys)" "list_all2 op \<in> (x # ys) (a # as @ [a])"
    by auto
  define xs where "xs = flat (siterate f ys)"
  from ys have "P [x] ys" unfolding P_def by auto
  from \<open>P _ _\<close> have *: "\<exists> xs. P xs ys" by blast
  have P_1[intro]:"ys \<noteq> []" if "P xs ys" for xs ys using that unfolding P_def by (cases ys) auto
  have P_2[intro]: "last ys \<in> a" if "P xs ys" for xs ys
    using that P_1[OF that] unfolding P_def by (auto dest:  list_all2_last)
  from * have "stream_all2 op \<in> xs (cycle (as @ [a]))"
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
  "\<exists> xs. run (x ## xs) \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> a) \<and> infs b (x ## xs)"
  if assms: "Steps (a # as @ [a])" "x \<in> a" "b \<in> set (a # as @ [a])"
  using Steps_run_cycle_buechi[OF that(1,2)] that(2,3)
  apply safe
  apply (rule exI conjI)+
   apply assumption
  apply (subst alw_ev_stl[symmetric])
  by (force dest: alw_ev_HLD_cycle[of _ _ b] stream_all2_sset1)

lemma Steps_run_cycle_buechi':
  "\<exists> xs. run (x ## xs) \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> a) \<and> infs a (x ## xs)"
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

end (* Simulation Graph Prestable *)


section \<open>Double Simulation\<close>

locale Double_Simulation_Defs =
  fixes C :: "'a \<Rightarrow> 'a \<Rightarrow> bool" -- "Concrete step relation"
    and A1 :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" -- "Step relation for the first abstraction layer"
    and P1 :: "'a set \<Rightarrow> bool" -- "Valid states of the first abstraction layer"
    and A2 :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" -- "Step relation for the second abstraction layer"
    and P2 :: "'a set \<Rightarrow> bool" -- "Valid states of the second abstraction layer"
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

sublocale pre: Simulation_Graph_Prestable C A1 by standard (rule prestable)

lemma closure_involutive:
  "closure (\<Union> closure x) = closure x"
  unfolding closure_def by (auto dest: P1_distinct)

lemma closure_finite:
  "finite (closure x)"
  using P1_finite unfolding closure_def by auto

lemma closure_non_empty:
  "closure x \<noteq> {}" if "P2 x"
  using that unfolding closure_def by (auto dest!: P2_cover)

lemma A2'_A2_closure:
  "A2' (closure x) (closure y)" if "A2 x y"
  using that unfolding A2'_def by auto

lemma Steps_Union:
  "\<exists> as. post_defs.Steps (a # as) \<and> list_all2 (\<lambda> x a. a = closure x) (x # xs) (a # as)"
  if "Steps (x # xs)" "a = closure x"
using that proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc y xs)
  from snoc.prems(1) Steps_appendD1[of "x # xs"] have "Steps (x # xs)" by simp
  from snoc.IH[OF this snoc.prems(2-)] guess as by safe
  note guessed = this
  show ?case
  proof (cases xs rule: rev_cases)
    case Nil
    with snoc.prems have "A2 x y" by (auto elim: Steps_cases)
    with guessed \<open>xs = _\<close> show ?thesis by (auto dest!: A2'_A2_closure)
  next
    case (snoc ys z)
    with snoc.prems have "A2 z y"
      by (metis Steps.steps_appendD3 append_Cons append_assoc append_self_conv2)
    with snoc guessed obtain as' where [simp]: "as = as' @ [closure z]"
      by (auto simp add: list_all2_append1 list_all2_Cons1)
    with \<open>A2 z y\<close> have "A2' (closure z) (closure y)" by (auto dest!: A2'_A2_closure)
    then show ?thesis
      apply (inst_existentials "as' @ [closure z, closure y]")
      using guessed post_defs.Steps_appendI[of "a # as'" "closure z" "closure y"] apply force
      using guessed
      apply safe
      unfolding list_all2_append1
      apply (inst_existentials "as' @ [closure z]" "[closure y]")
      by (auto dest: list_all2_lengthD)
  qed
qed

(* XXX Unused? *)
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
  "\<exists> xs. run xs \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a}. x \<in> \<Union> closure a) \<and> shd xs \<in> \<Union> closure a"
  if assms: "Steps (a # as @ [a])" "P2 a"
proof -
  from Steps_Union[OF assms(1) HOL.refl] guess as1 by safe
  note as1 = this
  obtain as1 where
    "post_defs.Steps (closure a # as1 @ [closure a])"
    "list_all2 (\<lambda>x a. a = closure x) (a # as @ [a]) (closure a # as1 @ [closure a])"
  proof (atomize_elim, cases "as = []", goal_cases)
    case 1
    with as1 have "post_defs.Steps [closure a, closure a]" by (simp add: list_all2_Cons1)
    with \<open>as = []\<close> show ?case by - (rule exI[where x = "[]"]; simp)
  next
    case 2
    with as1 obtain as2 where "as1 = as2 @ [closure a]"
      by (auto simp: list_all2_append1 list_all2_Cons1)
    with as1 show ?case by auto
  qed
  from Steps_run_cycle'[OF this(1) closure_finite closure_non_empty[OF \<open>P2 a\<close>]] this(2)
  show ?thesis by (force dest: list_all2_set2)
qed

lemma Steps_run_cycle'':
  "\<exists> x xs. run (x ## xs) \<and> x \<in> \<Union> closure a\<^sub>0
  \<and> (\<forall> x \<in> sset xs. \<exists> a \<in> set as \<union> {a} \<union> set bs. x \<in> \<Union> closure a)
  \<and> infs (\<Union> closure a) (x ## xs)"
  if assms: "Steps (a\<^sub>0 # as @ a # bs @ [a])" "P2 a"
proof -
  from Steps_Union[OF assms(1) HOL.refl] guess as1 by safe
  note as1 = this
  from as1(2) have "as1 = map closure (as @ a # bs @ [a])" unfolding list_all2_op_map_iff ..
  from
    post_defs.Steps.steps_decomp[of "closure a\<^sub>0 # map closure as" "map closure (a # bs @ [a])"]
    as1(1)[unfolded this]
  have *:
    "post_defs.Steps (closure a\<^sub>0 # map closure as)"
    "post_defs.Steps (closure a # map closure bs @ [closure a])"
    "A2' (closure (last (a\<^sub>0 # as))) (closure a)"
    by (simp split: if_split_asm add: last_map)+
  then obtain bs1 where bs1:
    "post_defs.Steps (closure a # bs1 @ [closure a])"
    "list_all2 (\<lambda>x a. a = closure x) (a # bs @ [a]) (closure a # bs1 @ [closure a])"
    unfolding list_all2_op_map_iff by auto
  from post.Steps_steps_cycle[OF this(1) closure_finite closure_non_empty[OF \<open>P2 a\<close>]] guess a1 as1
    by safe
  note as1 = this
  with post.poststable[OF *(3)] obtain a2 where "a2 \<in> closure (last (a\<^sub>0 # as))" "A1 a2 a1"
    by auto
  with post.Steps_poststable[OF *(1), of a2] obtain as2 where as2:
    "pre_defs.Steps as2" "list_all2 op \<in> as2 (closure a\<^sub>0 # map closure as)" "last as2 = a2"
    by (auto split: if_split_asm simp: last_map)
  from as2(2) have "hd as2 \<in> closure a\<^sub>0" by (cases as2) auto
  then have "hd as2 \<noteq> {}" unfolding closure_def by auto
  then obtain x\<^sub>0 where "x\<^sub>0 \<in> hd as2" by auto
  from pre.Steps_prestable[OF as2(1) \<open>x\<^sub>0 \<in> _\<close>] obtain xs where xs:
    "steps (x\<^sub>0 # xs)" "list_all2 op \<in> (x\<^sub>0 # xs) as2"
    by auto
  with \<open>last as2 = a2\<close> have "last (x\<^sub>0 # xs) \<in> a2"
    unfolding list_all2_Cons1 by (auto intro: list_all2_last)
  with pre.prestable[OF \<open>A1 a2 a1\<close>] obtain y where "C (last (x\<^sub>0 # xs)) y" "y \<in> a1" by auto
  from pre.Steps_run_cycle_buechi'[OF as1(1) \<open>y \<in> a1\<close>] obtain ys where ys:
    "run (y ## ys)" "\<forall>x\<in>sset ys. \<exists>a\<in>set as1 \<union> {a1}. x \<in> a" "infs a1 (y ## ys)"
    by auto
  from ys(3) \<open>a1 \<in> closure a\<close> have "infs (\<Union> closure a) (y ## ys)"
    by (auto simp: HLD_iff elim!: alw_ev_mono)
  from extend_run[OF xs(1) \<open>C _ _\<close> \<open>run (y ## ys)\<close>] have "run ((x\<^sub>0 # xs) @- y ## ys)" by simp
  then show ?thesis
    apply (inst_existentials x\<^sub>0 "xs @- y ## ys")
      apply (simp; fail)
    using \<open>x\<^sub>0 \<in> _\<close> \<open>hd as2 \<in> _\<close> apply (auto; fail)
    using xs(2) as2(2) bs1(2) \<open>y \<in> a1\<close> \<open>a1 \<in> _\<close> ys(2) as1(2)
    unfolding list_all2_op_map_iff list_all2_Cons1 list_all2_Cons2
      apply auto
       apply (fastforce dest!: list_all2_set1)
     apply blast
    using \<open>infs (\<Union> closure a) (y ## ys)\<close>
    by (simp add: sdrop_shift)
qed

end (* Double Simulation Graph *)


section \<open>Finite Graphs\<close>

locale Finite_Graph = Graph_Defs +
  fixes x\<^sub>0
  assumes finite_reachable: "finite {x. E\<^sup>*\<^sup>* x\<^sub>0 x}"
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
  shows "\<exists> x ys zs. steps (x\<^sub>0 # ys @ x # zs @ [x]) \<and> set ys \<union> set zs \<subseteq> {x\<^sub>0} \<union> sset xs"
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
    by (inst_existentials "hd zs" ys "tl zs") (auto dest: list.set_sel(2))
qed

(* XXX Duplication *)
lemma buechi_run_finite_state_set_cycle_steps:
  assumes "run (x\<^sub>0 ## xs)" "alw (ev (holds \<phi>)) (x\<^sub>0 ## xs)"
  shows
  "\<exists> x ys zs.
    steps (x\<^sub>0 # ys @ x # zs @ [x]) \<and> set ys \<union> set zs \<subseteq> {x\<^sub>0} \<union> sset xs \<and> (\<exists> y \<in> set (x # zs). \<phi> y)"
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
    by (inst_existentials "hd zs" ys "tl zs") (auto dest: list.set_sel(2))
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

locale Simulation_Graph_Complete_Defs =
  Simulation_Graph_Defs C A for C :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and A :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" +
  fixes P :: "'a set \<Rightarrow> bool" -- "well-formed abstractions"

locale Simulation_Graph_Complete = Simulation_Graph_Complete_Defs +
  assumes complete: "C x y \<Longrightarrow> P S \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists> T. A S T \<and> y \<in> T"
      and P_invariant: "P S \<Longrightarrow> A S T \<Longrightarrow> P T"
begin

lemma steps_complete:
  "\<exists> as. Steps (a # as) \<and> list_all2 (op \<in>) xs as" if "steps (x # xs)" "x \<in> a" "P a"
  using that
  by (induction xs arbitrary: x a) (erule steps.cases; fastforce dest!: complete intro: P_invariant)+

lemma abstract_run_Run:
  "Run (abstract_run a xs)" if "run (x ## xs)" "x \<in> a" "P a"
  using that
proof (coinduction arbitrary: a x xs)
  case (run a x xs)
  obtain y ys where "xs = y ## ys" by (metis stream.collapse)
  with run have "C x y" "run (y ## ys)" by (auto elim: run.cases)
  from complete[OF \<open>C x y\<close> \<open>P a\<close> \<open>x \<in> a\<close>] obtain b where "A a b \<and> y \<in> b" by auto
  then have "A a (SOME b. A a b \<and> y \<in> b) \<and> y \<in> (SOME b. A a b \<and> y \<in> b)" by (rule someI)
  moreover with \<open>P a\<close> have "P (SOME b. A a b \<and> y \<in> b)" by (blast intro: P_invariant)
  ultimately show ?case using \<open>run (y ## ys)\<close> unfolding \<open>xs = _\<close>
    apply (subst abstract_run_ctr, simp)
    apply (subst abstract_run_ctr, simp)
    by (auto simp: abstract_run_ctr[symmetric])
qed

lemma abstract_run_abstract:
  "stream_all2 (op \<in>) (x ## xs) (abstract_run a xs)" if "run (x ## xs)" "x \<in> a" "P a"
using that proof (coinduction arbitrary: a x xs)
  case run: (stream_rel x' u b' v a x xs)
  obtain y ys where "xs = y ## ys" by (metis stream.collapse)
  with run have "C x y" "run (y ## ys)" by (auto elim: run.cases)
  from complete[OF \<open>C x y\<close> \<open>P a\<close> \<open>x \<in> a\<close>] obtain b where "A a b \<and> y \<in> b" by auto
  then have "A a (SOME b. A a b \<and> y \<in> b) \<and> y \<in> (SOME b. A a b \<and> y \<in> b)" by (rule someI)
  with \<open>run (y ## ys)\<close> \<open>x \<in> a\<close> \<open>P a\<close> run(1,2) \<open>xs = _\<close> show ?case
    by (subst (asm) abstract_run_ctr) (auto intro: P_invariant)
qed

lemma run_complete:
  "\<exists> as. Run (a ## as) \<and> stream_all2 (op \<in>) xs as" if "run (x ## xs)" "x \<in> a" "P a"
  using abstract_run_Run[OF that] abstract_run_abstract[OF that]
  apply (subst (asm) abstract_run_ctr)
  apply (subst (asm) (2) abstract_run_ctr)
  by auto

end (* Simulation Graph Complete Abstraction *)


subsection \<open>Runs in Finite Complete Graphs\<close>

locale Simulation_Graph_Finite_Complete = Simulation_Graph_Complete +
  fixes a\<^sub>0
  assumes finite_abstract_reachable: "finite {a. A\<^sup>*\<^sup>* a\<^sub>0 a}"
begin

sublocale Steps_finite: Finite_Graph A a\<^sub>0
  by standard (rule finite_abstract_reachable)

lemma run_finite_state_set_cycle_steps:
  assumes "run (x\<^sub>0 ## xs)" "x\<^sub>0 \<in> a\<^sub>0" "P a\<^sub>0"
  shows "\<exists> x ys zs.
    Steps (a\<^sub>0 # ys @ x # zs @ [x]) \<and> (\<forall> a \<in> set ys \<union> set zs. \<exists> x \<in> {x\<^sub>0} \<union> sset xs. x \<in> a)"
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
    \<and> (\<forall> a \<in> set ys \<union> set zs. \<exists> x \<in> {x\<^sub>0} \<union> sset xs. x \<in> a)
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

end (* Simulation Graph Finite Complete Abstraction *)


section \<open>Finite Complete Double Simulations\<close>

locale Double_Simulation_Finite_Complete = Double_Simulation +
  fixes a\<^sub>0
  assumes complete: "C x y \<Longrightarrow> x \<in> S \<Longrightarrow> P2 S \<Longrightarrow> \<exists> T. A2 S T \<and> y \<in> T"
  assumes finite_abstract_reachable: "finite {a. A2\<^sup>*\<^sup>* a\<^sub>0 a}"
  assumes P2_invariant: "P2 a \<Longrightarrow> A2 a a' \<Longrightarrow> P2 a'"
      and P2_a\<^sub>0: "P2 a\<^sub>0"
begin

sublocale Simulation_Graph_Finite_Complete C A2 P2 a\<^sub>0
  by standard (blast intro: complete finite_abstract_reachable P2_invariant)+

lemma P2_invariant_Steps:
  "list_all P2 as" if "Steps (a\<^sub>0 # as)"
  using that P2_a\<^sub>0 by (induction "a\<^sub>0 # as" arbitrary: as a\<^sub>0) (auto intro: P2_invariant)

theorem infinite_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs)) \<longleftrightarrow> (\<exists> as a bs. Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "\<Union>closure a\<^sub>0 = a\<^sub>0" "P2 a\<^sub>0"
proof (safe, goal_cases)
  case (1 x\<^sub>0 xs)
  from run_finite_state_set_cycle_steps[OF this(2,1)] that(2) show ?case by auto
next
  case prems: (2 as a bs)
  with Steps.steps_decomp[of "a\<^sub>0 # as @ [a]" "bs @ [a]"] have "Steps (a\<^sub>0 # as @ [a])" by auto
  from P2_invariant_Steps[OF this] have "P2 a" by auto
  from Steps_run_cycle''[OF prems this] that show ?case by auto
qed

context
  fixes \<phi> :: "'a \<Rightarrow> bool" -- "The property we want to check"
  assumes \<phi>_closure_compatible: "x \<in> a \<Longrightarrow> \<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union> closure a. \<phi> x)"
begin

theorem infinite_buechi_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as a bs. Steps (a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall> x \<in> \<Union> closure a. \<phi> x))"
  if "\<Union>closure a\<^sub>0 = a\<^sub>0"
proof (safe, goal_cases)
  case (1 x\<^sub>0 xs)
  from buechi_run_finite_state_set_cycle_steps[OF this(2,1) P2_a\<^sub>0, of \<phi>] this(3) guess a ys zs
    by clarsimp
  note guessed = this(2-)
  from guessed(3) show ?case
  proof (standard, goal_cases)
    case 1
    then obtain x where "x \<in> a" "\<phi> x" by auto
    with \<phi>_closure_compatible have "\<forall> x \<in> \<Union> closure a. \<phi> x" by blast
    with guessed(1,2) show ?case by auto
  next
    case 2
    then obtain b x where "x \<in> b" "b \<in> set zs" "\<phi> x" by auto
    with \<phi>_closure_compatible have *: "\<forall> x \<in> \<Union> closure b. \<phi> x" by blast
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
      unfolding HLD_iff by (inst_existentials x xs) (auto intro: alw_ev_mono) (* Slow *)
    done
qed

end

end (* Double Simulation Finite Complete Abstraction *)


section \<open>Encoding of Properties in Runs\<close>

locale Double_Simulation_Finite_Complete_Abstraction_Prop =
  Double_Simulation +
  fixes a\<^sub>0
  fixes \<phi> :: "'a \<Rightarrow> bool" -- "The property we want to check"
  assumes complete: "C x y \<Longrightarrow> x \<in> S \<Longrightarrow> \<exists> T. A2 S T \<and> y \<in> T"
  assumes finite_P2: "finite {a. P2 a}"
  assumes P2_invariant: "P2 a \<Longrightarrow> A2 a a' \<Longrightarrow> P2 a'"
      and P2_a\<^sub>0: "P2 a\<^sub>0"
  assumes \<phi>_A1_compatible: "A1 a b \<Longrightarrow> b \<subseteq> {x. \<phi> x} \<or> b \<inter> {x. \<phi> x} = {}"
      and \<phi>_P2_compatible: "P2 a \<Longrightarrow> P2 (a \<inter> {x. \<phi> x})"
begin

definition "C_\<phi> x y \<equiv> C x y \<and> \<phi> y"
definition "A1_\<phi> a b \<equiv> A1 a b \<and> b \<subseteq> {x. \<phi> x}"
definition "A2_\<phi> S S' \<equiv> \<exists> S''. A2 S S'' \<and> S'' \<inter> {x. \<phi> x} = S'"

lemma A2_\<phi>_P2_invariant:
  "P2 a" if "A2_\<phi>\<^sup>*\<^sup>* a\<^sub>0 a"
  using that by induction (auto intro: \<phi>_P2_compatible P2_invariant P2_a\<^sub>0 simp: A2_\<phi>_def)

sublocale phi: Double_Simulation_Finite_Complete C_\<phi> A1_\<phi> P1 A2_\<phi> P2 a\<^sub>0
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
  case 7
  have "{a. A2_\<phi>\<^sup>*\<^sup>* a\<^sub>0 a} \<subseteq> {a. P2 a}"
    by (blast intro: A2_\<phi>_P2_invariant)
  then show ?case (is "finite ?S") using finite_P2 by (rule finite_subset)
next
  case (8 a a')
  then show ?case unfolding A2_\<phi>_def by (auto intro: P2_invariant \<phi>_P2_compatible)
next
  case 9
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

corollary infinite_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> run (x\<^sub>0 ## xs) \<and> pred_stream \<phi> (x\<^sub>0 ## xs)) \<longleftrightarrow>
   (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "\<Union>closure a\<^sub>0 = a\<^sub>0" "P2 a\<^sub>0" "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding phi.infinite_run_cycle_iff[OF that(1,2), symmetric] phi_run_iff[symmetric]
  using that(3) by auto

theorem Alw_ev_mc:
  "(\<forall> x\<^sub>0 \<in> a\<^sub>0. Alw_ev (Not o \<phi>) x\<^sub>0) \<longleftrightarrow> \<not> (\<exists> as a bs. phi.Steps (a\<^sub>0 # as @ a # bs @ [a]))"
  if "\<Union>closure a\<^sub>0 = a\<^sub>0" "P2 a\<^sub>0" "a\<^sub>0 \<subseteq> {x. \<phi> x}"
  unfolding Alw_ev alw_holds_pred_stream_iff infinite_run_cycle_iff[OF that, symmetric]
  by (auto simp: comp_def)

end

section \<open>Instantiation of Simulation Locales\<close>

subsection \<open>Additional Lemmas on Regions\<close>

context AlphaClosure
begin

context
  fixes l l' :: 's and A :: "('a, 'c, t, 's) ta"
  assumes valid_abstraction: "valid_abstraction A X k"
begin

interpretation alpha: AlphaClosure_global _ "k l" "\<R> l" by standard (rule finite)
lemma [simp]: "alpha.cla = cla l" unfolding alpha.cla_def cla_def ..

interpretation alpha': AlphaClosure_global _ "k l'" "\<R> l'" by standard (rule finite)
lemma [simp]: "alpha'.cla = cla l'" unfolding alpha'.cla_def cla_def ..

lemma regions_poststable':
  assumes
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle>" "Z \<subseteq> V" "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}"
  shows "\<exists> R \<in> \<R> l. A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',R'\<rangle> \<and> R \<inter> Z \<noteq> {}"
using assms proof (induction A \<equiv> A l \<equiv> l _ _ l' \<equiv> l' _rule: step_z.induct)
  case A: (step_t_z Z)
  from \<open>R' \<inter> (Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}) \<noteq> {}\<close> obtain u d where u:
    "u \<in> Z" "u \<oplus> d \<in> R'" "u \<oplus> d \<turnstile> inv_of A l" "0 \<le> d"
    unfolding zone_delay_def by blast+
  with alpha.closure_subs[OF A(2)] obtain R where R1: "u \<in> R" "R \<in> \<R> l"
    by (simp add: cla_def) blast
  from \<open>Z \<subseteq> V\<close> \<open>u \<in> Z\<close> have "\<forall>x\<in>X. 0 \<le> u x" unfolding V_def by fastforce
  from region_cover'[OF this] have R: "[u]\<^sub>l \<in> \<R> l" "u \<in> [u]\<^sub>l" by auto
  from SuccI2[OF \<R>_def' this(2,1) \<open>0 \<le> d\<close> HOL.refl] u(2) have v'1:
    "[u \<oplus> d]\<^sub>l \<in> Succ (\<R> l) ([u]\<^sub>l)" "[u \<oplus> d]\<^sub>l \<in> \<R> l"
    by auto
  from alpha.regions_closed'_spec[OF R(1,2) \<open>0 \<le> d\<close>] have v'2: "u \<oplus> d \<in> [u \<oplus> d]\<^sub>l" by simp
  from valid_abstraction have
    "\<forall>(x, m)\<in>clkp_set A l. m \<le> real (k l x) \<and> x \<in> X \<and> m \<in> \<nat>"
    by (auto elim!: valid_abstraction.cases)
  then have
    "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k l x) \<and> x \<in> X \<and> m \<in> \<nat>"
    unfolding clkp_set_def collect_clki_def inv_of_def by fastforce
  from ccompatible[OF this, folded \<R>_def'] v'1(2) v'2 u(2,3) have
    "[u \<oplus> d]\<^sub>l \<subseteq> \<lbrace>inv_of A l\<rbrace>"
    unfolding ccompatible_def ccval_def by auto
  from
    alpha.valid_regions_distinct_spec[OF v'1(2) _ v'2 \<open>u \<oplus> d \<in> R'\<close>] \<open>R' \<in> _\<close> \<open>l = l'\<close>
    alpha.region_unique_spec[OF R1]
  have "[u \<oplus> d]\<^sub>l = R'" "[u]\<^sub>l = R" by auto
  from valid_abstraction \<open>R \<in> _\<close> \<open>_ \<in> Succ (\<R> l) _\<close> \<open>_ \<subseteq> \<lbrace>inv_of A l\<rbrace>\<close> have
    "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l, R'\<rangle>"
    by (auto simp: comp_def \<open>[u \<oplus> d]\<^sub>l = R'\<close> \<open>_ = R\<close>)
  with \<open>l = l'\<close> \<open>R \<in> _\<close> \<open>u \<in> R\<close> \<open>u \<in> Z\<close> show ?case by - (rule bexI[where x = R]; auto)
next
  case A: (step_a_z g a r Z)
  from A(4) obtain u v' where
    "u \<in> Z" and v': "v' = [r\<rightarrow>0]u" "u \<turnstile> g" "v' \<turnstile> inv_of A l'" "v' \<in> R'"
    unfolding zone_set_def by blast
  from \<open>u \<in> Z\<close> alpha.closure_subs[OF A(2)] A(1) obtain u' R where u':
    "u \<in> R" "u' \<in> R" "R \<in> \<R> l"
    by (simp add: cla_def) blast
  then have "\<forall>x\<in>X. 0 \<le> u x" unfolding \<R>_def by fastforce
  from region_cover'[OF this] have "[u]\<^sub>l \<in> \<R> l" "u \<in> [u]\<^sub>l" by auto
  have *:
    "[u]\<^sub>l \<subseteq> \<lbrace>g\<rbrace>" "region_set' ([u]\<^sub>l) r 0 \<subseteq> [[r\<rightarrow>0]u]\<^sub>l'"
    "[[r\<rightarrow>0]u]\<^sub>l' \<in> \<R> l'" "[[r\<rightarrow>0]u]\<^sub>l' \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
  proof -
    from valid_abstraction have "collect_clkvt (trans_of A) \<subseteq> X"
      "\<forall> l g a r l' c. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> c \<notin> set r \<longrightarrow> k l' c \<le> k l c"
      by (auto elim: valid_abstraction.cases)
    with A(1) have "set r \<subseteq> X" "\<forall>y. y \<notin> set r \<longrightarrow> k l' y \<le> k l y"
      unfolding collect_clkvt_def by (auto 4 8)
    with
      region_set_subs[
        of _ X "k l" _ 0, where k' = "k l'", folded \<R>_def, OF \<open>[u]\<^sub>l \<in> \<R> l\<close> \<open>u \<in> [u]\<^sub>l\<close> finite
        ]
    show "region_set' ([u]\<^sub>l) r 0 \<subseteq> [[r\<rightarrow>0]u]\<^sub>l'" "[[r\<rightarrow>0]u]\<^sub>l' \<in> \<R> l'" by auto
    from valid_abstraction have *:
      "\<forall>l. \<forall>(x, m)\<in>clkp_set A l. m \<le> real (k l x) \<and> x \<in> X \<and> m \<in> \<nat>"
      by (fastforce elim: valid_abstraction.cases)+
    with A(1) have "\<forall>(x, m)\<in>collect_clock_pairs g. m \<le> real (k l x) \<and> x \<in> X \<and> m \<in> \<nat>"
      unfolding clkp_set_def collect_clkt_def by fastforce
    from \<open>u \<in> [u]\<^sub>l\<close> \<open>[u]\<^sub>l \<in> \<R> l\<close> ccompatible[OF this, folded \<R>_def] \<open>u \<turnstile> g\<close> show "[u]\<^sub>l \<subseteq> \<lbrace>g\<rbrace>"
      unfolding ccompatible_def ccval_def by blast
    have **: "[r\<rightarrow>0]u \<in> [[r\<rightarrow>0]u]\<^sub>l'"
      using \<open>R' \<in> \<R> l'\<close> \<open>v' \<in> R'\<close> alpha'.region_unique_spec v'(1) by blast
    from * have
      "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l'). m \<le> real (k l' x) \<and> x \<in> X \<and> m \<in> \<nat>"
      unfolding inv_of_def clkp_set_def collect_clki_def by fastforce
    from ** \<open>[[r\<rightarrow>0]u]\<^sub>l' \<in> \<R> l'\<close> ccompatible[OF this, folded \<R>_def] \<open>v' \<turnstile> _\<close> show
      "[[r\<rightarrow>0]u]\<^sub>l' \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
      unfolding ccompatible_def ccval_def \<open>v' = _\<close> by blast
  qed
  from * \<open>v' = _\<close> \<open>u \<in> [u]\<^sub>l\<close> have "v' \<in> [[r\<rightarrow>0]u]\<^sub>l'" unfolding region_set'_def by auto
  from alpha'.valid_regions_distinct_spec[OF *(3) \<open>R' \<in> \<R> l'\<close> \<open>v' \<in> [[r\<rightarrow>0]u]\<^sub>l'\<close> \<open>v' \<in> R'\<close>]
  have "[[r\<rightarrow>0]u]\<^sub>l' = R'" .
  from alpha.region_unique_spec[OF u'(1,3)] have "[u]\<^sub>l = R" by auto
  from A valid_abstraction \<open>R \<in> _\<close> * have "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', R'\<rangle>"
    by (auto simp: comp_def \<open>_ = R'\<close> \<open>_ = R\<close>)
  with \<open>R \<in> _\<close> \<open>u \<in> R\<close> \<open>u \<in> Z\<close> show ?case by - (rule bexI[where x = R]; auto)
qed

end (* End of context for fixed locations *)


text \<open>
  Poststability of Closures:
  For every transition in the zone graph and each region in the closure of the resulting zone,
  there exists a similar transition in the region graph.
\<close>
lemma regions_poststable:
  assumes valid_abstraction: "valid_abstraction A X k"
  and A:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l',Z'\<rangle>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'',Z''\<rangle>"
    "Z \<subseteq> V" "R'' \<in> \<R> l''" "R'' \<inter> Z'' \<noteq> {}"
  shows "\<exists> R \<in> \<R> l. A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^sub>a \<langle>l'',R''\<rangle> \<and> R \<inter> Z \<noteq> {}"
proof -
  from A(1) \<open>Z \<subseteq> V\<close> have "Z' \<subseteq> V" by (rule step_z_V)
  from A(1) have [simp]: "l' = l" by auto
  from regions_poststable'[OF valid_abstraction A(2) \<open>Z' \<subseteq> V\<close> \<open>R'' \<in> _\<close> \<open>R'' \<inter> Z'' \<noteq> {}\<close>] obtain R'
    where R': "R'\<in>\<R> l'" "A,\<R> \<turnstile> \<langle>l', R'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', R''\<rangle>" "R' \<inter> Z' \<noteq> {}"
    by auto
  from regions_poststable'[OF valid_abstraction A(1) \<open>Z \<subseteq> V\<close> R'(1,3)] obtain R where
    "R \<in> \<R> l" "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l, R'\<rangle>" "R \<inter> Z \<noteq> {}"
    by auto
  with R'(2) show ?thesis by - (rule bexI[where x = "R"]; auto intro: step_r'.intros)
qed

lemma closure_regions_poststable:
  assumes valid_abstraction: "valid_abstraction A X k"
  and A:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l',Z'\<rangle>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<alpha>(\<upharpoonleft>a)\<^esub> \<langle>l'',Z''\<rangle>"
    "Z \<subseteq> V" "R'' \<in> \<R> l''" "R'' \<subseteq> Z''"
  shows "\<exists> R \<in> \<R> l. A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^sub>a \<langle>l'',R''\<rangle> \<and> R \<inter> Z \<noteq> {}"
  using A(2) regions_poststable[OF valid_abstraction A(1) _ A(3,4)] A(4,5)
  apply cases
  unfolding cla_def
  apply auto
    oops



end (* End of Alpha Closure *)

context Regions
begin

inductive step_z_beta' ::
  "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<beta>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l'', Z''\<rangle>" if
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<beta>(\<upharpoonleft>a)\<^esub> \<langle>l'', Z''\<rangle>"

lemma closure_parts_mono:
  "{R \<in> \<R> l. R \<inter> Z \<noteq> {}} \<subseteq> {R \<in> \<R> l. R \<inter> Z' \<noteq> {}}" if
  "Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z \<subseteq> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z'"
proof (clarify, goal_cases)
  case prems: (1 R)
  with that have "R \<subseteq> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z'"
    unfolding cla_def by auto
  from \<open>_ \<noteq> {}\<close> obtain u where "u \<in> R" "u \<in> Z" by auto
  with \<open>R \<subseteq> _\<close> obtain R' where "R' \<in> \<R> l" "u \<in> R'" "R' \<inter> Z' \<noteq> {}" unfolding cla_def by force
  from \<R>_regions_distinct[OF \<R>_def' this(1,2) \<open>R \<in> _\<close>] \<open>u \<in> R\<close> have "R = R'" by auto
  with \<open>R' \<inter> Z' \<noteq> {}\<close> \<open>R \<inter> Z' = {}\<close> show ?case by simp
qed

lemma closure_parts_id:
  "{R \<in> \<R> l. R \<inter> Z \<noteq> {}} = {R \<in> \<R> l. R \<inter> Z' \<noteq> {}}" if
  "Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z = Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z'"
  using closure_parts_mono that by blast

(* XXX All of these should be considered for moving into the locales for global sets of regions *)
context
  fixes l' :: 's and A :: "('a, 'c, t, 's) ta"
  assumes valid_abstraction: "valid_abstraction A X k"
begin

interpretation regions: Regions_global _ _ _ "k l'"
  by standard (rule finite clock_numbering not_in_X non_empty)+

lemmas regions_poststable = regions_poststable[OF valid_abstraction]

lemma clkp_set_clkp_set1:
  "\<exists> l. (c, x) \<in> clkp_set A l" if "(c, x) \<in> Timed_Automata.clkp_set A"
  using that
  unfolding Timed_Automata.clkp_set_def Closure.clkp_set_def
  unfolding Timed_Automata.collect_clki_def Closure.collect_clki_def
  unfolding Timed_Automata.collect_clkt_def Closure.collect_clkt_def
  by fastforce

lemma clkp_set_clkp_set2:
  "(c, x) \<in> Timed_Automata.clkp_set A" if "(c, x) \<in> clkp_set A l" for l
  using that
  unfolding Timed_Automata.clkp_set_def Closure.clkp_set_def
  unfolding Timed_Automata.collect_clki_def Closure.collect_clki_def
  unfolding Timed_Automata.collect_clkt_def Closure.collect_clkt_def
  by fastforce

lemma clock_numbering_le: "\<forall>c\<in>clk_set A. v c \<le> n"
proof
  fix c assume "c \<in> clk_set A"
  then have "c \<in> X"
  proof (safe, clarsimp, goal_cases)
    case (1 x)
    then obtain l where "(c, x) \<in> clkp_set A l" by (auto dest: clkp_set_clkp_set1)
    with valid_abstraction show "c \<in> X" by (auto elim!: valid_abstraction.cases)
  next
    case 2
    with valid_abstraction show "c \<in> X" by (auto elim!: valid_abstraction.cases)
  qed
  with clock_numbering show "v c \<le> n" by auto
qed

lemma beta_alpha_step:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<alpha>(a)\<^esub> \<langle>l', Closure\<^sub>\<alpha>\<^sub>,\<^sub>l' Z'\<rangle>" if
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>" "Z \<in> V'"
proof -
  from that obtain Z1' where Z1': "Z' = Approx\<^sub>\<beta> l' Z1'" "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z1'\<rangle>"
    by (clarsimp elim!: step_z_beta.cases)
  with \<open>Z \<in> V'\<close> have "Z1' \<in> V'"
    using valid_abstraction clock_numbering_le by (auto intro: step_z_V')
  let ?alpha = "Closure\<^sub>\<alpha>\<^sub>,\<^sub>l' Z1'" and ?beta = "Closure\<^sub>\<alpha>\<^sub>,\<^sub>l' (Approx\<^sub>\<beta> l' Z1')"
  have "?beta \<subseteq> ?alpha"
    using regions.approx_\<beta>_closure_\<alpha>'[OF \<open>Z1' \<in> V'\<close>] regions.alpha_interp.closure_involutive
    by (auto 4 3 dest: regions.alpha_interp.cla_mono)
  moreover have "?alpha \<subseteq> ?beta"
    by (intro regions.alpha_interp.cla_mono[simplified] regions.beta_interp.apx_subset)
  ultimately have "?beta = ?alpha" ..
  with Z1' show ?thesis by auto
qed

lemma beta_alpha_region_step:
  "\<exists> R \<in> \<R> l. R \<inter> Z \<noteq> {} \<and> A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^sub>a \<langle>l', R'\<rangle>" if
  "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>" "Z \<in> V'" "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}"
proof -
  from that(1) obtain l'' Z'' where steps:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l'', Z''\<rangle>" "A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<beta>(\<upharpoonleft>a)\<^esub> \<langle>l', Z'\<rangle>"
    by (auto elim!: step_z_beta'.cases)
  with \<open>Z \<in> V'\<close> steps(1) have "Z'' \<in> V'"
    using valid_abstraction clock_numbering_le by (blast intro: step_z_V')
  from beta_alpha_step[OF steps(2) this] have "A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<alpha>\<upharpoonleft>a\<^esub> \<langle>l', Closure\<^sub>\<alpha>\<^sub>,\<^sub>l'(Z')\<rangle>" .
  from step_z_alpha.cases[OF this] obtain Z1 where Z1:
    "A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z1\<rangle>" "Closure\<^sub>\<alpha>\<^sub>,\<^sub>l'(Z') = Closure\<^sub>\<alpha>\<^sub>,\<^sub>l'(Z1)"
    by metis
  from closure_parts_id[OF this(2)] that(3,4) have "R' \<inter> Z1 \<noteq> {}" by blast
  from regions_poststable[OF steps(1) Z1(1) _ \<open>R' \<in> _\<close> this] \<open>Z \<in> V'\<close> show ?thesis
    by (auto dest: V'_V)
qed

lemma step_z_beta'_steps_z_beta:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>"
  using that by (blast elim: step_z_beta'.cases)

lemma step_z_beta'_V':
  "Z' \<in> V'" if "Z \<in> V'" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>"
  using that(2)
  by (blast intro:
      step_z_beta'_steps_z_beta steps_z_beta_V'[OF _ valid_abstraction clock_numbering_le that(1)]
      )

end (* End of context for fixed location *)

end (* End of Regions *)


subsection \<open>Instantiation of Double Simulation\<close>

definition state_set :: "('a, 'c, 'time, 's) ta \<Rightarrow> 's set" where
  "state_set A \<equiv> fst ` (fst A) \<union> (snd o snd o snd o snd) ` (fst A)"

lemma finite_trans_of_finite_state_set:
  "finite (state_set A)" if "finite (trans_of A)"
  using that unfolding state_set_def trans_of_def by auto

context Regions
begin

lemma step_z_beta'_state_set:
  "l' \<in> state_set A" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>"
  using that by (force elim!: step_z_beta'.cases simp: state_set_def trans_of_def)

context
  fixes l' :: 's
begin

interpretation regions: Regions_global _ _ _ "k l'"
  by standard (rule finite clock_numbering not_in_X non_empty)+

lemma apx_finite:
  "finite {Approx\<^sub>\<beta> l' Z | Z. Z \<subseteq> V}" (is "finite ?S")
proof -
  have "finite regions.\<R>\<^sub>\<beta>"
    by (simp add: regions.beta_interp.finite_\<R>)
  then have "finite {S. S \<subseteq> regions.\<R>\<^sub>\<beta>}"
    by auto
  then have "finite {\<Union> S | S. S \<subseteq> regions.\<R>\<^sub>\<beta>}"
    by auto
  moreover have "?S \<subseteq> {\<Union> S | S. S \<subseteq> regions.\<R>\<^sub>\<beta>}"
    by (auto dest!: regions.beta_interp.apx_in)
  ultimately show ?thesis by (rule finite_subset[rotated])
qed

lemmas apx_subset = regions.beta_interp.apx_subset

lemma step_z_beta'_empty:
  "Z' = {}" if "A \<turnstile>' \<langle>l, {}\<rangle> \<leadsto>\<^bsub>\<beta>a\<^esub> \<langle>l', Z'\<rangle>"
  using that
  by (auto
      elim!: step_z_beta'.cases step_z.cases
      simp: regions.beta_interp.apx_empty zone_delay_def zone_set_def
     )

end (* Global Set of Regions *)

end (* Regions *)


locale Regions_TA = Regions X _ _  k for X :: "'c set" and k :: "'s \<Rightarrow> 'c \<Rightarrow> nat" +
  fixes A :: "('a, 'c, t, 's) ta"
  assumes valid_abstraction: "valid_abstraction A X k"
    and finite_state_set: "finite (state_set A)"
begin

definition "R_of lR = snd ` lR"

definition "from_R l R = {(l, u) | u. u \<in> R}"

lemma from_R_fst:
  "\<forall>x\<in>from_R l R. fst x = l"
  unfolding from_R_def by auto

lemma R_of_from_R [simp]:
  "R_of (from_R l R) = R"
  unfolding R_of_def from_R_def image_def by auto

(* XXX Bundle this? *)
no_notation Regions_Beta.part ("[_]\<^sub>_" [61,61] 61)
notation part'' ("[_]\<^sub>_" [61,61] 61)

definition "C \<equiv> \<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"

definition
  "A1 \<equiv> \<lambda> lR lR'.
    \<exists> l l'. (\<forall> x \<in> lR. fst x = l) \<and> (\<forall> x \<in> lR'. fst x = l')
    \<and> (\<exists> a. A,\<R> \<turnstile> \<langle>l, R_of lR\<rangle> \<leadsto>\<^sub>a \<langle>l', R_of lR'\<rangle>)"

definition
  "A2 \<equiv> \<lambda> lZ lZ'. \<exists> l l'.
      (\<forall> x \<in> lZ. fst x = l) \<and> (\<forall> x \<in> lZ'. fst x = l') \<and> R_of lZ \<in> V' \<and> R_of lZ' \<noteq> {}
    \<and> (\<exists> a. A \<turnstile>' \<langle>l, R_of lZ\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', R_of lZ'\<rangle>)"

definition
  "P1 \<equiv> \<lambda> lR. \<exists> l. (\<forall> x \<in> lR. fst x = l) \<and> l \<in> state_set A \<and> R_of lR \<in> \<R> l"

definition
  "P2 \<equiv> \<lambda> lZ. (\<exists> l \<in> state_set A. \<forall> x \<in> lZ. fst x = l) \<and> R_of lZ \<in> V' \<and> R_of lZ \<noteq> {}"

lemmas sim_defs = C_def A1_def A2_def P1_def P2_def

sublocale sim: Double_Simulation
  C  -- "Concrete step relation"
  A1 -- "Step relation for the first abstraction layer"
  P1 -- "Valid states of the first abstraction layer"
  A2 -- "Step relation for the second abstraction layer"
  P2 -- "Valid states of the second abstraction layer"
proof (standard, goal_cases)
  case (1 S T)
  then show ?case
    unfolding sim_defs
    by (force dest!: bspec step_r'_sound simp: split_beta R_of_def elim!: step'.cases)
next
  case prems: (2 lR' lZ' lZ)
  from prems(1) guess l' unfolding sim_defs Double_Simulation_Defs.closure_def by clarsimp
  note l' = this
  from prems(2) guess l l2 a unfolding sim_defs by clarsimp
  note guessed = this
  with l' have [simp]: "l2 = l'" by auto
  note guessed = guessed[unfolded \<open>l2 = l'\<close>]
  from l'(1,2) guessed(2) have "R_of lR' \<inter> R_of lZ' \<noteq> {}"
    unfolding R_of_def by auto
  from beta_alpha_region_step[OF valid_abstraction, OF guessed(5) \<open>_ \<in> V'\<close> \<open>_ \<in> \<R> l'\<close> this] l'(1)
  obtain R where "R \<in> \<R> l" "R \<inter> R_of lZ \<noteq> {}" "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^sub>a \<langle>l', R_of lR'\<rangle>"
    by auto
  then show ?case
    unfolding Double_Simulation_Defs.closure_def sim_defs
    apply -
    apply (rule bexI[where x = "from_R l R"])
     apply (inst_existentials l l' a)
    subgoal
      by (rule from_R_fst)
    subgoal
      by (rule l')
    subgoal
      by simp
    subgoal
      apply safe
       apply (inst_existentials l)
         apply (rule from_R_fst; fail)
      subgoal
        apply (auto elim!: step_r'.cases)
        by (auto 4 4 intro!: bexI[rotated] simp: state_set_def trans_of_def image_def)
       apply (simp; fail)
      subgoal
        using guessed(1) by (auto 4 3 simp: from_R_def image_def R_of_def)
      done
    done
next
  case prems: (3 x y)
  from prems(1) guess lx unfolding P1_def by safe
  note lx = this
  from prems(2) guess ly unfolding P1_def by safe
  note ly = this
  show ?case
  proof (cases "lx = ly")
    case True
    have "R_of x \<noteq> R_of y"
    proof (rule ccontr, simp)
      assume A: "R_of x = R_of y"
      with lx(1) ly(1) \<open>lx = ly\<close> have "x = y"
        by - (rule prod_set_fst_id; auto simp: R_of_def)
      with \<open>x \<noteq> y\<close> show False ..
    qed
    from \<R>_regions_distinct[OF \<R>_def' \<open>R_of x \<in> _\<close> _ \<open>R_of y \<in> _\<close>[folded True] this] have
      "R_of x \<inter> R_of y = {}"
      by auto
    with lx ly \<open>lx = ly\<close> show ?thesis
      by (auto simp: R_of_def)
  next
    case False
    with lx ly show ?thesis by auto
  qed
next
  case 4
  have "finite (\<R> l)" for l
    unfolding \<R>_def by (intro finite_\<R> finite)
  have *: "finite {x. (\<forall> y \<in> x. fst y = l) \<and> R_of x \<in> \<R> l}" (is "finite ?S") for l
  proof -
    have "?S = (\<lambda> y. (\<lambda> x. (l, x)) ` y) ` \<R> l"
      unfolding R_of_def
      apply safe
      subgoal for x
        unfolding image_def by safe (erule bexI[rotated]; force)
      unfolding image_def by auto
    with \<open>finite _\<close> show ?thesis by auto
  qed
  have
    "{x. \<exists>l. (\<forall>x\<in>x. fst x = l) \<and> l \<in> state_set A \<and> R_of x \<in> \<R> l} =
    (\<Union> l \<in> state_set A. ({x. (\<forall> y \<in> x. fst y = l) \<and> R_of x \<in> \<R> l}))"
    by auto
  also have "finite \<dots>" by (blast intro: finite_state_set *)
  finally show ?case unfolding P1_def .
next
  case (5 a)
  then guess l unfolding sim_defs by clarsimp
  note l = this
  from \<open>R_of a \<noteq> {}\<close> obtain u where "u \<in> R_of a" by blast
  with region_cover'[of u] V'_V[OF \<open>_ \<in> V'\<close>] have "u \<in> [u]\<^sub>l" "[u]\<^sub>l \<in> \<R> l"
    unfolding V_def by auto
  with l(1,2) \<open>u \<in> R_of a\<close> show ?case
    by (inst_existentials "(\<lambda> x. (l, x)) ` ([u]\<^sub>l)" l) (force simp: sim_defs R_of_def image_def)+
qed

sublocale Graph_Defs "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}" .

lemmas step_z_beta'_V' = step_z_beta'_V'[OF valid_abstraction]

inductive
  steps_z_beta' :: "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  init: "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>" |
  step: "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>" if "A \<turnstile>' \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l'', Z''\<rangle>" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>"

lemma steps_sim_Steps:
  "sim.Steps (map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs))" if "steps ((l, Z) # xs)" "Z \<in> V'"
using that proof (induction "(l, Z) # xs" arbitrary: l Z xs)
  case Single
  then show ?case by (auto intro: Graph_Defs.steps.intros)
next
  case (Cons lZ' xs l Z)
  obtain l' Z' where [simp]: "lZ' = (l', Z')" by (metis prod.exhaust)
  from Cons have "Z' \<in> V'"
    by (auto intro: step_z_beta'_V')
  from Cons.prems Cons.hyps(1,2) Cons.hyps(3)[OF \<open>lZ' = _\<close>] show ?case
    apply simp
    apply (rule Graph_Defs.steps.intros)
    by (auto simp: from_R_fst sim_defs intro: step_z_beta'_V')
qed

lemma sim_Steps_steps:
  "steps ((l, Z) # xs)" if "sim.Steps (map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs))" "Z \<in> V'"
using that proof (induction "map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs)" arbitrary: l Z xs)
  case (Single x)
  then show ?case by (auto intro: Graph_Defs.steps.intros)
next
  case (Cons x y xs l Z xs')
  then obtain l' Z' ys where [simp]:
    "xs' = (l', Z') # ys" "x = from_R l Z" "y = from_R l' Z'"
    by (cases xs') auto
  with \<open>x # y # _ = _\<close> have "y # xs = map (\<lambda>(x, y). from_R x y) ((l', Z') # ys)" by simp
  from \<open>A2 x y\<close> obtain a where "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>a\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
      by atomize_elim (simp add: A2_def; auto dest: step_z_beta'_empty simp: from_R_def)
  moreover with Cons.prems step_z_beta'_V' have "Z' \<in> V'" by blast
  moreover from Cons.hyps(3)[OF \<open>y # xs = _\<close> \<open>Z' \<in> V'\<close>] have "steps ((l', Z') # ys)" .
  ultimately show ?case unfolding \<open>xs' = _\<close> by - (rule steps.intros; auto)
qed

lemma sim_steps_equiv:
  "steps ((l, Z) # xs) \<longleftrightarrow> sim.Steps (map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs))" if "Z \<in> V'"
  using that sim_Steps_steps steps_sim_Steps by fast

text \<open>
  Infinite runs in the simulation graph yield infinite concrete runs, which pass through the same
  closures. However, this lemma is not strong enough for Büchi runs.
\<close>
lemma beta_steps_run_cycle:
  assumes assms: "steps ((l, Z) # xs @ [(l, Z)])" "Z \<in> V'" "Z \<noteq> {}" "l \<in> state_set A"
  shows "\<exists> ys.
    sim.run ys \<and>
    (\<forall>x\<in>sset ys. \<exists> (l, Z) \<in> set xs \<union> {(l, Z)}. fst x = l \<and> snd x \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z) \<and>
    fst (shd ys) = l \<and> snd (shd ys) \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z"
proof -
  have steps: "sim.Steps (from_R l Z # map (\<lambda>(l, Z). from_R l Z) xs @ [from_R l Z])"
    using steps_sim_Steps[OF assms(1,2)] by simp
  from sim.Steps_run_cycle[OF this] obtain ys where ys:
    "sim.run ys"
    "\<forall>x\<in>sset ys. \<exists>a\<in>set (map (\<lambda>(l, Z). from_R l Z) xs) \<union> {from_R l Z}. x \<in> \<Union>sim.closure a"
    "shd ys \<in> \<Union>sim.closure (from_R l Z)"
    using assms(2-) by atomize_elim (auto simp: V'_def from_R_fst sim_defs)
  have *: "fst lu = l" "snd lu \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z" if "lu \<in> \<Union>sim.closure (from_R l Z)" for lu
    using that
      unfolding from_R_def sim_defs sim.closure_def Double_Simulation_Defs.closure_def
     apply safe
    subgoal
      by auto
    unfolding cla_def
    by auto (metis IntI R_of_def empty_iff fst_conv image_subset_iff order_refl snd_conv)
  from ys(3) have "fst (shd ys) = l" "snd (shd ys) \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z" by (auto 4 3 intro: *)
  moreover from ys(2) have
    "\<forall>x\<in>sset ys. \<exists> (l, Z) \<in> set xs \<union> {(l, Z)}. fst x = l \<and> snd x \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z"
    apply safe
    apply (drule bspec, assumption)
    apply safe
    unfolding set_map
     apply safe
    subgoal for a b aa X l2 Z2
      apply (rule bexI[where x = "(l2, Z2)"])
       apply safe
      subgoal
        by (auto 4 3 simp: from_R_def sim.closure_def Double_Simulation_Defs.closure_def sim_defs)
           (metis fst_conv)
      unfolding from_R_def sim.closure_def Double_Simulation_Defs.closure_def cla_def sim_defs
      by auto (metis IntI R_of_def empty_iff fst_conv image_subset_iff order_refl snd_conv)
    using * by force
  ultimately show ?thesis using \<open>sim.run ys\<close> by (inst_existentials ys) auto
qed

end (* Regions TA *)


context Regions_TA
begin

lemma sim_closure_from_R:
  "sim.closure (from_R l Z) = {from_R l Z' | Z'. l \<in> state_set A \<and> Z' \<in> \<R> l \<and> Z \<inter> Z' \<noteq> {}}"
  unfolding sim.closure_def
  unfolding from_R_def P1_def R_of_def
  apply auto
  subgoal premises prems for x l' u
  proof -
    from prems have [simp]: "l' = l" by auto
    from prems show ?thesis by force
  qed
  subgoal
    unfolding image_def by auto
  done

lemma from_R_loc:
  "l' = l" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

lemma from_R_val:
  "u \<in> Z" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

lemma from_R_R_of:
  "from_R l (R_of S) = S" if "\<forall> x \<in> S. fst x = l"
  using that unfolding from_R_def R_of_def by force

lemma run_map_from_R:
  "map (\<lambda>(x, y). from_R x y) (map (\<lambda> lR. ((THE l. \<forall> x \<in> lR. fst x = l), R_of lR)) xs) = xs"
  if "sim.Steps (x # xs)"
  using that
proof (induction "x # xs" arbitrary: x xs)
  case Single
  then show ?case by simp
next
  case (Cons x y xs)
  then show ?case
    apply (subst (asm) A2_def)
    apply simp
    apply clarify
    apply (rule from_R_R_of)
    apply (rule theI)
    unfolding R_of_def by force+
qed

end (* Regions TA *)



locale Regions_TA_Start_State = Regions_TA _ _ _ _ _ A for A :: "('a, 'c, t, 's) ta" +
  fixes l\<^sub>0 :: "'s" and Z\<^sub>0 :: "('c, t) zone"
  assumes start_state: "l\<^sub>0 \<in> state_set A" "Z\<^sub>0 \<in> V'" "Z\<^sub>0 \<noteq> {}"
begin

definition "a\<^sub>0 = from_R l\<^sub>0 Z\<^sub>0"

lemma step_z_beta'_complete:
  assumes "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" "u \<in> Z" "Z \<subseteq> V"
  shows "\<exists> Z' a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>a\<^esub> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
proof -
  from assms(1) obtain l'' u'' d a where steps:
    "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l'', u''\<rangle>" "A \<turnstile> \<langle>l'', u''\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>"
    by (force elim!: step'.cases)
  then obtain Z'' where
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l'', Z''\<rangle>" "u'' \<in> Z''"
    by (meson \<open>u \<in> Z\<close> step_t_z_complete)
  moreover with steps(2) obtain Z' where
    "A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z'\<rangle>" "u' \<in> Z'"
    by (meson \<open>u'' \<in> Z''\<close> step_a_z_complete)
  ultimately show ?thesis using \<open>Z \<subseteq> V\<close>
    by (inst_existentials "Approx\<^sub>\<beta> l' Z'" a)
       ((rule, assumption)+, (drule step_z_V, assumption)+, rule apx_subset)
qed

lemma R_ofI[intro]:
  "Z \<in> R_of S" if "(l, Z) \<in> S"
  using that unfolding R_of_def by force

lemma from_R_I[intro]:
  "(l', u') \<in> from_R l' Z'" if "u' \<in> Z'"
  using that unfolding from_R_def by auto

sublocale sim_complete: Double_Simulation_Finite_Complete
  C  -- "Concrete step relation"
  A1 -- "Step relation for the first abstraction layer"
  P1 -- "Valid states of the first abstraction layer"
  A2 -- "Step relation for the second abstraction layer"
  P2 -- "Valid states of the second abstraction layer"
  a\<^sub>0 -- "Start state"
proof (standard, goal_cases)
  case (1 x y S)
  -- Completeness
  then show ?case
    unfolding sim_defs
    apply clarsimp
    apply (drule step_z_beta'_complete[rotated 2, OF V'_V], assumption)
     apply force
    apply clarify
    subgoal for l u l' u' l'' Z'
      apply (inst_existentials "from_R l' Z'")
       apply (inst_existentials l)
      by (auto intro!: from_R_fst)
    done
next
  case 2
  -- Finiteness
  have "{a. A2\<^sup>*\<^sup>* a\<^sub>0 a} \<subseteq> {from_R l Z | l Z. l \<in> state_set A \<and> Z \<in> {Approx\<^sub>\<beta> l Z | Z. Z \<subseteq> V}} \<union> {a\<^sub>0}"
    apply clarsimp
    subgoal for x
    proof (induction a\<^sub>0 _ rule: rtranclp.induct)
      case rtrancl_refl
      then show ?case by simp
    next
      case prems: (rtrancl_into_rtrancl b c)
      have *: "\<exists>l Z. c = from_R l Z \<and> l \<in> state_set A \<and> (\<exists>Za. Z = Approx\<^sub>\<beta> l Za \<and> Za \<subseteq> V)"
        if "A2 b c" for b
        using that
        unfolding A2_def
        apply clarify
        subgoal for l l'
          apply (inst_existentials l' "R_of c")
            apply (simp add: from_R_R_of; fail)
           apply (rule step_z_beta'_state_set; assumption)
          by (auto dest!: V'_V step_z_V elim!: step_z_beta'.cases)
        done
      from prems show ?case
        by (cases "b = a\<^sub>0"; intro *)
    qed
    done
  also have "finite \<dots>" (is "finite ?S")
  proof -
    have "?S = {a\<^sub>0} \<union>
      (\<lambda> (l, Z). from_R l Z) ` \<Union> ((\<lambda> l. (\<lambda> Z. (l, Z)) ` {Approx\<^sub>\<beta> l Z | Z. Z \<subseteq> V}) ` (state_set A))"
      by auto
    also have "finite \<dots>"
      by (blast intro: apx_finite finite_state_set)
    finally show ?thesis .
  qed
  finally show ?case .
next
  case prems: (3 a a')
  -- \<open>Preservation of Well-Formedness\<close>
  with sim.P2_cover[OF prems(1)] show ?case
    unfolding sim_defs
    by (auto intro: step_z_beta'_state_set; auto dest!: step_z_beta'_V'[rotated] dest: V'_V)
next
  case 4
  from start_state show ?case unfolding a\<^sub>0_def by (auto simp: sim_defs from_R_fst)
qed

lemma (in Double_Simulation) P1_closure_id:
  "closure R = {R}" if "P1 R" "R \<noteq> {}"
  unfolding closure_def using that P1_distinct by blast

context
  fixes \<phi> :: "'s \<times> ('c \<Rightarrow> real) \<Rightarrow> bool" -- "The property we want to check"
  assumes \<phi>_closure_compatible: "x \<in> a \<Longrightarrow> \<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union> sim.closure a. \<phi> x)"
      and sim_closure: "\<Union>sim.closure a\<^sub>0 = a\<^sub>0"
begin

lemma infinite_buechi_run_cycle_iff':
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> sim.run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as a bs. sim.Steps (a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall> x \<in> \<Union> sim.closure a. \<phi> x))"
  using sim_complete.infinite_buechi_run_cycle_iff[OF \<phi>_closure_compatible, OF _ sim_closure] .

theorem infinite_buechi_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> sim.run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as l Z bs. steps ((l\<^sub>0, Z\<^sub>0) # as @ (l, Z) # bs @ [(l, Z)]) \<and> (\<forall> x \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z. \<phi> (l, x)))"
  unfolding infinite_buechi_run_cycle_iff' sim_steps_equiv[OF start_state(2)]
  apply (simp add: a\<^sub>0_def)
proof (safe, goal_cases)
  case prems: (1 as a bs)
  let ?l = "(THE l. \<forall>la\<in>a. fst la = l)"
  from prems(2) obtain a1 where "A2 a1 a"
    apply atomize_elim
    apply (cases as)
     apply (auto elim: sim.Steps_cases)
    by (metis append_Cons list.discI list.sel(1) sim.Steps.steps_decomp)
  then have "a \<noteq> {}" unfolding A2_def R_of_def by auto
  with \<open>A2 a1 a\<close> have "\<forall> x \<in> a. fst x = ?l"
    unfolding A2_def by - ((erule exE conjE)+, (rule theI; force))
  moreover with \<open>A2 a1 a\<close> \<open>a \<noteq> {}\<close> have "?l \<in> state_set A" unfolding A2_def
    by (fastforce intro: step_z_beta'_state_set)
  ultimately have "\<forall>x\<in>Closure\<^sub>\<alpha>\<^sub>,\<^sub>?l R_of a. \<phi> (?l, x)"
    unfolding cla_def
  proof (clarify, goal_cases)
    case prems2: (1 x X)
    then have P1_l_X: "P1 (from_R (THE l. \<forall>la\<in>a. fst la = l) X)"
      unfolding P1_def
      apply (inst_existentials ?l)
        apply (rule from_R_fst; fail)
      by (simp only: R_of_from_R; fail)+
    from prems prems2 show ?case
      unfolding sim.closure_def
      apply rotate_tac
      apply (drule bspec[where x = "from_R ?l X"])
      subgoal
        using P1_l_X
        apply clarify
        subgoal premises prems
        proof -
          from \<open>X \<inter> _ \<noteq> {}\<close> obtain l u where "u \<in> X" "(l, u) \<in> a"
            unfolding R_of_def from_R_def by auto
          moreover with prems have "l = ?l" by fastforce
          ultimately show ?thesis using prems(8) by auto
        qed
        done
      apply (subst \<phi>_closure_compatible[of _ "from_R ?l X"])
       apply blast
      by (subst sim.P1_closure_id; blast intro: P1_l_X)
  qed
  with prems(2) run_map_from_R[OF prems(2)] show ?case
    by (inst_existentials
        "map (\<lambda>lR. (THE l. \<forall>x\<in>lR. fst x = l, R_of lR)) as"
        ?l "R_of a"
        "map (\<lambda>lR. (THE l. \<forall>x\<in>lR. fst x = l, R_of lR)) bs"
        ) auto
next
  case (2 as l Z bs)
  then show ?case
    by (inst_existentials "map (\<lambda>(x, y). from_R x y) as")
       (force simp: sim_closure_from_R cla_def dest: from_R_loc from_R_val)
qed

end (* Context for Formula *)

end (* Regions TA with Start State*)

section \<open>Comments\<close>

text \<open>
\<^item> Pre-stability can easily be extended to infinite runs (see construction with \<open>sgenerate\<close> above)
\<^item> Post-stability can not
\<^item> Pre-stability + Completeness means that for every two concrete states in the same abstract class,
  there are equivalent runs
\<^item> Can offer representation view via suitable locale instantiations?
\<^item> Abstractions view?
\<^item> \<open>\<phi>\<close>-construction can be done on an automaton too (also for disjunctions)
\<^item> Büchi properties are nothing but \<open>\<box>\<diamond>\<close>-properties (@{term \<open>alw (ev \<phi>)\<close>}
\<close>

end (* Theory *)