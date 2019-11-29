theory Simulation_Graphs_Certification
  imports TA_Impl.Subsumption_Graphs TA.Simulation_Graphs
begin

section \<open>Certification Theorems Based on Subsumption and Simulation Graphs\<close>

subsection \<open>Misc\<close>

lemma finite_ImageI:
  assumes "finite S" "\<forall>a \<in> S. finite {b. (a, b) \<in> R}"
  shows "finite (R `` S)"
proof -
  have "R `` S \<subseteq> (\<Union> x \<in> S. {y. (x, y) \<in> R})"
    unfolding Image_def by auto
  also have "finite \<dots>"
    using assms by auto
  finally show ?thesis .
qed

lemma (in Graph_Defs) steps_two_iff[simp]:
  "steps [a, b] \<longleftrightarrow> E a b"
  by (auto elim!: steps.cases)

lemma (in Graph_Defs) steps_Cons_two_iff:
  "steps (a # b # as) \<longleftrightarrow> E a b \<and> steps (b # as)"
  by (auto elim: steps.cases)


subsection \<open>Certifying Cycle-Freeness in Graphs\<close>

locale Contract =
  fixes A B :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and G :: "'a \<Rightarrow> bool"
begin

definition "E a b \<equiv> A a b \<and> G a \<or> \<not> G a \<and> B a b \<and> G b"
definition "E' a b \<equiv> G a \<and> G b \<and> (A a b \<or> (\<exists> c. A a c \<and> \<not> G c \<and> B c b))"

sublocale E: Graph_Defs E .
sublocale E': Graph_Defs E' .

lemma steps_contract:
  assumes "E.steps (a # xs @ [b])" "G a" "G b"
  shows "\<exists>as. E'.steps (a # as @ [b])"
  using assms
proof (induction xs arbitrary: a rule: length_induct)
  case prems: (1 xs)
  show ?case
  proof (cases xs)
    case Nil
    with prems show ?thesis
      apply (inst_existentials "[] :: 'a list")
      apply (auto elim!: E.steps.cases)
      apply (auto simp: E_def E'_def)
      done
  next
    case (Cons y ys)
    with \<open>E.steps (a # xs @ [b])\<close> have "E a y" "E.steps (y # ys @ [b])"
      by (cases, auto)+
    from this(1) \<open>G a\<close> consider (graph) "A a y" "G a" "G y" | (non_graph) "A a y" "G a" "\<not> G y"
      unfolding E_def by auto
    then show ?thesis
    proof cases
      case graph
      with \<open>E.steps (y # ys @ [b])\<close> prems(1) \<open>G b\<close> obtain as where "E'.steps (y # as @ [b])"
        unfolding \<open>xs = _\<close> by auto
      also from graph have "E' a y"
        unfolding E'_def by auto
      finally (E'.steps.Cons[rotated]) show ?thesis
        by (inst_existentials "y # as") auto
    next
      case non_graph
      show ?thesis
      proof (cases ys)
        case Nil
        with \<open>E.steps (y # ys @ [b])\<close> have "E y b"
          by auto
        with \<open>\<not> G y\<close> have "B y b" "G b"
          unfolding E_def by auto
        with \<open>A a y\<close> \<open>G a\<close> \<open>\<not> G y\<close> have "E'.steps [a, b]"
          by (auto simp: E'_def)
        then show ?thesis
          by (inst_existentials "[] :: 'a list") auto
      next
        case (Cons z zs)
        with \<open>E.steps (y # ys @ [b])\<close> have "E y z" "E.steps (z # zs @ [b])"
          by (auto simp: E.steps_Cons_two_iff)
        with \<open>\<not> G y\<close> have "B y z" "G z"
          unfolding E_def by auto
        with \<open>A a y\<close> \<open>G a\<close> \<open>\<not> G y\<close> have "E' a z"
          by (auto simp: E'_def)
        also from \<open>E.steps (z # zs @ [b])\<close> prems(1) obtain as where "E'.steps (z # as @ [b])"
          unfolding \<open>xs = _\<close> \<open>ys = _\<close> using \<open>G z\<close> \<open>G b\<close> by force
        finally (E'.steps.Cons) show ?thesis
          by (inst_existentials "z # as") auto
      qed
    qed
  qed
qed

lemma E'_G[dest, intro]:
  assumes "E' x y"
  shows "G x" "G y"
  using assms unfolding E'_def by auto

lemma E'_steps_G:
  assumes "E'.steps (x # xs)" "xs \<noteq> []"
  shows "G x"
proof -
  from \<open>E'.steps _\<close> \<open>xs \<noteq> []\<close> obtain y where "E' x y"
    by (auto elim: E'.steps.cases)
  then show ?thesis
    by auto
qed

lemma E_E'_cycle:
  assumes "E\<^sup>+\<^sup>+ x x" "G x"
  shows "E'\<^sup>+\<^sup>+ x x"
proof -
  from \<open>E\<^sup>+\<^sup>+ x x\<close> obtain xs where "E.steps (x # xs @ [x])"
    including graph_automation by auto
  with \<open>G x\<close> obtain ys where "E'.steps (x # ys @ [x])"
    by (auto dest: steps_contract)
  then show ?thesis
    using E'.reaches1_steps_iff by blast
qed

text \<open>This can be proved by rotating the cycle if \<open>\<not> G x\<close>\<close>
lemma
  assumes "E\<^sup>*\<^sup>* s x" "E\<^sup>+\<^sup>+ x x" "G s"
  shows "E'\<^sup>*\<^sup>* s x \<and> E'\<^sup>+\<^sup>+ x x"
proof -
  show ?thesis
  proof (cases "G x")
    case True
    with \<open>E\<^sup>+\<^sup>+ x x\<close> have "E'\<^sup>+\<^sup>+ x x"
      by (auto dest: E_E'_cycle)
  from \<open>E\<^sup>*\<^sup>* s x\<close> consider (refl) "s = x" | (steps) "E\<^sup>+\<^sup>+ s x"
    by cases (auto simp: E.reaches1_reaches_iff2)
  then show ?thesis
  proof cases
    case refl
    with \<open>E'\<^sup>+\<^sup>+ x x\<close> show ?thesis
      by simp
  next
    case steps
    then obtain xs where "E.steps (s # xs @ [x])"
      including graph_automation by auto
    with \<open>G s\<close> \<open>G x\<close> obtain ys where "E'.steps (s # ys @ [x])"
      by (auto dest: steps_contract)
    with \<open>E'\<^sup>+\<^sup>+ x x\<close> show ?thesis
      including graph_automation by auto
  next
    oops

text \<open>Certifying cycle-freeness with a topological ordering of graph components\<close>
context
  fixes f :: "'a \<Rightarrow> nat" and F :: "'a \<Rightarrow> bool"
  assumes f_topo1: "\<forall>a b. G a \<and> A a b \<and> G b \<longrightarrow> (if F a then f a < f b else f a \<le> f b)"
      and f_topo2:
      "\<forall>a b c. G a \<and> A a b \<and> \<not> G b \<and> G c \<and> B b c \<longrightarrow> (if F a then f a < f c else f a \<le> f c)"
begin

lemma f_forward:
  assumes "E' a b"
  shows "f a \<le> f b"
  using assms f_topo1 f_topo2 unfolding E'_def by (cases "F a") (auto simp: less_imp_le)

lemma f_strict:
  assumes "E' a b" "F a"
  shows "f a < f b"
  using assms f_topo1 f_topo2 unfolding E'_def by (auto simp: less_imp_le)

text \<open>We do not even need this property any more.\<close>
lemma no_trivial_lasso:
  assumes "F a" "G a" "E' a a"
  shows False
  using assms f_topo1 f_topo2 unfolding E'_def by (meson less_irrefl)

lemma reaches_f_mono:
  assumes "E'\<^sup>*\<^sup>* a b"
  shows "f a \<le> f b"
  using assms by induction (auto intro: f_forward order.trans)

theorem no_accepting_cycle:
  assumes "E'\<^sup>+\<^sup>+ x x"
  shows "\<not> F x"
proof (rule ccontr, simp)
  assume "F x"
  from \<open>E'\<^sup>+\<^sup>+ x x\<close> obtain y where "E' x y" "E'\<^sup>*\<^sup>* y x"
    including graph_automation_aggressive by auto
  from \<open>E' x y\<close> \<open>F x\<close> have "f x < f y"
    by (rule f_strict)
  moreover from \<open>E'\<^sup>*\<^sup>* y x\<close> have "f y \<le> f x"
    by (rule reaches_f_mono)
  ultimately show False
    by simp
qed

end (* Context for 'topological' ordering *)

end (* Contract *)

locale Contract2 =
  fixes A B :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and G :: "'a \<Rightarrow> bool"
  fixes f :: "'a \<Rightarrow> nat" and F :: "'a \<Rightarrow> bool"
  assumes f_topo:
      "\<forall>a b c. G a \<and> A a b \<and> G c \<and> B b c \<longrightarrow> (if F a then f a < f c else f a \<le> f c)"
begin

definition "E a c \<equiv> \<exists>b. G a \<and> G c \<and> A a b \<and> B b c"

sublocale E: Graph_Defs E .

lemma f_forward:
  assumes "E a b"
  shows "f a \<le> f b"
  using assms f_topo unfolding E_def by (cases "F a") (auto simp: less_imp_le)

lemma f_strict:
  assumes "E a b" "F a"
  shows "f a < f b"
  using assms f_topo unfolding E_def by (auto simp: less_imp_le)

text \<open>We do not even need this property any more.\<close>
lemma no_trivial_lasso:
  assumes "F a" "G a" "E a a"
  shows False
  using assms f_topo unfolding E_def by (meson less_irrefl)

lemma reaches_f_mono:
  assumes "E\<^sup>*\<^sup>* a b"
  shows "f a \<le> f b"
  using assms by induction (auto intro: f_forward order.trans)

theorem no_accepting_cycle:
  assumes "E\<^sup>+\<^sup>+ x x"
  shows "\<not> F x"
proof (rule ccontr, simp)
  assume "F x"
  from \<open>E\<^sup>+\<^sup>+ x x\<close> obtain y where "E x y" "E\<^sup>*\<^sup>* y x"
    including graph_automation_aggressive by auto
  from \<open>E x y\<close> \<open>F x\<close> have "f x < f y"
    by (rule f_strict)
  moreover from \<open>E\<^sup>*\<^sup>* y x\<close> have "f y \<le> f x"
    by (rule reaches_f_mono)
  ultimately show False
    by simp
qed

end (* Contract *)


subsection \<open>Reachability and Over-approximation\<close>

context
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool"
    and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50) and less (infix "\<prec>" 50)
  assumes preorder: "class.preorder less_eq less"
  assumes mono: "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow> \<exists> b'. E b b' \<and> a' \<preceq> b'"
  assumes invariant: "P a \<Longrightarrow> E a a' \<Longrightarrow> P b"
begin

interpretation preorder less_eq less
  by (rule preorder)

interpretation Simulation_Invariant
  E "\<lambda> x y. \<exists> z. z \<preceq> y \<and> E x z \<and> P z" "(\<preceq>)" P P
  by standard (auto 0 4 intro: invariant dest: mono)

context
  fixes F :: "'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "F a \<Longrightarrow> a \<preceq> b \<Longrightarrow> F b"
begin

corollary reachability_correct:
  "\<nexists> s'. A.reaches a s' \<and> F s'" if "\<nexists> s'. B.reaches b s' \<and> F s'" "a \<preceq> b" "P a" "P b"
  using that by (auto dest!: simulation_reaches)

end (* Context for property *)

end (* Context for over-approximation *)


context Simulation_Invariant
begin

context
  fixes F :: "'a \<Rightarrow> bool" and F' :: "'b \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "F a \<Longrightarrow> a \<sim> b \<Longrightarrow> F' b"
begin

corollary reachability_correct:
  "\<nexists> s'. A.reaches a s' \<and> F s'" if "\<nexists> s'. B.reaches b s' \<and> F' s'" "a \<sim> b" "PA a" "PB b"
  using that by (auto dest!: simulation_reaches)

end (* Context for property *)

end (* Simulation Invariant *)


subsection \<open>Invariants for Un-reachability\<close>

locale Unreachability_Invariant = Subsumption_Graph_Pre_Defs + preorder less_eq less +
  fixes s\<^sub>0
  fixes S :: "'a set" and SE :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes mono:
    "s \<preceq> s' \<Longrightarrow> s \<rightarrow> t \<Longrightarrow> s \<in> S \<or> reaches s\<^sub>0 s \<Longrightarrow> s' \<in> S \<or> reaches s\<^sub>0 s'
  \<Longrightarrow> \<exists> t'. t \<preceq> t' \<and> s' \<rightarrow> t'"
  assumes S_E_subsumed: "s \<in> S \<Longrightarrow> s \<rightarrow> t \<Longrightarrow> \<exists> t' \<in> S. SE t t'"
  assumes subsumptions_subsume: "SE s t \<Longrightarrow> s \<preceq> t"
begin

lemma reachable_S_subsumed:
  "\<exists> s'. s' \<in> S \<and> s \<preceq> s'" if "s' \<in> S" "s\<^sub>0 \<preceq> s'" "reaches s\<^sub>0 s"
  supply [intro] = order_trans less_trans less_imp_le
  using that(3) apply induction
  subgoal
    using that(1,2) by blast
  apply clarify
  apply (drule mono)
  using S_E_subsumed subsumptions_subsume by blast+

definition E' where
  "E' s t \<equiv> \<exists>s'. E s s' \<and> SE s' t \<and> t \<in> S"

sublocale G: Graph_Defs E' .

context
  fixes s\<^sub>0'
  assumes "s\<^sub>0 \<preceq> s\<^sub>0'" "s\<^sub>0' \<in> S"
begin

interpretation Simulation_Invariant E E' "(\<preceq>)" "\<lambda>s. reaches s\<^sub>0 s" "\<lambda>x. x \<in> S"
proof standard
  fix a b a' :: \<open>'a\<close>
  assume \<open>a \<rightarrow> b\<close> \<open>s\<^sub>0 \<rightarrow>* a\<close> \<open>a' \<in> S\<close> \<open>a \<preceq> a'\<close>
  with mono[OF \<open>a \<preceq> a'\<close> \<open>a \<rightarrow> b\<close>] obtain b' where "b \<preceq> b'" "a' \<rightarrow> b'"
    by auto
  with S_E_subsumed[OF \<open>a' \<in> S\<close>] obtain c where "c \<in> S" "SE b' c"
    by auto
  with \<open>a' \<rightarrow> b'\<close> have "E' a' c"
    unfolding E'_def by auto
  with \<open>b \<preceq> b'\<close> \<open>SE b' c\<close> subsumptions_subsume show \<open>\<exists>b'. E' a' b' \<and> b \<preceq> b'\<close>
    by (blast intro: order_trans)
qed (auto simp: E'_def)

lemma run_subsumed:
  assumes "run (s\<^sub>0 ## xs)"
  obtains ys where "G.run (s\<^sub>0' ## ys)" "stream_all2 (\<preceq>) xs ys" "pred_stream (\<lambda>x. x \<in> S) ys"
proof -
  from \<open>s\<^sub>0 \<preceq> _\<close> \<open>s\<^sub>0' \<in> S\<close> have "equiv' s\<^sub>0 s\<^sub>0'"
    unfolding equiv'_def by auto
  with assms show ?thesis
    by - (drule simulation_run, auto
          dest: PB_invariant.invariant_run elim: stream_all2_weaken intro!: that simp: equiv'_def)
qed

context
  fixes F :: "'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "reaches s\<^sub>0 a \<Longrightarrow> F a \<Longrightarrow> a \<preceq> b \<Longrightarrow> b \<in> S \<Longrightarrow> F b"
begin

corollary final_unreachable:
  "\<nexists> s'. reaches s\<^sub>0 s' \<and> F s'" if "\<forall> s' \<in> S. \<not> F s'"
  using that \<open>s\<^sub>0 \<preceq> s\<^sub>0'\<close> \<open>s\<^sub>0' \<in> S\<close> by (auto 4 3 dest: reachable_S_subsumed)

lemma buechi_run_lasso:
  assumes "finite S" "run (s\<^sub>0 ## xs)" "alw (ev (holds F)) (s\<^sub>0 ## xs)"
  obtains s where "G.reaches s\<^sub>0' s" "G.reaches1 s s" "F s"
proof -
  interpret Finite_Graph E' s\<^sub>0'
    by (standard, rule finite_subset[OF _ assms(1)])
       (auto intro: PB_invariant.invariant_reaches \<open>s\<^sub>0' \<in> S\<close>)
  from run_subsumed[OF assms(2)] obtain ys where ys:
    "G.run (s\<^sub>0' ## ys)" "stream_all2 (\<preceq>) xs ys" "pred_stream (\<lambda>x. x \<in> S) ys" .
  moreover from \<open>run _\<close> have "pred_stream (reaches s\<^sub>0) xs"
    using run_reachable by blast
  ultimately have "stream_all2 (\<lambda>x y. x \<preceq> y \<and> reaches s\<^sub>0 x \<and> y \<in> S) xs ys"
    by (smt stream.pred_set stream.rel_mono_strong)
  with assms(3) \<open>s\<^sub>0 \<preceq> _\<close> \<open>s\<^sub>0' \<in> S\<close> have "alw (ev (holds F)) (s\<^sub>0' ## ys)"
    by (elim alw_ev_lockstep) (erule stream.rel_intros[rotated], auto)
  from buechi_run_lasso[OF ys(1) this] show ?thesis
    using that .
qed

end (* Context for property *)

end (* Start state *)

end (* Unreachability Invariant *)

locale Reachability_Invariant_paired_pre_defs =
  ord less_eq less for less_eq :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix "\<preceq>" 50) and less (infix "\<prec>" 50) +
  fixes E :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool"

locale Reachability_Invariant_paired_defs =
  Reachability_Invariant_paired_pre_defs _ _ E for E :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool" +
  fixes M :: "'l \<Rightarrow> 's set"
    and L :: "'l set"
  fixes l\<^sub>0 :: 'l and s\<^sub>0 :: 's
begin

definition "covered \<equiv> \<lambda> (l, s). \<exists> s' \<in> M l. s \<prec> s'"

definition "RE = (\<lambda>(l, s) ab. s \<in> M l \<and> \<not> covered (l, s) \<and> E (l, s) ab)"

end (* Reachability Invariant paired defs *)

locale Unreachability_Invariant_paired_pre =
  Reachability_Invariant_paired_defs _ _ E +
  preorder less_eq less for E :: "('l \<times> 's) \<Rightarrow> _" +
  fixes P :: "('l \<times> 's) \<Rightarrow> bool"
  assumes mono:
    "s \<preceq> s' \<Longrightarrow> E (l, s) (l', t) \<Longrightarrow> P (l, s) \<Longrightarrow> P (l, s') \<Longrightarrow> \<exists> t'. t \<preceq> t' \<and> E (l, s') (l', t')"
  assumes P_invariant: "P (l, s) \<Longrightarrow> E (l, s) (l', s') \<Longrightarrow> P (l', s')"

locale Unreachability_Invariant_paired =
  Unreachability_Invariant_paired_pre _ _ M L l\<^sub>0 s\<^sub>0 E P for M :: "'l \<Rightarrow> 's set" and L l\<^sub>0 s\<^sub>0 E P +
  fixes SE :: "'l \<times> 's \<Rightarrow> 'l \<times> 's \<Rightarrow> bool"
  assumes subsumption_edges_subsume: "SE (l, s) (l', s') \<Longrightarrow> l' = l \<and> s \<preceq> s'"
  assumes M_invariant: "l \<in> L \<Longrightarrow> s \<in> M l \<Longrightarrow> P (l, s)"
  assumes start: "l\<^sub>0 \<in> L" "\<exists>s' \<in> M l\<^sub>0. s\<^sub>0 \<preceq> s'" "P (l\<^sub>0, s\<^sub>0)"
  assumes closed:
    "\<forall>l \<in> L. \<forall>s \<in> M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s'' \<in> M l'. SE (l', s') (l', s''))"
begin

interpretation Graph_Invariant E P
  by standard (auto intro: P_invariant)

interpretation Unreachability_Invariant
  "\<lambda> (l, s) (l', s'). l' = l \<and> s \<preceq> s'" "\<lambda> (l, s) (l', s'). l' = l \<and> s \<prec> s'" E "(l\<^sub>0, s\<^sub>0)"
  "{(l, s) | l s. l \<in> L \<and> s \<in> M l}"
  supply [intro] = order_trans less_trans less_imp_le
  apply standard
      apply (auto simp: less_le_not_le; fail)+
    apply (fastforce intro: invariant_reaches[OF _ start(3)] M_invariant dest: mono)
  subgoal for s t
    using closed by (cases s; cases t) fastforce
  subgoal
    using subsumption_edges_subsume by auto
  done

lemma E_L:
  assumes "l \<in> L" "s \<in> M l" "E (l, s) (l', s')"
  shows "l' \<in> L"
  using assms closed by simp

context
  fixes F
  assumes F_mono: "\<And> a b. P a \<Longrightarrow> F a \<Longrightarrow> (\<lambda>(l, s) (l', s'). l' = l \<and> s \<preceq> s') a b \<Longrightarrow> P b \<Longrightarrow> F b"
begin

private definition
  "s' \<equiv> SOME s. s \<in> M l\<^sub>0 \<and> s\<^sub>0 \<preceq> s"

private lemma s'_correct:
  "s' \<in> M l\<^sub>0 \<and> s\<^sub>0 \<preceq> s'"
  using start(2) unfolding s'_def by - (rule someI_ex, auto)

private lemma s'_1:
  "(l\<^sub>0, s') \<in> {(l, s) |l s. l \<in> L \<and> s \<in> M l}"
  using s'_correct start by auto

private lemma s'_2:
  "(case (l\<^sub>0, s\<^sub>0) of (l, s) \<Rightarrow> \<lambda>(l', s'). l' = l \<and> s \<preceq> s') (l\<^sub>0, s')"
  using s'_correct start by auto

theorem final_unreachable:
  assumes "\<forall>s'\<in>{(l, s) |l s. l \<in> L \<and> s \<in> M l}. \<not> F s'"
  shows "\<nexists>s'. (l\<^sub>0, s\<^sub>0) \<rightarrow>* s' \<and> F s'"
  using invariant_reaches start(3) M_invariant F_mono assms
  by - (simp, rule final_unreachable[OF s'_2 s'_1, simplified], blast+)

lemma buechi_run_lasso:
  assumes "finite {(l, s) |l s. l \<in> L \<and> s \<in> M l}"
  assumes "run ((l\<^sub>0, s\<^sub>0) ## xs)" "alw (ev (holds F)) ((l\<^sub>0, s\<^sub>0) ## xs)"
  obtains s\<^sub>0' l s where
    "G.reaches (l\<^sub>0, s\<^sub>0') (l, s)" "G.reaches1 (l, s) (l, s)" "F (l, s)" "s\<^sub>0' \<in> M l\<^sub>0" "s\<^sub>0 \<preceq> s\<^sub>0'"
  using F_mono assms M_invariant invariant_reaches start(3) s'_correct
  by - (rule buechi_run_lasso[OF s'_2 s'_1, of F]; clarsimp; blast)

context
  fixes f :: "'l \<times> 's \<Rightarrow> nat"
  assumes finite: "finite L" "\<forall> l \<in> L. finite (M l)"
  assumes f_topo: "\<And>l s l1 s1 l2 s2.
    l \<in> L \<Longrightarrow> s \<in> M l \<Longrightarrow> l2 \<in> L \<Longrightarrow> s2 \<in> M l2 \<Longrightarrow> E (l, s) (l1, s1) \<Longrightarrow> SE (l1, s1) (l2, s2) \<Longrightarrow>
    if F (l, s) then f (l, s) < f (l2, s2) else f (l, s) \<le> f (l2, s2)"
begin

interpretation c: Contract2
  where A = "\<lambda>(l, s) (l', s'). l \<in> L \<and> s \<in> M l \<and> E (l, s) (l', s')"
    and B = SE
    and G = "\<lambda>(l, s). l \<in> L \<and> s \<in> M l"
  using f_topo by - (standard, auto)

lemma no_buechi_run:
  assumes "Graph_Defs.run E ((l\<^sub>0, s\<^sub>0) ## xs)" "alw (ev (holds F)) ((l\<^sub>0, s\<^sub>0) ## xs)"
  shows False
proof -
  have finite: "finite {(l, s). l \<in> L \<and> s \<in> M l}" (is "finite ?S")
  proof -
    have "?S \<subseteq> L \<times> \<Union> (M ` L)"
      by auto
    also from finite have "finite \<dots>"
      by auto
    finally show ?thesis .
  qed
  interpret sim: Simulation E' c.E "\<lambda>(l, s) (l', s'). l = l' \<and> s' = s \<and> l \<in> L \<and> s \<in> M l"
    unfolding E'_def c.E_def by standard auto
  obtain s\<^sub>0' l s where
    "s\<^sub>0 \<preceq> s\<^sub>0'" "s\<^sub>0' \<in> M l\<^sub>0" "G.reaches (l\<^sub>0, s\<^sub>0') (l, s)" "G.reaches1 (l, s) (l, s)" "F (l, s)"
    using finite assms by - (rule buechi_run_lasso, auto)
  then have "c.E.reaches1 (l, s) (l, s)"
    using E'_def G.reaches1_reaches_iff2 by - (frule sim.simulation_reaches1, auto)
  then have "\<not> F (l, s)"
    by (rule c.no_accepting_cycle)
  from this \<open>F (l, s)\<close> show ?thesis ..
qed

end (* 'Topological' numbering *)

end (* Final state predicate *)

end (* Unreachability Invariant paired *)



subsection \<open>Unused\<close>

lemma (in Reachability_Compatible_Subsumption_Graph_Final) no_accepting_cycleI:
  assumes "\<nexists> x. G'.reachable x \<and> x \<rightarrow>\<^sub>G\<^sup>+' x \<and> F x"
  shows "\<nexists> x. reachable x \<and> x \<rightarrow>\<^sup>+ x \<and> F x"
  using cycle_G'_cycle assms F_mono by auto


locale Reachability_Compatible_Subsumption_Graph_Final2_pre =
  Subsumption_Graph_Defs + preorder less_eq less +
  fixes P :: "'a \<Rightarrow> bool" and G :: "'a \<Rightarrow> bool"
  assumes mono:
    "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow> \<exists>b'. E b b' \<and> a' \<preceq> b'"
  assumes P_invariant: "P a \<Longrightarrow> E a b \<Longrightarrow> P b"
  assumes G_P[intro]: "G a \<Longrightarrow> P a"
  assumes subgraph: "\<forall> s s'. RE s s' \<longrightarrow> E s s'"
  assumes G_finite: "finite {a. G a}"
      and finitely_branching: "\<And>a. G a \<Longrightarrow> finite (Collect (E a))"
  assumes G_start: "G s\<^sub>0"
  fixes F :: "'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "F a \<Longrightarrow> a \<preceq> b \<Longrightarrow> F b"
  assumes G_anti_symmetric[rule_format]: "\<forall> a b. G a \<and> G b \<and> a \<preceq> b \<and> b \<preceq> a \<longrightarrow> a = b"
begin

abbreviation "E_mix \<equiv> \<lambda> x y. RE x y \<and> G x \<and> G y \<or> E x y \<and> G x \<and> \<not> G y \<or> \<not> G x \<and> x \<prec> y \<and> G y"

sublocale G_mix: Graph_Start_Defs E_mix s\<^sub>0 .

sublocale P_invariant: Graph_Invariant E P
  by standard (auto intro: P_invariant)

sublocale G_invariant: Graph_Invariant E_mix P
  by standard (auto simp: subgraph intro: P_invariant)

lemma mix_reachable_G[intro]:
  "P x" if "G_mix.reachable x"
proof -
  from G_start have "P s\<^sub>0"
    by auto
  with that show ?thesis
    by induction (auto simp: subgraph intro: P_invariant)
qed

lemma P_reachable[intro]:
  "P a" if "reachable a"
  using that G_start by (auto simp: reachable_def intro: P_invariant.invariant_reaches)

lemma mix_finite_reachable: "finite {a. G_mix.reachable a}"
proof -
  have "G x \<or> (\<exists> a. G a \<and> E a x)" if "G_mix.reachable x" for x
    using that G_start by induction auto
  then have "{a. G_mix.reachable a} \<subseteq> Collect G \<union> {(a, b). E a b} `` Collect G"
    by auto
  also have "finite \<dots>"
    using G_finite by (auto intro: finitely_branching)
  finally show ?thesis .
qed

end

locale Reachability_Compatible_Subsumption_Graph_Final2 =
  Reachability_Compatible_Subsumption_Graph_Final2_pre +
  assumes liveness_compatible:
    "\<forall>a a' b. P a \<and> G a' \<and> a \<preceq> a' \<and> E a b
      \<longrightarrow> (\<exists>b'. b \<preceq> b' \<and> a' \<rightarrow>\<^sub>G b' \<and> G b')
        \<or> (\<exists>b' b''. b \<preceq> b' \<and> b' \<prec> b'' \<and> E a' b' \<and> \<not> G b' \<and> G b'')"
begin

text \<open>Setup for automation\<close>
context
  includes graph_automation
begin

lemma subsumption_step:
  "(\<exists>b'. b \<preceq> b' \<and> a' \<rightarrow>\<^sub>G b' \<and> G b') \<or> (\<exists>b' b''. b \<preceq> b' \<and> b' \<prec> b'' \<and> E a' b' \<and> \<not> G b' \<and> G b'')"
  if "P a" "E a b" "G a'" "a \<preceq> a'"
  using liveness_compatible that by auto

lemma subsumption_step':
  "\<exists> b'. b \<preceq> b' \<and> G_mix.reaches1 a' b' \<and> G b'" if "P a" "E a b" "G a'" "a \<preceq> a'"
proof -
  from subsumption_step[OF that] show ?thesis
  proof (safe, goal_cases)
    case (1 b')
    then show ?case
      using that(3) by auto
  next
    case (2 b' b'')
    with \<open>G a'\<close> have "E_mix b' b''" "E_mix a' b'"
      by auto
    with \<open>b \<preceq> b'\<close> \<open>b' \<prec> b''\<close> \<open>G b''\<close> show ?case
      including graph_automation_aggressive using le_less_trans less_imp_le by blast
  qed
qed

theorem reachability_complete':
  "\<exists> s'. s \<preceq> s' \<and> G_mix.reachable s' \<and> G s'" if "a \<rightarrow>* s" "G_mix.reachable a" "G a"
  using that
proof (induction)
  case base
  then show ?case by auto
next
  case (step s t)
  then obtain s' where "s \<preceq> s'" "G_mix.reachable s'" "G s'"
    by auto
  from \<open>G a\<close> \<open>a \<rightarrow>* s\<close> have "P s"
    by (auto intro: P_invariant.invariant_reaches)
  from subsumption_step[OF this \<open>E s t\<close> \<open>G s'\<close> \<open>s \<preceq> s'\<close>] show ?case
  proof safe
    fix b' :: \<open>'a\<close>
    assume \<open>t \<preceq> b'\<close> and \<open>s' \<rightarrow>\<^sub>G b'\<close> and \<open>G b'\<close>
    with \<open>G s'\<close> have "E_mix s' b'"
      by auto
    with \<open>t \<preceq> b'\<close> \<open>G b'\<close> \<open>G_mix.reachable s'\<close> show \<open>\<exists>s'. t \<preceq> s' \<and> G_mix.reachable s' \<and> G s'\<close>
      by auto
  next
    fix b' b'' :: \<open>'a\<close>
    assume  \<open>t \<preceq> b'\<close> and \<open>b' \<prec> b''\<close> and \<open>s' \<rightarrow> b'\<close> and \<open>\<not> G b'\<close> and \<open>G b''\<close>
    with \<open>G s'\<close> have "E_mix s' b'" "E_mix b' b''"
      by auto
    with \<open>G b''\<close> \<open>t \<preceq> _\<close> \<open>_ \<prec> b''\<close> \<open>G_mix.reachable s'\<close> show 
      \<open>\<exists>s'. t \<preceq> s' \<and> G_mix.reachable s' \<and> G s'\<close>
      apply (inst_existentials b'')
      subgoal
        using le_less_trans less_imp_le by auto
      by auto
  qed
qed

lemma steps_G_mix_steps:
  "\<exists> ys ns. list_all2 (\<preceq>) xs (nths ys ns) \<and> G_mix.steps (b # ys)" if
  "steps (a # xs)" "P a" "a \<preceq> b" "G b"
  using that
proof (induction "a # xs" arbitrary: a b xs)
  case (Single)
  then show ?case by force
next
  case (Cons x y xs)
  from subsumption_step'[OF \<open>P x\<close> \<open>E x y\<close> _ \<open>x \<preceq> b\<close>] \<open>G b\<close> obtain b' where
    "y \<preceq> b'" "G_mix.reaches1 b b'" "G b'"
    by auto
  with \<open>P x\<close> Cons.hyps(1) Cons.prems(3) obtain ys ns where
    "list_all2 (\<preceq>) xs (nths ys ns)" "G_mix.steps (b' # ys)"
    by atomize_elim
       (blast intro: Cons.hyps(3)[OF _ \<open>y \<preceq> b'\<close>]
          P_invariant graphI_aggressive G_invariant.invariant_reaches
       )
  from  \<open>G_mix.reaches1 b b'\<close> this(2) obtain as where
    "G_mix.steps (b # as @ b' # ys)"
    by (fastforce intro: G_mix.graphI_aggressive1)
  with \<open>y \<preceq> b'\<close> show ?case
    apply (inst_existentials "as @ b' # ys" "{length as} \<union> {n + length as + 1 | n. n \<in> ns}")
    subgoal
      apply (subst nths_split, force)
      apply (subst nths_nth, (simp; fail))
      apply simp
      apply (subst nths_shift, force)
      subgoal premises prems
      proof -
        have
          "{x - length as |x. x \<in> {Suc (n + length as) |n. n \<in> ns}} = {n + 1 | n. n \<in> ns}"
          by force
        with \<open>list_all2 _ _ _\<close> show ?thesis
          by (simp add: nths_Cons)
      qed
      done
    by assumption
qed

lemma cycle_G_mix_cycle'':
  assumes "steps (s\<^sub>0 # ws @ x # xs @ [x])"
  shows "\<exists> x' xs' ys'. x \<preceq> x' \<and> G_mix.steps (s\<^sub>0 # xs' @ x' # ys' @ [x'])"
proof -
  let ?n  = "card {x. G_mix.reachable x} + 1"
  let ?xs = "x # concat (replicate ?n (xs @ [x]))"
  from assms(1) have "steps (x # xs @ [x])"
    by (auto intro: graphI_aggressive2)
  with steps_replicate[of "x # xs @ [x]" ?n] have "steps ?xs"
    by auto
  have "steps (s\<^sub>0 # ws @ ?xs)"
  proof -
    from assms have "steps (s\<^sub>0 # ws @ [x])" (* XXX *)
      by (auto intro: graphI_aggressive2)
    with \<open>steps ?xs\<close> show ?thesis
      by (fastforce intro: graphI_aggressive1)
  qed
  from steps_G_mix_steps[OF this, of s\<^sub>0] G_start obtain ys ns where ys:
    "list_all2 (\<preceq>) (ws @ x # concat (replicate ?n (xs @ [x]))) (nths ys ns)"
    "G_mix.steps (s\<^sub>0 # ys)"
    by auto
  then obtain x' ys' ns' ws' where ys':
    "G_mix.steps (x' # ys')" "G_mix.steps (s\<^sub>0 # ws' @ [x'])"
    "list_all2 (\<preceq>) (concat (replicate ?n (xs @ [x]))) (nths ys' ns')"
    apply atomize_elim
    apply auto
    apply (subst (asm) list_all2_append1)
    apply safe
    apply (subst (asm) list_all2_Cons1)
    apply safe
    apply (drule nths_eq_appendD)
    apply safe
    apply (drule nths_eq_ConsD)
    apply safe
    subgoal for ys1 ys2 z ys3 ys4 ys5 ys6 ys7 i
      apply (inst_existentials z ys7)
      subgoal premises prems
        using prems(1) by (auto intro: G_mix.graphI_aggressive2)
      subgoal premises prems
      proof -
        from prems have "G_mix.steps ((s\<^sub>0 # ys4 @ ys6 @ [z]) @ ys7)"
          by auto
        moreover then have "G_mix.steps (s\<^sub>0 # ys4 @ ys6 @ [z])"
          by (auto intro: G_mix.graphI_aggressive2)
        ultimately show ?thesis
          by (inst_existentials "ys4 @ ys6") auto
      qed
      by force
    done
  let ?ys = "filter ((\<preceq>) x) ys'"
  have "length ?ys \<ge> ?n"
    using list_all2_replicate_elem_filter[OF ys'(3), of x]
    using filter_nths_length[of "((\<preceq>) x)" ys' ns']
    by auto
  from \<open>G_mix.steps (s\<^sub>0 # ws' @ [x'])\<close> have "G_mix.reachable x'"
    by - (rule G_mix.reachable_reaches, auto)
  have "set ?ys \<subseteq> set ys'"
    by auto
  also have "\<dots> \<subseteq> {x. G_mix.reachable x}"
    using \<open>G_mix.steps (x' # _)\<close> \<open>G_mix.reachable x'\<close>
    by clarsimp (rule G_mix.reachable_steps_elem[rotated], assumption, auto)
  finally have "\<not> distinct ?ys"
    using distinct_card[of ?ys] \<open>_ >= ?n\<close>
    by - (rule ccontr; drule distinct_length_le[OF mix_finite_reachable]; simp)
  from not_distinct_decomp[OF this] obtain as y bs cs where "?ys = as @ [y] @ bs @ [y] @ cs"
    by auto
  then obtain as' bs' cs' where
    "ys' = as' @ [y] @ bs' @ [y] @ cs'"
    apply atomize_elim
    apply simp
    apply (drule filter_eq_appendD filter_eq_ConsD filter_eq_appendD[OF sym], clarify)+
    apply clarsimp
    subgoal for as1 as2 bs1 bs2 cs'
      by (inst_existentials "as1 @ as2" "bs1 @ bs2") simp
    done
  have "G_mix.steps (y # bs' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>G_mix.steps (x' # _)\<close> \<open>ys' = _\<close> show ?thesis
      by (force intro: G_mix.graphI_aggressive2)
  qed
  moreover have "G_mix.steps (s\<^sub>0 # ws' @ x' # as' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>G_mix.steps (x' # ys')\<close> \<open>ys' = _\<close> have "G_mix.steps (x' # as' @ [y])"
      by (force intro: G_mix.graphI_aggressive2)
    with \<open>G_mix.steps (s\<^sub>0 # ws' @ [x'])\<close> show ?thesis
      by (fastforce intro: G_mix.graphI_aggressive1)
  qed
  moreover from \<open>?ys = _\<close> have "x \<preceq> y"
  proof -
    from \<open>?ys = _\<close> have "y \<in> set ?ys" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis
    by (inst_existentials y "ws' @ x' # as'" bs'; fastforce intro: G_mix.graphI_aggressive1)
qed

lemma cycle_G_mix_cycle':
  assumes "steps (s\<^sub>0 # ws @ x # xs @ [x])"
  shows "\<exists> y ys. x \<preceq> y \<and> G_mix.steps (y # ys @ [y]) \<and> G_mix.reachable y"
proof -
  from cycle_G_mix_cycle''[OF assms] obtain x' xs' ys' where
    "x \<preceq> x'" "G_mix.steps (s\<^sub>0 # xs' @ x' # ys' @ [x'])"
    by auto
  then show ?thesis
    apply (inst_existentials x' ys')
    subgoal by assumption
    subgoal by (auto intro: G_mix.graphI_aggressive2)
    by (rule G_mix.reachable_reaches, auto)
qed

lemma cycle_G_mix_cycle:
  assumes "reachable x" "x \<rightarrow>\<^sup>+ x"
  shows "\<exists> y ys. x \<preceq> y \<and> G_mix.reachable y \<and> G_mix.reaches1 y y"
proof -
  from assms(2) obtain xs where *: "steps (x # xs @ x # xs @ [x])"
    by (fastforce intro: graphI_aggressive1)
  from reachable_steps[of x] assms(1) obtain ws where "steps ws" "hd ws = s\<^sub>0" "last ws = x"
    by auto
  with * obtain us where "steps (s\<^sub>0 # (us @ xs) @ x # xs @ [x])"
    by (cases ws; force intro: graphI_aggressive1) (* slow *)
  from cycle_G_mix_cycle'[OF this] show ?thesis
    by (auto simp: G_mix.steps_reaches1)
qed

theorem no_accepting_cycleI:
  assumes "\<nexists> x. G_mix.reachable x \<and> G_mix.reaches1 x x \<and> F x"
  shows "\<nexists> x. reachable x \<and> x \<rightarrow>\<^sup>+ x \<and> F x"
  using cycle_G_mix_cycle assms F_mono by auto

end

end


locale Reachability_Compatible_Subsumption_Graph_Final'_pre =
  Subsumption_Graph_Defs + preorder less_eq less +
  fixes P :: "'a \<Rightarrow> bool" and G :: "'a \<Rightarrow> bool"
  assumes mono:
    "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> P a \<Longrightarrow> P b \<Longrightarrow> \<exists>b'. E b b' \<and> a' \<preceq> b'"
  assumes P_invariant: "P a \<Longrightarrow> E a b \<Longrightarrow> P b"
  assumes G_P[intro]: "G a \<Longrightarrow> P a"
  assumes subgraph: "\<forall> s s'. RE s s' \<longrightarrow> E s s'"
  assumes G_finite: "finite {a. G a}"
  assumes G_start: "G s\<^sub>0"
  fixes F :: "'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "F a \<Longrightarrow> a \<preceq> b \<Longrightarrow> F b"
  assumes G_anti_symmetric[rule_format]: "\<forall> a b. G a \<and> G b \<and> a \<preceq> b \<and> b \<preceq> a \<longrightarrow> a = b"
begin

abbreviation "E_mix \<equiv> \<lambda> x y. RE x y \<and> G y \<or> x \<prec> y \<and> G y"

sublocale G_mix: Graph_Start_Defs E_mix s\<^sub>0 .

sublocale P_invariant: Graph_Invariant E P
  by standard (auto intro: P_invariant)

sublocale G_invariant: Graph_Invariant E_mix G
  by standard auto

lemma mix_reachable_G[intro]:
  "G x" if "G_mix.reachable x"
  using that G_start by induction auto

lemma P_reachable[intro]:
  "P a" if "reachable a"
  using that G_start by (auto simp: reachable_def intro: P_invariant.invariant_reaches)

lemma mix_finite_reachable: "finite {a. G_mix.reachable a}"
  by (blast intro: finite_subset[OF _ G_finite])

end


locale Reachability_Compatible_Subsumption_Graph_Final'' =
  Reachability_Compatible_Subsumption_Graph_Final'_pre +
  assumes liveness_compatible:
    "\<forall>a a' b. P a \<and> G a' \<and> a \<preceq> a' \<and> E a b
      \<longrightarrow> (\<exists> a'' b'. a' \<preceq> a'' \<and> b \<preceq> b' \<and> a'' \<rightarrow>\<^sub>G b' \<and> G a'' \<and> G b')"
begin

text \<open>Setup for automation\<close>
context
  includes graph_automation
begin

lemma subsumption_step:
  "\<exists> a'' b'. a' \<preceq> a'' \<and> b \<preceq> b' \<and> a'' \<rightarrow>\<^sub>G b' \<and> G a'' \<and> G b'" if
  "P a" "E a b" "G a'" "a \<preceq> a'"
  using liveness_compatible that by auto

lemma G_mix_reaches:
  assumes "G a" "G b" "a \<preceq> b"
  shows "G_mix.reaches a b"
  using assms by (cases "a \<prec> b") (auto simp: G_anti_symmetric less_le_not_le)

lemma subsumption_step':
  "\<exists> b'. b \<preceq> b' \<and> G_mix.reaches1 a' b'" if "P a" "E a b" "G a'" "a \<preceq> a'"
proof -
  from subsumption_step[OF that] guess a'' b'
    by safe
  with \<open>G a'\<close> have "G_mix.reaches a' a''" "E_mix a'' b'"
    by (auto intro: G_mix_reaches)
  with \<open>b \<preceq> b'\<close> show ?thesis
    unfolding G_mix.reaches1_reaches_iff2 by auto
qed

theorem reachability_complete':
  "\<exists> s'. s \<preceq> s' \<and> G_mix.reachable s' \<and> G s'" if "a \<rightarrow>* s" "G_mix.reachable a" "G a"
  using that
proof (induction)
  case base
  then show ?case by auto
next
  case (step s t)
  then obtain s' where "s \<preceq> s'" "G_mix.reachable s'" "G s'"
    by auto
  from \<open>G a\<close> \<open>a \<rightarrow>* s\<close> have "P s"
    by (auto intro: P_invariant.invariant_reaches)
  from subsumption_step[OF this \<open>E s t\<close> \<open>G s'\<close> \<open>s \<preceq> s'\<close>] guess s'' t' by clarify
  with \<open>G_mix.reachable s'\<close> show ?case
    using G_mix_reaches by (inst_existentials t') blast+
qed

lemma steps_G_mix_steps:
  "\<exists> ys ns. list_all2 (\<preceq>) xs (nths ys ns) \<and> G_mix.steps (b # ys)" if
  "steps (a # xs)" "P a" "a \<preceq> b" "G b"
  using that
proof (induction "a # xs" arbitrary: a b xs)
  case (Single)
  then show ?case by force
next
  case (Cons x y xs)
  from subsumption_step'[OF \<open>P x\<close> \<open>E x y\<close> _ \<open>x \<preceq> b\<close>] \<open>G b\<close> obtain b' where
    "y \<preceq> b'" "G_mix.reaches1 b b'"
    by auto
  with \<open>P x\<close> Cons.hyps(1) Cons.prems(3) obtain ys ns where
    "list_all2 (\<preceq>) xs (nths ys ns)" "G_mix.steps (b' # ys)"
    by atomize_elim
       (blast intro: Cons.hyps(3)[OF _ \<open>y \<preceq> b'\<close>]
          P_invariant graphI_aggressive G_invariant.invariant_reaches
       )
  from  \<open>G_mix.reaches1 b b'\<close> this(2) obtain as where
    "G_mix.steps (b # as @ b' # ys)"
    by (fastforce intro: G_mix.graphI_aggressive1)
  with \<open>y \<preceq> b'\<close> show ?case
    apply (inst_existentials "as @ b' # ys" "{length as} \<union> {n + length as + 1 | n. n \<in> ns}")
    subgoal
      apply (subst nths_split, force)
      apply (subst nths_nth, (simp; fail))
      apply simp
      apply (subst nths_shift, force)
      subgoal premises prems
      proof -
        have
          "{x - length as |x. x \<in> {Suc (n + length as) |n. n \<in> ns}} = {n + 1 | n. n \<in> ns}"
          by force
        with \<open>list_all2 _ _ _\<close> show ?thesis
          by (simp add: nths_Cons)
      qed
      done
    by assumption
qed

lemma cycle_G_mix_cycle'':
  assumes "steps (s\<^sub>0 # ws @ x # xs @ [x])"
  shows "\<exists> x' xs' ys'. x \<preceq> x' \<and> G_mix.steps (s\<^sub>0 # xs' @ x' # ys' @ [x'])"
proof -
  let ?n  = "card {x. G_mix.reachable x} + 1"
  let ?xs = "x # concat (replicate ?n (xs @ [x]))"
  from assms(1) have "steps (x # xs @ [x])"
    by (auto intro: graphI_aggressive2)
  with steps_replicate[of "x # xs @ [x]" ?n] have "steps ?xs"
    by auto
  have "steps (s\<^sub>0 # ws @ ?xs)"
  proof -
    from assms have "steps (s\<^sub>0 # ws @ [x])" (* XXX *)
      by (auto intro: graphI_aggressive2)
    with \<open>steps ?xs\<close> show ?thesis
      by (fastforce intro: graphI_aggressive1)
  qed
  from steps_G_mix_steps[OF this, of s\<^sub>0] obtain ys ns where ys:
    "list_all2 (\<preceq>) (ws @ x # concat (replicate ?n (xs @ [x]))) (nths ys ns)"
    "G_mix.steps (s\<^sub>0 # ys)"
    by auto
  then obtain x' ys' ns' ws' where ys':
    "G_mix.steps (x' # ys')" "G_mix.steps (s\<^sub>0 # ws' @ [x'])"
    "list_all2 (\<preceq>) (concat (replicate ?n (xs @ [x]))) (nths ys' ns')"
    apply atomize_elim
    apply auto
    apply (subst (asm) list_all2_append1)
    apply safe
    apply (subst (asm) list_all2_Cons1)
    apply safe
    apply (drule nths_eq_appendD)
    apply safe
    apply (drule nths_eq_ConsD)
    apply safe
    subgoal for ys1 ys2 z ys3 ys4 ys5 ys6 ys7 i
      apply (inst_existentials z ys7)
      subgoal premises prems
        using prems(1) by (auto intro: G_mix.graphI_aggressive2)
      subgoal premises prems
      proof -
        from prems have "G_mix.steps ((s\<^sub>0 # ys4 @ ys6 @ [z]) @ ys7)"
          by auto
        moreover then have "G_mix.steps (s\<^sub>0 # ys4 @ ys6 @ [z])"
          by (auto intro: G_mix.graphI_aggressive2)
        ultimately show ?thesis
          by (inst_existentials "ys4 @ ys6") auto
      qed
      by force
    done
  let ?ys = "filter ((\<preceq>) x) ys'"
  have "length ?ys \<ge> ?n"
    using list_all2_replicate_elem_filter[OF ys'(3), of x]
    using filter_nths_length[of "((\<preceq>) x)" ys' ns']
    by auto
  from \<open>G_mix.steps (s\<^sub>0 # ws' @ [x'])\<close> have "G_mix.reachable x'"
    by - (rule G_mix.reachable_reaches, auto)
  have "set ?ys \<subseteq> set ys'"
    by auto
  also have "\<dots> \<subseteq> {x. G_mix.reachable x}"
    using \<open>G_mix.steps (x' # _)\<close> \<open>G_mix.reachable x'\<close>
    by clarsimp (rule G_mix.reachable_steps_elem[rotated], assumption, auto)
  finally have "\<not> distinct ?ys"
    using distinct_card[of ?ys] \<open>_ >= ?n\<close>
    by - (rule ccontr; drule distinct_length_le[OF mix_finite_reachable]; simp)
  from not_distinct_decomp[OF this] obtain as y bs cs where "?ys = as @ [y] @ bs @ [y] @ cs"
    by auto
  then obtain as' bs' cs' where
    "ys' = as' @ [y] @ bs' @ [y] @ cs'"
    apply atomize_elim
    apply simp
    apply (drule filter_eq_appendD filter_eq_ConsD filter_eq_appendD[OF sym], clarify)+
    apply clarsimp
    subgoal for as1 as2 bs1 bs2 cs'
      by (inst_existentials "as1 @ as2" "bs1 @ bs2") simp
    done
  have "G_mix.steps (y # bs' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>G_mix.steps (x' # _)\<close> \<open>ys' = _\<close> show ?thesis
      by (force intro: G_mix.graphI_aggressive2)
  qed
  moreover have "G_mix.steps (s\<^sub>0 # ws' @ x' # as' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>G_mix.steps (x' # ys')\<close> \<open>ys' = _\<close> have "G_mix.steps (x' # as' @ [y])"
      by (force intro: G_mix.graphI_aggressive2)
    with \<open>G_mix.steps (s\<^sub>0 # ws' @ [x'])\<close> show ?thesis
      by (fastforce intro: G_mix.graphI_aggressive1)
  qed
  moreover from \<open>?ys = _\<close> have "x \<preceq> y"
  proof -
    from \<open>?ys = _\<close> have "y \<in> set ?ys" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis
    by (inst_existentials y "ws' @ x' # as'" bs'; fastforce intro: G_mix.graphI_aggressive1)
qed

lemma cycle_G_mix_cycle':
  assumes "steps (s\<^sub>0 # ws @ x # xs @ [x])"
  shows "\<exists>y ys. x \<preceq> y \<and> G_mix.steps (y # ys @ [y]) \<and> G_mix.reachable y"
proof -
  from cycle_G_mix_cycle''[OF assms] obtain x' xs' ys' where
    "x \<preceq> x'" "G_mix.steps (s\<^sub>0 # xs' @ x' # ys' @ [x'])"
    by auto
  then show ?thesis
    apply (inst_existentials x' ys')
    subgoal by assumption
    subgoal by (auto intro: G_mix.graphI_aggressive2)
    by (rule G_mix.reachable_reaches, auto)
qed

lemma cycle_G_mix_cycle:
  assumes "reachable x" "x \<rightarrow>\<^sup>+ x"
  shows "\<exists>y. x \<preceq> y \<and> G_mix.reachable y \<and> G_mix.reaches1 y y"
proof -
  from assms(2) obtain xs where *: "steps (x # xs @ x # xs @ [x])"
    by (fastforce intro: graphI_aggressive1)
  from reachable_steps[of x] assms(1) obtain ws where "steps ws" "hd ws = s\<^sub>0" "last ws = x"
    by auto
  with * obtain us where "steps (s\<^sub>0 # (us @ xs) @ x # xs @ [x])"
    by (cases ws; force intro: graphI_aggressive1) (* slow *)
  from cycle_G_mix_cycle'[OF this] show ?thesis
    by (auto simp: G_mix.steps_reaches1)
qed

end

end


locale Reachability_Compatible_Subsumption_Graph_Final' =
  Reachability_Compatible_Subsumption_Graph_Final'_pre +
  assumes liveness_compatible:
    "\<forall> s. G s \<longrightarrow> (\<forall> s'. E s s' \<longrightarrow> RE s s' \<and> G s') \<or> (\<exists> t. s \<prec> t \<and> G t)"
begin

text \<open>Setup for automation\<close>
context
  includes graph_automation
begin

lemmas preorder_intros = order_trans less_trans less_imp_le

lemma reachable_has_surrogate:
  "\<exists> t. G t \<and> s \<preceq> t \<and> (\<forall> s'. E t s' \<longrightarrow> RE t s' \<and> G s')" if "G s"
proof -
  note [intro] = preorder_intros
  from G_finite \<open>G s\<close> obtain x where
    "\<forall>s'. E x s' \<longrightarrow> RE x s' \<and> G s'" "G x" "((\<prec>)\<^sup>*\<^sup>*) s x"
    by atomize_elim (induction rule: rtranclp_ev_induct2, auto simp: liveness_compatible)
  moreover from \<open>((\<prec>)\<^sup>*\<^sup>*) s x\<close> have "s \<prec> x \<or> s = x"
    by induction auto
  ultimately show ?thesis
    by auto
qed

lemma subsumption_step:
  "\<exists> a'' b'. a' \<preceq> a'' \<and> b \<preceq> b' \<and> a'' \<rightarrow>\<^sub>G b' \<and> G a'' \<and> G b'" if
  "P a" "E a b" "G a'" "a \<preceq> a'"
proof -
  note [intro] = preorder_intros
  from mono[OF \<open>a \<preceq> a'\<close> \<open>E a b\<close>] \<open>P a\<close> \<open>G a'\<close> obtain b' where "E a' b'" "b \<preceq> b'"
    by auto
  from reachable_has_surrogate[OF \<open>G a'\<close>] obtain a''
    where "a' \<preceq> a''" "G a''" and *: "\<forall> s'. E a'' s' \<longrightarrow> RE a'' s' \<and> G s'"
    by auto
  from mono[OF \<open>a' \<preceq> a''\<close> \<open>E a' b'\<close>] \<open>G a'\<close> \<open>G a''\<close> obtain b'' where
    "E a'' b''" "b' \<preceq> b''"
    by auto
  with * \<open>a' \<preceq> a''\<close> \<open>b \<preceq> b'\<close> \<open>G a''\<close> show ?thesis
    by auto
qed

end

sublocale Reachability_Compatible_Subsumption_Graph_Final''
  using subsumption_step by - (standard, auto)

theorem no_accepting_cycleI:
  assumes "\<nexists> x. G_mix.reachable x \<and> G_mix.reaches1 x x \<and> F x"
  shows "\<nexists> x. reachable x \<and> x \<rightarrow>\<^sup>+ x \<and> F x"
  using cycle_G_mix_cycle assms F_mono by auto

end


locale Reachability_Compatible_Subsumption_Graph_Final1 =
  Reachability_Compatible_Subsumption_Graph_Final'_pre +
  assumes reachable_has_surrogate:
    "\<forall> s. G s \<longrightarrow> (\<exists> t. G t \<and> s \<preceq> t \<and> (\<forall> s'. E t s' \<longrightarrow> RE t s' \<and> G s'))"
begin

text \<open>Setup for automation\<close>
context
  includes graph_automation
begin

lemmas preorder_intros = order_trans less_trans less_imp_le

lemma subsumption_step:
  "\<exists> a'' b'. a' \<preceq> a'' \<and> b \<preceq> b' \<and> a'' \<rightarrow>\<^sub>G b' \<and> G a'' \<and> G b'" if
  "P a" "E a b" "G a'" "a \<preceq> a'"
proof -
  note [intro] = preorder_intros
  from mono[OF \<open>a \<preceq> a'\<close> \<open>E a b\<close>] \<open>P a\<close> \<open>G a'\<close> obtain b' where "E a' b'" "b \<preceq> b'"
    by auto
  from reachable_has_surrogate \<open>G a'\<close> obtain a''
    where "a' \<preceq> a''" "G a''" and *: "\<forall> s'. E a'' s' \<longrightarrow> RE a'' s' \<and> G s'"
    by auto
  from mono[OF \<open>a' \<preceq> a''\<close> \<open>E a' b'\<close>] \<open>G a'\<close> \<open>G a''\<close> obtain b'' where
    "E a'' b''" "b' \<preceq> b''"
    by auto
  with * \<open>a' \<preceq> a''\<close> \<open>b \<preceq> b'\<close> \<open>G a''\<close> show ?thesis
    by auto
qed

end

sublocale Reachability_Compatible_Subsumption_Graph_Final''
  using subsumption_step by - (standard, auto)

theorem no_accepting_cycleI:
  assumes "\<nexists> x. G_mix.reachable x \<and> G_mix.reaches1 x x \<and> F x"
  shows "\<nexists> x. reachable x \<and> x \<rightarrow>\<^sup>+ x \<and> F x"
  using cycle_G_mix_cycle assms F_mono by auto

end



subsection \<open>Instantiating Reachability Compatible Subsumption Graphs\<close>

locale Reachability_Invariant_paired = Reachability_Invariant_paired_defs + preorder less_eq less +
  assumes E_T: "\<forall> l s l' s'. E (l, s) (l', s') \<longleftrightarrow> (\<exists> f. (l', f) \<in> T l \<and> s' = f s)"
  assumes mono:
    "s \<preceq> s' \<Longrightarrow> E (l, s) (l', t) \<Longrightarrow> E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) (l, s) \<Longrightarrow> E\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) (l, s')
    \<Longrightarrow> \<exists> t'. t \<preceq> t' \<and> E (l, s') (l', t')"
  assumes finitely_branching: "finite (Collect (E (a, b)))"
  assumes start:"l\<^sub>0 \<in> L" "s\<^sub>0 \<in> S" "s\<^sub>0 \<in> M(l\<^sub>0)"
  assumes closed:
    "\<forall> l \<in> L. \<forall> (l', f) \<in> T l. l' \<in> L \<and> (\<forall> s \<in> M l. (\<exists> s' \<in> M l'. f s \<prec> s') \<or> f s \<in> M l')"
  assumes reachable:
    "\<forall> l \<in> L. \<forall> s \<in> M l. RE\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) (l, s)"
  assumes finite:
    "finite L" "\<forall> l \<in> L. finite (M l)"
begin

lemma invariant:
  "((\<exists> s' \<in> M l. s \<prec> s') \<or> s \<in> M l) \<and> l \<in> L" if "RE\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) (l, s)"
  using that start closed by (induction rule: rtranclp_induct2) (auto 4 3 simp: RE_def)

interpretation Reachability_Compatible_Subsumption_Graph_View 
  "\<lambda> (l, s) (l', s'). l' = l \<and> s \<preceq> s'" "\<lambda> (l, s) (l', s'). l' = l \<and> s \<prec> s'"
  E "(l\<^sub>0, s\<^sub>0)" RE
  "\<lambda> (l, s) (l', s'). l' = l \<and> s \<prec> s'" covered
  supply [intro] = order_trans less_trans less_imp_le
  apply standard
         apply (auto simp: less_le_not_le; fail)
        apply (auto simp: less_le_not_le; fail)
       apply (auto simp: less_le_not_le; fail)
      apply clarsimp
      apply (drule mono, assumption+, (simp add: Graph_Start_Defs.reachable_def; fail)+)
      apply blast
     apply (clarsimp simp: Graph_Start_Defs.reachable_def; safe)
  subgoal for l s
    apply (drule invariant)
    using reachable unfolding covered_def RE_def by fastforce
  subgoal for l s l' s'
    apply (drule invariant)
    unfolding RE_def covered_def using E_T by force
  subgoal
    using E_T by force
  subgoal
    unfolding RE_def using E_T by force
  subgoal
    unfolding Graph_Start_Defs.reachable_def
  proof -
    have 1: "finite {(l, s). l \<in> L \<and> s \<in> M l}"
    proof -
      let ?S = "{(l, s). l \<in> L \<and> s \<in> M l}"
      have "?S \<subseteq> (\<Union>l\<in>L. ((\<lambda> s. (l, s)) ` M l))"
        by auto
      also have "finite \<dots>"
        using finite by auto
      finally show "finite ?S" .
    qed
    have 2: "finite (Collect (E (l, s)))" for l s
      by (rule finitely_branching)
    let ?S = "{a. RE\<^sup>*\<^sup>* (l\<^sub>0, s\<^sub>0) a}"
    have "?S \<subseteq> {(l\<^sub>0, s\<^sub>0)} \<union> (\<Union> ((\<lambda> a. {b. E a b}) ` {(l, s). l \<in> L \<and> s \<in> M l}))"
      using invariant by (auto simp: RE_def elim: rtranclp.cases)
    also have "finite \<dots>"
      using 1 2 by auto
    finally show "finite ?S" .
  qed
  done

context
  assumes no_subsumption_cycle: "G'.reachable x \<Longrightarrow> x \<rightarrow>\<^sub>G\<^sup>+' x \<Longrightarrow> x \<rightarrow>\<^sub>G\<^sup>+ x"
  fixes F :: "'b \<times> 'a \<Rightarrow> bool" \<comment> \<open>Final states\<close>
  assumes F_mono[intro]: "F (l, a) \<Longrightarrow> a \<preceq> b \<Longrightarrow> F (l, b)"
begin

interpretation Liveness_Compatible_Subsumption_Graph
  "\<lambda> (l, s) (l', s'). l' = l \<and> s \<preceq> s'" "\<lambda> (l, s) (l', s'). l' = l \<and> s \<prec> s'"
  E "(l\<^sub>0, s\<^sub>0)" RE F
  by standard (auto intro: no_subsumption_cycle)

lemma
  "\<nexists> x. reachable x \<and> F x \<and> x \<rightarrow>\<^sup>+ x" if "\<nexists> x. G.reachable x \<and> F x \<and> x \<rightarrow>\<^sub>G\<^sup>+ x"
  using cycle_iff that by auto

lemma no_reachable_cycleI:
  "\<nexists> x. reachable x \<and> F x \<and> x \<rightarrow>\<^sup>+ x" if "\<nexists> x. G'.reachable x \<and> F x \<and> x \<rightarrow>\<^sub>G\<^sup>+ x"
  using that cycle_iff unfolding G_G'_reachable_iff[symmetric] by auto

text \<open>
  We can certify this by accepting a set of components and checking that:
  \<^item> there are no cycles in the component graph (including subsumption edges)
  \<^item> no non-trivial component contains a final state
  \<^item> no component contains an internal subsumption edge
\<close>

end (* Final states and liveness compatibility *)

end (* Reachability Invariant paired *)


subsection \<open>Certifying Cycle-Freeness with Graph Components\<close>
context
  fixes E1 E2 :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  fixes S :: "'a set set"
  fixes s\<^sub>0 :: 'a and a\<^sub>0 :: "'a set"
  assumes start: "s\<^sub>0 \<in> a\<^sub>0" "a\<^sub>0 \<in> S"
  assumes closed:
    "\<forall> a \<in> S. \<forall> x \<in> a. \<forall> y. E1 x y \<longrightarrow> (\<exists> b \<in> S. y \<in> b)"
    "\<forall> a \<in> S. \<forall> x \<in> a. \<forall> y. E2 x y \<longrightarrow> (\<exists> b \<in> S. y \<in> b)"
  assumes finite: "\<forall> a \<in> S. finite a"
begin

definition "E \<equiv> \<lambda> x y. E1 x y \<or> E2 x y"

definition "C \<equiv> \<lambda> a b. \<exists> x \<in> a. \<exists> y \<in> b. E x y \<and> b \<in> S"

interpretation E1: Graph_Start_Defs E1 s\<^sub>0 .
interpretation E2: Graph_Start_Defs E2 s\<^sub>0 .
interpretation E: Graph_Start_Defs E s\<^sub>0 .
interpretation C: Graph_Start_Defs C a\<^sub>0 .

lemma E_closed:
  "\<forall> a \<in> S. \<forall> x \<in> a. \<forall> y. E x y \<longrightarrow> (\<exists> b \<in> S. y \<in> b)"
  using closed unfolding E_def by auto

interpretation E_invariant: Graph_Invariant E "\<lambda> x. \<exists> a \<in> S. x \<in> a"
  using E_closed by - (standard, auto)

interpretation E1_invariant: Graph_Invariant E1 "\<lambda> x. \<exists> a \<in> S. x \<in> a"
  using closed by - (standard, auto)

interpretation E2_invariant: Graph_Invariant E2 "\<lambda> x. \<exists> a \<in> S. x \<in> a"
  using closed by - (standard, auto)

interpretation C_invariant: Graph_Invariant C "\<lambda> a. a \<in> S \<and> a \<noteq> {}"
  unfolding C_def by standard auto

interpretation Simulation_Invariant E C "(\<in>)" "\<lambda> x. \<exists> a \<in> S. x \<in> a" "\<lambda> a. a \<in> S \<and> a \<noteq> {}"
  unfolding C_def by (standard; blast dest: E_invariant.invariant[rotated])+

interpretation Subgraph E E1
  unfolding E_def by standard auto

context
  assumes no_internal_E2:  "\<forall> a \<in> S. \<forall> x \<in> a. \<forall> y \<in> a. \<not> E2 x y"
      and no_component_cycle: "\<forall> a \<in> S. \<nexists> b. (C.reachable a \<and> C a b \<and> C.reaches b a \<and> a \<noteq> b)"
begin

lemma E_C_reaches1:
  "C.reaches1 a b" if "E.reaches1 x y" "x \<in> a" "a \<in> S" "y \<in> b" "b \<in> S"
  using that
proof (induction arbitrary: b)
  case (base y)
  then have "C a b"
    unfolding C_def by auto
  then show ?case
    by auto
next
  case (step y z c)
  then obtain b where "y \<in> b" "b \<in> S"
    by (meson E_invariant.invariant_reaches tranclp_into_rtranclp)
  from step.IH[OF \<open>x \<in> a\<close> \<open>a \<in> S\<close> this] have "C.reaches1 a b" .
  moreover from step.prems \<open>E _ _\<close> \<open>y \<in> b\<close> \<open>b \<in> S\<close> have "C b c"
    unfolding C_def by auto
  finally show ?case .
qed

lemma certify_no_E1_cycle:
  assumes "E.reachable x" "E.reaches1 x x"
    shows "E1.reaches1 x x"
proof (rule ccontr)
  assume A: "\<not> E1.reaches1 x x"
  with \<open>E.reaches1 x x\<close> obtain y z where "E.reaches x y" "E2 y z" "E.reaches z x"
    by (fastforce dest!: non_subgraph_cycle_decomp simp: E_def)
  from start \<open>E.reachable x\<close> obtain a where [intro]: "C.reachable a" "x \<in> a" "a \<in> S"
    unfolding E.reachable_def C.reachable_def by (auto dest: simulation_reaches)
  with \<open>E.reaches x y\<close> obtain b where "C.reaches a b" "y \<in> b" "b \<in> S"
    by (auto dest: simulation_reaches)
  from \<open>C.reaches a b\<close> have "C.reachable b"
    by (blast intro: C.reachable_reaches)
  from \<open>E.reaches z x\<close> have \<open>E.reaches1 z x \<or> z = x\<close> 
    by (meson rtranclpD)
  then show False
  proof
    assume "E.reaches1 z x"
    from \<open>y \<in> b\<close> \<open>b \<in> S\<close> \<open>E2 y z\<close> obtain c where "C b c" \<open>z \<in> c\<close> \<open>c \<in> S\<close>
      using A_B_step[of y z b] unfolding E_def by (auto dest: C_invariant.invariant[rotated])
    with no_internal_E2 \<open>y \<in> _\<close> \<open>E2 y z\<close> have "b \<noteq> c"
      by auto
    with \<open>E2 y z\<close> \<open>y \<in> b\<close> \<open>z \<in> c\<close> \<open>c \<in> S\<close> have "C b c"
      unfolding C_def E_def by auto
    from \<open>E.reaches1 z x\<close> \<open>z \<in> c\<close> \<open>c \<in> S\<close> \<open>x \<in> a\<close> have "C.reaches1 c a"
      by (auto intro: E_C_reaches1)
    with \<open>C.reaches a b\<close> have "C.reaches1 c b"
      by auto
    then have "C.reaches c b"
      by auto
    with \<open>C b c\<close> \<open>b \<in> S\<close> \<open>C.reachable b\<close> \<open>b \<noteq> c\<close> no_component_cycle show False
      by auto
  next
    assume [simp]: "z = x"
    with \<open>y \<in> b\<close> \<open>E2 y z\<close> \<open>a \<in> S\<close> \<open>x \<in> a\<close> have "C b a"
      unfolding C_def E_def by auto
    with no_internal_E2 \<open>y \<in> _\<close> \<open>E2 y z\<close> have "b \<noteq> a"
      by auto
    with \<open>C.reaches a b\<close> \<open>C b a\<close> \<open>b \<in> S\<close> \<open>C.reachable b\<close> no_component_cycle show False
      by auto
  qed
qed

lemma certify_no_accepting_cycle:
  assumes
    "\<forall> a \<in> S. card a > 1 \<longrightarrow> (\<forall> x \<in> a. \<not> F x)"
    "\<forall> a \<in> S. \<forall> x. a = {x} \<longrightarrow> (\<not> F x \<or> \<not> E1 x x)"
  assumes "E.reachable x" "E1.reaches1 x x"
  shows "\<not> F x"
proof (rule ccontr, simp)
  assume "F x"
  from start \<open>E.reachable x\<close> obtain a where "x \<in> a" "a \<in> S" "C.reachable a"
    unfolding E.reachable_def C.reachable_def by (auto dest: simulation_reaches)
  consider "card a = 0" | "card a = 1" | "card a > 1"
    by force
  then show False
  proof cases
    assume "card a = 0"
    with finite \<open>x \<in> a\<close> \<open>a \<in> S\<close> show False
      by auto
  next
    assume "card a > 1"
    with \<open>x \<in> a\<close> \<open>a \<in> S\<close> assms(1) \<open>F x\<close> show False
      by auto
  next
    assume "card a = 1"
    with finite \<open>x \<in> a\<close> \<open>a \<in> S\<close> have "a = {x}"
      using card_1_singletonE by blast
    with \<open>a \<in> S\<close> assms(2) \<open>F x\<close> have "\<not> E1 x x"
      by auto
    from assms(4) show False
    proof (cases rule: converse_tranclpE, assumption, goal_cases)
      case 1
      with \<open>\<not> E1 x x\<close> show ?thesis
        by auto
    next
      case (2 y)
      interpret sim: Simulation E1 E "(=)"
        by (rule Subgraph_Simulation)
      from \<open>E1.reaches1 y x\<close> have "E.reaches1 y x"
        by (auto dest: sim.simulation_reaches1)
      from \<open>E1 x y\<close> \<open>\<not> E1 x x\<close> \<open>a = _\<close> \<open>x \<in> a\<close> \<open>a \<in> S\<close> obtain b where "y \<in> b" "b \<in> S" "C a b"
        by (meson C_def E_def closed(1))
      with \<open>a = _\<close> \<open>\<not> E1 x x\<close> \<open>E1 x y\<close> have "a \<noteq> b"
        by auto
      from \<open>y \<in> b\<close> \<open>b \<in> S\<close> \<open>E.reaches1 y x\<close> \<open>x \<in> a\<close> \<open>a \<in> S\<close> have "C.reaches1 b a"
        by (auto intro: E_C_reaches1)
      with \<open>x \<in> a\<close> \<open>a \<in> S\<close> \<open>C a b\<close> \<open>C.reachable a\<close> \<open>a \<noteq> b\<close> show ?thesis
        including graph_automation_aggressive using no_component_cycle by auto
    qed
  qed
qed

end (* Cycle-freeness *)

end (* Graph Components *)

end (* Theory *)