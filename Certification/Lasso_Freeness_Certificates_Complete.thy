theory Lasso_Freeness_Certificates_Complete
  imports Main "HOL-Library.Countable" "../library/Graph_Library_Adaptor"
begin

text \<open>
  This theory gives two valid ways of generating a certificate that proves that the given
  graph does not contain an accepting lasso.
\<close>

locale Contract_Downward =
  fixes E :: "'a :: countable \<Rightarrow> 'a \<Rightarrow> bool" and F :: "'a \<Rightarrow> bool"
  fixes f :: "'a \<Rightarrow> nat"
  assumes f_topo: "E a b \<Longrightarrow> if F a then f a > f b else f a \<ge> f b"
begin

lemma f_downward:
  assumes "E a b"
  shows "f a \<ge> f b"
  using assms f_topo by (cases "F a") (auto simp: less_imp_le)

lemma f_strict:
  assumes "E a b" "F a"
  shows "f a > f b"
  using assms f_topo by (auto simp: less_imp_le)

text \<open>We do not even need this property any more.\<close>
lemma no_trivial_lasso:
  assumes "F a" "E a a"
  shows False
  using assms f_topo by (meson less_irrefl)

lemma reaches_f_mono:
  assumes "E\<^sup>*\<^sup>* a b"
  shows "f a \<ge> f b"
  using assms by induction (auto intro: f_downward order.trans)

lemma no_accepting_cycle:
  assumes "E\<^sup>+\<^sup>+ x x"
  shows "\<not> F x"
proof (rule ccontr, simp)
  assume "F x"
  from \<open>E\<^sup>+\<^sup>+ x x\<close> obtain y where "E x y" "E\<^sup>*\<^sup>* y x"
    including graph_automation_aggressive by auto
  from \<open>E x y\<close> \<open>F x\<close> have "f x > f y"
    by (rule f_strict)
  moreover from \<open>E\<^sup>*\<^sup>* y x\<close> have "f y \<ge> f x"
    by (rule reaches_f_mono)
  ultimately show False
    by simp
qed

sublocale Graph_Defs .

lemma run_f_mono:
  assumes "run (x ## xs)" "c \<ge> f x"
  shows "pred_stream (\<lambda>a. c \<ge> f a) xs"
  using assms
  by (coinduction arbitrary: x xs) (metis f_downward order.trans run.cases stream.inject)

lemma no_Buechi_run:
  assumes "run xs" "infs F xs"
  shows False
proof -
  let ?S = "f ` sset xs" let ?T = "f ` sset (sfilter F xs)"
  obtain x ys where "xs = x ## ys"
    by (cases xs)
  let ?ub = "f x"
  from \<open>run xs\<close> have "run ys" "f (shd ys) \<le> ?ub"
    unfolding \<open>xs = _\<close> by (force elim: run.cases dest: f_downward)+
  then have "pred_stream (\<lambda>x. f x \<le> ?ub) ys"
    by (coinduction arbitrary: ys) (fastforce elim: run.cases dest: f_downward intro: order.trans)
  then have "finite ?S"
    unfolding stream.pred_set \<open>xs = _\<close> finite_nat_set_iff_bounded_le by auto
  from \<open>run xs\<close> \<open>infs F xs\<close> have "sdistinct (smap f (sfilter F xs))"
  proof (coinduction arbitrary: xs)
    case (sdistinct x xs ys)
    obtain y xs' where [simp]: "xs = y ## xs'"
      by (cases xs)
    obtain as bs x' y' ys' where eqs:
      "F x'" "F y'" "x = f x'" "y = f y'"
      "ys = as @- x' ## bs @- y' ## ys'" "xs' = smap f (sfilter F ys')"
      "list_all (Not o F) as" "list_all (Not o F) bs"
    proof (atomize_elim, goal_cases)
      case 1
      from sdistinct have "ev (holds F) ys"
        by auto
      from \<open>x ## xs = _\<close> have "x ## y ## xs' = smap f (sfilter F ys)"
        by simp
      then obtain x' y' ys' where "x = f x'" "y = f y'" "sfilter F ys = x' ## y' ## ys'" 
        "xs' = smap f ys'"
        apply atomize_elim
        unfolding scons_eq_smap
        apply (elim conjE)
        apply (intro exI conjI)
          apply assumption+
        apply (subst stream.collapse)+
        ..
      with \<open>ev (holds F) ys\<close> show ?case
        apply -
        apply (drule (1) sfilter_SCons_decomp)
        apply (elim conjE exE)
        apply (drule sfilter_SCons_decomp, metis alw.cases alw_shift sdistinct(3) stream.sel(2))
        by force
    qed
    have "run (y' ## ys')"
      using \<open>run ys\<close> unfolding \<open>ys = _\<close> (* XXX This should be solved by automation *)
      by (metis alw.cases alw_iff_sdrop alw_shift run_sdrop stream.sel(2))
    from eqs \<open>run ys\<close> have "steps (as @ x' # bs @ [y'])"
      by (simp add: run_decomp)
    then have "steps (x' # bs @ [y'])"
      using steps_appendD2 by blast
    then have "E\<^sup>+\<^sup>+ x' y'"
      using steps_reaches1 by blast
    with \<open>F x'\<close> have "f x' > f y'"
      using f_strict reaches1_reaches_iff1 reaches_f_mono by fastforce
    moreover have "pred_stream (\<lambda>a. f y' \<ge> f a) ys'"
      by (rule run_f_mono[where c = "f y'"]) (auto intro: \<open>run (y' ## ys')\<close>)
    ultimately have "x \<notin> f ` sset ys'"
      unfolding stream.pred_set eqs by auto
    from \<open>infs F ys\<close> have "infs F ys'"
      unfolding eqs by auto
    then have "sset (sfilter F ys') \<subseteq> sset ys'"
      by (rule sset_sfilter)
    with \<open>x \<notin> _\<close> \<open>f x' > f y'\<close> have "x \<notin> sset xs"
      unfolding stream.pred_set eqs \<open>xs = _\<close> by auto
    with \<open>run (y' ## ys')\<close> \<open>infs F ys'\<close> eqs \<open>xs' = _\<close> show ?case
      by - (safe, rule exI[where x = "y'##ys'"], auto)
  qed
  then have "infinite ?T"
    by - (drule sdistinct_infinite_sset, simp)
  moreover have "?T \<subseteq> ?S"
    by (rule image_mono sset_sfilter assms)+
  ultimately show ?thesis
    using \<open>finite ?S\<close> finite_subset by auto
qed

end (* Fixed numbering *)

context
  fixes E :: "'a :: countable \<Rightarrow> 'a \<Rightarrow> bool" and F :: "'a \<Rightarrow> bool"
begin

context
  fixes f :: "'a \<Rightarrow> nat"
  assumes f_topo: "E a b \<Longrightarrow> if F a then f a < f b else f a \<le> f b"
begin

lemma f_forward:
  assumes "E a b"
  shows "f a \<le> f b"
  using assms f_topo by (cases "F a") (auto simp: less_imp_le)

lemma f_strict:
  assumes "E a b" "F a"
  shows "f a < f b"
  using assms f_topo by (auto simp: less_imp_le)

text \<open>We do not even need this property any more.\<close>
lemma no_trivial_lasso:
  assumes "F a" "E a a"
  shows False
  using assms f_topo by (meson less_irrefl)

lemma reaches_f_mono:
  assumes "E\<^sup>*\<^sup>* a b"
  shows "f a \<le> f b"
  using assms by induction (auto intro: f_forward order.trans)

lemma no_accepting_cycle:
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

end (* Fixed numbering *)

context
  assumes no_accepting_cycle: "E\<^sup>+\<^sup>+ x x \<Longrightarrow> \<not> F x"
begin

definition
  "reach x \<equiv> card {y. F y \<and> E\<^sup>*\<^sup>* x y}"

context
  assumes finite: "finite {y. E\<^sup>*\<^sup>* x y}"
begin

lemma reach_mono:
  assumes "E x y"
  shows "reach x \<ge> reach y"
  using assms unfolding reach_def by (intro card_mono finite_subset[OF _ finite]) auto

lemma reach_strict:
  assumes "E x y" "F x"
  shows "reach x > reach y"
  using assms unfolding reach_def
  apply (intro psubset_card_mono finite_subset[OF _ finite])
  apply auto
  subgoal premises prems
  proof -
    from prems have "E\<^sup>*\<^sup>* y x"
      by auto
    with \<open>E x y\<close> have "E\<^sup>+\<^sup>+ x x"
      by auto
    with \<open>F x\<close> no_accepting_cycle show False
      by auto
  qed
  done

end (* Finite reachable set *)

end

end

context Finite_Graph
begin

context
  assumes no_accepting_cycle: "E\<^sup>+\<^sup>+ x x \<Longrightarrow> \<not> F x"
begin

private definition
  "f x \<equiv> scc_num (THE V. is_max_scc V \<and> x \<in> V)"

lemma f_topo:
  assumes "E a b"
  shows "if F a then f a < f b else f a \<le> f b"
proof -
  from assms obtain A where A: "is_max_scc A" "a \<in> A"
    by - (rule max_sccI, auto simp: vertices_def)
  from assms obtain B where B: "is_max_scc B" "b \<in> B"
    by - (rule max_sccI[where a = b], auto simp: vertices_def)
  from A B have [simp]: "f a = scc_num A" "f b = scc_num B"
    unfolding f_def using is_max_scc_disjoint
    by (intro arg_cong[where f = scc_num] the_equality, auto)+
  have "f a \<le> f b"
  proof (cases "A = B")
    case True
    then show ?thesis
      by simp
  next
    case False
    with \<open>E a b\<close> \<open>a \<in> A\<close> \<open>b \<in> B\<close> have "edge A B"
      unfolding edge_def by auto
    then have "f a < f b"
      using A B scc_num_topological by simp
    then show ?thesis
      by simp
  qed
  moreover have "f a \<noteq> f b" if "F a"
  proof (rule ccontr)
    assume "\<not> f a \<noteq> f b"
    with A B have "A = B"
      using scc_num_inj unfolding inj_on_def by simp
    with A \<open>b \<in> B\<close> have "E\<^sup>*\<^sup>* b a"
      unfolding is_max_scc_def by auto
    with \<open>E a b\<close> have "E\<^sup>+\<^sup>+ a a"
      by auto
    with \<open>F a\<close> no_accepting_cycle show False
      by auto
  qed
  ultimately show ?thesis
    by auto
qed

end (* No accepting cycle *)

end (* Fixed graph & final state predicate *)

end