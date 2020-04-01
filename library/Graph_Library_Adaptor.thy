section \<open>Transferring Theorems Between Graph Libraries\<close>
theory Graph_Library_Adaptor
  imports Graphs "Graph_Theory.Graph_Theory" More_Methods
begin

no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open>From \<open>Graph_Theory\<close> to \<open>Graphs\<close>\<close>

context pre_digraph
begin

definition "E \<equiv> \<lambda>x y. (x, y) \<in> arcs_ends G"

interpretation Graph_Defs E .

lemma dominates_iff:
  "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> E u v"
  unfolding E_def by simp

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longleftrightarrow> reaches1 u v"
  unfolding tranclp_unfold E_def by simp

end

context wf_digraph
begin

interpretation Graph_Defs E .

lemma reachable_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> reaches u v" if "u \<in> verts G"
  apply (rule iffI)
  subgoal premises prems
    using prems unfolding reachable_def by induction (auto simp: dominates_iff)
  subgoal premises prems
    using prems by induction
      (auto 4 3 simp: that dominates_iff[symmetric] reachable_def intro: rtrancl_on_into_rtrancl_on)
  done

lemma vwalk_iff:
  "vwalk (u # xs) G \<longleftrightarrow> steps (u # xs)" if "u \<in> verts G"
  apply (rule iffI)
   apply (induction rule: vwalk_induct; auto simp: dominates_iff)
  subgoal premises prems
    using prems that by (induction "u # xs" arbitrary: u xs; simp add: adj_in_verts(2) dominates_iff)
  done

lemmas graph_convs1 = reachable_iff reachable1_iff vwalk_iff

end



subsection \<open>From \<open>Graphs\<close> to \<open>Graph_Theory\<close>\<close>

context Graph_Defs
begin

definition "G = \<lparr>verts = UNIV, arcs = {(a, b). E a b}, tail = fst, head = snd\<rparr>"

definition "G\<^sub>p = \<lparr>pverts = UNIV, parcs = {(a, b). E a b}\<rparr>"

lemma G_pair_conv:
  "with_proj G\<^sub>p = G"
  unfolding G\<^sub>p_def G_def with_proj_def by simp

sublocale digraph: nomulti_digraph G
  by standard (auto simp: G_def arc_to_ends_def)

sublocale pdigraph: pair_wf_digraph G\<^sub>p
  using G_pair_conv digraph.wf_digraph_axioms wf_digraph_wp_iff by metis

lemma arc_to_ends_eq[simp]:
  "arc_to_ends G = id"
  by (auto simp add: G_def arc_to_ends_def)

lemma arcs_ends_eq[simp]:
  "arcs_ends G = {(a, b). E a b}"
  unfolding arcs_ends_def arc_to_ends_eq by (simp add: G_def)

lemma dominates_iff[simp]:
  "u \<rightarrow>\<^bsub>G\<^esub> v \<longleftrightarrow> E u v"
  by simp

lemma verts_eq[simp]:
  "verts G = UNIV"
  unfolding G_def by simp

lemma reachable_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>* v"
  apply (simp only: reachable_def arcs_ends_eq verts_eq)
  apply (rule iffI)
  subgoal premises prems
    using prems by induction auto
  subgoal premises prems
    using prems by induction (auto intro: rtrancl_on_into_rtrancl_on)
  done

lemma pair_in_pair_set_iff:
  "(a, b) \<in> {(x, y). P x y} \<longleftrightarrow> P a b"
  by auto

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+ v"
  by (simp only: arcs_ends_eq pair_in_pair_set_iff tranclp_unfold)

lemma vwalk_iff:
  "vwalk xs G \<longleftrightarrow> steps xs"
  apply (rule iffI)
   apply (induction rule: vwalk_induct; auto)
  apply (induction rule: steps.induct; auto)
  done

lemmas graph_convs2 = reachable_iff reachable1_iff vwalk_iff

\<comment> \<open>Transferring a theorem (@{thm digraph.reachable_vpath_conv}):\<close>
lemma reachable_path_conv:
  "u \<rightarrow>* v \<longleftrightarrow> (\<exists>p. steps p \<and> distinct p \<and> hd p = u \<and> last p = v)"
  unfolding graph_convs2[symmetric] by (simp add: digraph.reachable_vpath_conv vpath_def)

end

context Subgraph_Defs
begin

definition "G' = \<lparr>verts = UNIV, arcs = {(a, b). E' a b}, tail = fst, head = snd\<rparr>"

definition "G\<^sub>p' = \<lparr>pverts = UNIV, parcs = {(a, b). E' a b}\<rparr>"

lemma G'_pair_conv:
  "with_proj G\<^sub>p' = G'"
  unfolding G\<^sub>p'_def G'_def with_proj_def by simp

sublocale digraph_sub: wf_digraph G'
  unfolding wf_digraph_def G'_def by simp

sublocale pdigraph_sub: pair_wf_digraph G\<^sub>p'
  using G'_pair_conv digraph_sub.wf_digraph_axioms wf_digraph_wp_iff by metis

lemma verts_eq[simp]:
  "verts G' = UNIV"
  unfolding G'_def by simp

end

context Subgraph
begin

lemma subgraph:
  "subgraph G' G.G"
  unfolding subgraph_def
  apply (intro conjI)
  subgoal
    by simp
  subgoal
    by (auto simp: G.G_def G'_def)
  subgoal
    by (simp add: G.digraph.wf_digraph_axioms)
  subgoal
    by (simp add: digraph_sub.wf_digraph_axioms)
  subgoal
    by (simp add: compatible_def G.G_def G'_def)
  done

lemma spanning:
  "spanning G' G.G"
  unfolding spanning_def by (simp add: subgraph)

lemma G'_eq:
  "G'.G = G'"
  by (auto simp: Graph_Defs.G_def G'_def)

lemmas subgraph_convs = G'.graph_convs2[unfolded G'_eq]

end

lemma (in Graph_Defs) reaches_steps_iff2:
  "x \<rightarrow>* y \<longleftrightarrow> (x = y \<or> (\<exists>vs. steps (x # vs @ [y])))"
  by (simp add: Nitpick.rtranclp_unfold reaches1_steps_iff)

lemma vwalkE2:
  assumes "vwalk p G"
  obtains u where "p = [u]" "u \<in> verts G"
    | u v es where "p = u # v # es" "(u,v) \<in> arcs_ends G" "vwalk (v # es) G"
  by (metis assms list.sel(1) vwalkE vwalk_consE vwalk_singleton vwalk_to_vpath.cases)

lemma (in wf_digraph) reachable_vwalk_conv2:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v \<longleftrightarrow> (u = v \<and> u \<in> verts G \<or> (\<exists>vs. vwalk (u # vs @ [v]) G))"
  unfolding reachable_vwalk_conv
  apply (rule iffI)
   apply (elim exE conjE, erule vwalkE2, (simp; fail),
      metis last.simps last_snoc list.distinct(1) list.sel(1) rev_exhaust vwalk_Cons_Cons)
  apply force
  done

context Subgraph_Node_Defs
begin

\<comment> \<open>Node-induced subgraph. Compare with @{term G'}.\<close>
definition "G\<^sub>n = \<lparr>verts = {x. V x}, arcs = {(a, b). E' a b}, tail = fst, head = snd\<rparr>"

sublocale digraph_nodes: wf_digraph G\<^sub>n
  unfolding wf_digraph_def G\<^sub>n_def E'_def by simp

lemma verts_eq[simp]:
  "verts G\<^sub>n = {x. V x}"
  unfolding G\<^sub>n_def by simp

lemma arcs_eq[simp]:
  "arcs G\<^sub>n = arcs G'"
  unfolding G\<^sub>n_def G'_def by simp

lemma subgraph_dominatesI:
  "a \<rightarrow>\<^bsub>G\<^sub>n\<^esub> b" if "a \<rightarrow> b" "V a" "V b"
  using that by (intro digraph_nodes.dominatesI) (auto simp: G\<^sub>n_def arc_to_ends_def E'_def)

lemma arcs_ends_eq:
  "arcs_ends G\<^sub>n = arcs_ends G'"
  unfolding G\<^sub>n_def G'_def E'_def arcs_ends_def arc_to_ends_def by simp

lemma subgraph_nodes':
  "subgraph G\<^sub>n G'"
  unfolding subgraph_def
  apply (intro conjI)
  subgoal
    by simp
  subgoal
    by simp
  subgoal
    by (simp add: digraph_sub.wf_digraph_axioms)
  subgoal
    by (simp add: digraph_nodes.wf_digraph_axioms)
  subgoal
    by (simp add: compatible_def G'_def G\<^sub>n_def)
  done

lemma subgraph_nodes:
  "subgraph G\<^sub>n G"
  by (rule subgraph_nodes' subgraph subgraph_trans)+

lemma induced_subgraph:
  "induced_subgraph G\<^sub>n G"
  unfolding induced_subgraph_def by (intro conjI subgraph_nodes) (auto simp: G\<^sub>n_def G_def E'_def)

\<comment> \<open>The notions of walks in the two versions of node-induced subgraphs are not equivalent
for empty paths, thus this is the only valid ``standard'' conversion theorem between paths:\<close>
lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^sub>n\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>G'\<^esub> v"
  unfolding arcs_ends_eq ..

lemma dominates_iff:
  "u \<rightarrow>\<^bsub>G\<^sub>n\<^esub> v \<longleftrightarrow> E' u v"
  unfolding G\<^sub>n_def arcs_ends_def arc_to_ends_def E'_def by simp
 
lemma subgraph_vwalk_iff:
  "vwalk (v # vs) G\<^sub>n \<longleftrightarrow> G'.steps (v # vs)" if "V v"
  apply (rule iffI)
   apply (induction rule: vwalk_induct; auto simp: dominates_iff; fail)
  subgoal premises prems
    using prems that
    by (induction "v # vs" arbitrary: v vs rule: G'.steps.induct; auto simp: dominates_iff E'_def)
  done

lemma subgraph_reaches_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^sub>n\<^esub> v \<longleftrightarrow> G'.reaches u v" if "V u"
  by (simp add: that G'.reaches_steps_iff2 digraph_nodes.reachable_vwalk_conv2 subgraph_vwalk_iff)

lemma subgraph_reaches1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^sub>n\<^esub> v \<longleftrightarrow> G'.reaches1 u v"
  unfolding reachable1_iff subgraph_convs ..

end


context Graph_Invariant
begin

sublocale Subgraph_Node_Defs where E = E and V = P .

lemma subgraph':
  assumes "x \<rightarrow> y" "P x"
  shows "E' x y"
  using assms by (intro subgraph') (auto intro: invariant)

lemma invariant_steps_iff:
  "G'.steps (v # vs) \<longleftrightarrow> steps (v # vs)" if "P v"
  apply (rule iffI)
  subgoal
    using G'.steps_alt_induct steps_appendI by blast
  subgoal premises prems
    using prems \<open>P v\<close> by (induction "v # vs" arbitrary: v vs) (auto intro: subgraph' invariant)
  done

lemma invariant_reaches_iff:
  "G'.reaches u v \<longleftrightarrow> reaches u v" if "P u"
  using that by (simp add: reaches_steps_iff2 G'.reaches_steps_iff2 invariant_steps_iff)

lemma invariant_reaches1_iff:
  "G'.reaches1 u v \<longleftrightarrow> reaches1 u v" if "P u"
  using that by (simp add: reaches1_steps_iff G'.reaches1_steps_iff invariant_steps_iff)

lemma reachable_iff:
  "u \<rightarrow>\<^sup>*\<^bsub>G\<^sub>n\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" if "P u"
  using that by (simp add: graph_convs2 subgraph_reaches_iff invariant_reaches_iff)

lemma reachable1_iff:
  "u \<rightarrow>\<^sup>+\<^bsub>G\<^sub>n\<^esub> v \<longleftrightarrow> u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v" if "P u"
  unfolding subgraph_reaches1_iff invariant_reaches1_iff[OF that] graph_convs2 ..

lemma vwalk_iff:
  "vwalk (u # vs) G\<^sub>n \<longleftrightarrow> vwalk (u # vs) G" if "P u"
  using that by (simp add: subgraph_vwalk_iff invariant_steps_iff graph_convs2)

end


locale DAG = Graph_Defs +
  assumes acyclic: "\<not> E\<^sup>+\<^sup>+ x x"
begin

lemma topological_numbering:
  fixes S assumes "finite S"
  shows "\<exists>f :: _ \<Rightarrow> nat. inj_on f S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. E x y \<longrightarrow> f x < f y)"
  using assms
proof (induction rule: finite_psubset_induct)
  case (psubset A)
  show ?case
  proof (cases "A = {}")
    case True
    then show ?thesis
      by simp
  next
    case False
    then obtain x where x: "x \<in> A" "\<forall>y \<in> A. \<not>E y x"
      using directed_graph_indegree_ge_1_cycle[OF \<open>finite A\<close>] acyclic by auto
    let ?A = "A - {x}"
    from \<open>x \<in> A\<close> have "?A \<subset> A"
      by auto
    from psubset.IH(1)[OF this] obtain f :: "_ \<Rightarrow> nat" where f:
      "inj_on f ?A" "\<forall>x\<in>?A. \<forall>y\<in>?A. x \<rightarrow> y \<longrightarrow> f x < f y"
      by blast
    let ?f = "\<lambda>y. if x \<noteq> y then f y + 1 else 0"
    from \<open>x \<in> A\<close> have "A = insert x ?A"
      by auto
    from \<open>inj_on f ?A\<close> have "inj_on ?f A"
      by (auto simp: inj_on_def)
    moreover from f(2) x(2) have "\<forall>x\<in>A. \<forall>y\<in>A. x \<rightarrow> y \<longrightarrow> ?f x < ?f y"
      by auto
    ultimately show ?thesis
      by blast
  qed
qed

end


context Graph_Defs
begin

definition "vertices = {x. \<exists>y. E x y \<or> E y x}"

lemma reaches1_verts:
  assumes "x \<rightarrow>\<^sup>+ y"
  shows "x \<in> vertices" and "y \<in> vertices"
  using assms reaches1_reaches_iff2 reaches1_reaches_iff1 vertices_def by blast+

end

locale Finite_Graph = Graph_Defs +
  assumes finite_graph: "finite vertices"

locale Finite_DAG = Finite_Graph + DAG
begin

lemma finite_reachable:
  "finite {y. x \<rightarrow>* y}" (is "finite ?S")
proof -
  have "?S \<subseteq> insert x vertices"
    by (metis insertCI mem_Collect_eq reaches1_verts(2) rtranclpD subsetI)
  also from finite_graph have "finite \<dots>" ..
  finally show ?thesis .
qed

end

locale dag = wf_digraph +
  assumes acyclic: "x \<rightarrow>\<^sup>+ x \<Longrightarrow> False"
begin

sublocale graph: DAG E
  by standard (auto simp: graph_convs1 intro: acyclic)

lemma topological_numbering:
  fixes S assumes "finite S"
  shows "\<exists>f :: _ \<Rightarrow> nat. inj_on f S \<and> (\<forall>x \<in> S. \<forall>y \<in> S. x \<rightarrow> y \<longrightarrow> f x < f y)"
  using graph.topological_numbering[OF assms] unfolding dominates_iff .

end

context fin_digraph
begin

sublocale graph: Finite_Graph E
  by standard (auto intro!: finite_subset[OF _ finite_verts] simp: E_def Graph_Defs.vertices_def)

end

locale fin_dag = fin_digraph + dag
begin

sublocale graph: Finite_DAG E ..

end

context pre_digraph
begin

definition
  "scc_graph = \<lparr>
    verts = sccs_verts,
    arcs = {(x, y). \<exists>a \<in> x. \<exists>b \<in> y. x \<noteq> y \<and> x \<in> sccs_verts \<and> y \<in> sccs_verts \<and> a \<rightarrow> b},
    tail = fst,
    head = snd
  \<rparr>"

interpretation scc_digraph: loopfree_digraph scc_graph
  by standard (auto simp: scc_graph_def)

lemmas scc_digraphI = scc_digraph.loopfree_digraph_axioms

end

context wf_digraph
begin

interpretation scc_digraph: loopfree_digraph scc_graph
  by (rule scc_digraphI)

lemma scc_graph_edgeE:
  assumes \<open>x \<rightarrow>\<^bsub>scc_graph\<^esub> y\<close> obtains a b where
    "a \<in> x" "b \<in> y" "a \<rightarrow> b" "x \<in> sccs_verts" "y \<in> sccs_verts" "x \<noteq> y"
    using assms by (force simp: scc_graph_def dest!: in_arcs_imp_in_arcs_ends)

lemma same_sccI:
  assumes "S \<in> sccs_verts" "x \<in> S" "x \<rightarrow>\<^sup>* y" "y \<rightarrow>\<^sup>* x"
  shows "y \<in> S"
  using assms by (auto simp: in_sccs_verts_conv_reachable)

lemma scc_graph_reachable1E:
  assumes \<open>x \<rightarrow>\<^sup>+\<^bsub>scc_graph\<^esub> y\<close> obtains a b where
    "x \<in> sccs_verts " "y \<in> sccs_verts " "x \<noteq> y" "a \<in> x" "b \<in> y" "a \<rightarrow>\<^sup>+ b"
  using assms
proof (atomize_elim, induction)
  case (base y)
  then show ?case
    by (auto elim!: scc_graph_edgeE)
next
  case (step y z)
  then obtain a b where IH: "x \<in> sccs_verts" "y \<in> sccs_verts" "a \<in> x" "b \<in> y" "a \<rightarrow>\<^sup>+ b" "x \<noteq> y"
    by auto
  from \<open>y \<rightarrow>\<^bsub>scc_graph\<^esub> z\<close> obtain b' c where *:
    "b' \<in> y" "c \<in> z" "b' \<rightarrow> c" "y \<in> sccs_verts" "z \<in> sccs_verts"
    by (elim scc_graph_edgeE)
  with \<open>b \<in> y\<close> have "b \<rightarrow>\<^sup>* b'"
    by (simp add: in_sccs_verts_conv_reachable)
  with \<open>b' \<rightarrow> c\<close> \<open>a \<rightarrow>\<^sup>+ b\<close> have "a \<rightarrow>\<^sup>+ c"
    using reachable1_reachable_trans by blast
  moreover have "x \<noteq> z"
  proof (rule ccontr, simp)
    assume "x = z"
    with \<open>a \<in> x\<close> \<open>c \<in> z\<close> \<open>x \<in> _\<close> have "c \<rightarrow>\<^sup>* a"
      by (simp add: in_sccs_verts_conv_reachable)
    with \<open>b \<rightarrow>\<^sup>* b'\<close> \<open>b' \<rightarrow> c\<close> have "b \<rightarrow>\<^sup>* a" \<comment> \<open>XXX: This should really be \<open>by simp\<close>\<close>
      by (meson reachable_adj_trans reachable_trans)
    with IH have "b \<in> x"
      by - (rule same_sccI, auto)
    with sccs_verts_disjoint IH show False
      by auto
  qed
  ultimately show ?case
    using IH * by auto
qed

interpretation scc_digraph: dag scc_graph
  by standard (auto elim: scc_graph_reachable1E)

lemmas scc_digraphI = scc_digraph.dag_axioms

end

context fin_digraph
begin

interpretation scc_digraph: dag scc_graph
  by (rule scc_digraphI)

interpretation scc_digraph: fin_dag scc_graph
  apply standard
  unfolding scc_graph_def
  subgoal finite_verts
    by (simp add: finite_sccs_verts)
  subgoal finite_arcs
    using finite_sccs_verts by defer_ex (auto simp: Collect_case_prod_Sigma)
  done

lemmas scc_digraphI = scc_digraph.fin_dag_axioms

definition
  "scc_num \<equiv> SOME f :: (_ \<Rightarrow> nat).
    inj_on f sccs_verts \<and> (\<forall>x\<in>sccs_verts. \<forall>y\<in>sccs_verts. x \<rightarrow>\<^bsub>scc_graph\<^esub> y \<longrightarrow> f x < f y)"

lemma
  shows scc_num_inj: "inj_on scc_num sccs_verts" (is ?thesis1)
    and scc_num_topological:
    "\<forall>x\<in>sccs_verts. \<forall>y\<in>sccs_verts. x \<rightarrow>\<^bsub>scc_graph\<^esub> y \<longrightarrow> scc_num x < scc_num y" (is ?thesis2)
proof -
  from scc_digraph.topological_numbering[OF finite_sccs_verts] have "?thesis1 \<and> ?thesis2"
    unfolding scc_num_def by (rule someI_ex)
  then show ?thesis1 and ?thesis2
    by auto
qed

end

context Finite_Graph
begin

interpretation Graph_Invariant
  where E = E and P = "\<lambda>x. x \<in> vertices"
  by standard (auto simp: vertices_def)

interpretation digraph_nodes: fin_digraph G\<^sub>n
  apply standard
  subgoal finite_verts
    by (simp add: Subgraph_Node_Defs.G\<^sub>n_def finite_graph)
  subgoal
    by (rule finite_subset[where B = "verts G\<^sub>n \<times> verts G\<^sub>n"])
       (auto simp: G'_def E'_def G\<^sub>n_def finite_graph)
  done

definition
  "is_max_scc S \<equiv>
  S \<subseteq> vertices \<and> S \<noteq> {} \<and> (\<forall>u \<in> S. \<forall>v \<in> S. u \<rightarrow>* v) \<and> (\<forall>u \<in> S. \<forall>v. v \<notin> S \<longrightarrow> \<not>u \<rightarrow>* v \<or> \<not>v \<rightarrow>* u)"

lemma is_max_scc_iff:
  "is_max_scc S \<longleftrightarrow> S \<in> digraph_nodes.sccs_verts"
proof (rule iffI)
  assume "is_max_scc S"
  then show "S \<in> digraph_nodes.sccs_verts"
    unfolding is_max_scc_def digraph_nodes.sccs_verts_def
    by (clarsimp, safe) (auto simp: reachable_iff graph_convs2 invariant_reaches)
next
  assume "S \<in> digraph_nodes.sccs_verts"
  then have "S \<subseteq> vertices"
    using digraph_nodes.sccs_verts_subsets by auto
  then show "is_max_scc S"
    using \<open>S \<in> _\<close> unfolding is_max_scc_def digraph_nodes.sccs_verts_def
    by (auto simp: Graph_Defs.reachable_iff in_mono invariant_reaches reachable_iff)
qed

lemma max_sccI:
  assumes "a \<in> vertices"
  obtains A where "is_max_scc A" "a \<in> A"
  subgoal premises that
    using assms
    by (intro that[of "{b. a \<rightarrow>* b \<and> b \<rightarrow>* a}"])
       (auto intro: invariant_reaches simp: is_max_scc_def, (meson rtranclp_trans)+)
       \<comment> \<open>XXX: graph automation\<close>
  done

lemma is_max_scc_disjoint:
  assumes "is_max_scc V" "is_max_scc W" "V \<noteq> W"
  shows "V \<inter> W = {}"
  using assms unfolding is_max_scc_iff by (rule digraph_nodes.sccs_verts_disjoint)

definition
  "edge V W \<equiv> \<exists>a \<in> V. \<exists>b \<in> W. V \<noteq> W \<and> E a b"

definition
  "scc_num \<equiv> SOME f :: (_ \<Rightarrow> nat).
    inj_on f {V. is_max_scc V} \<and> (\<forall>V. \<forall>W. is_max_scc V \<and> is_max_scc W \<and> edge V W \<longrightarrow> f V < f W)"

interpretation scc_digraph: fin_dag digraph_nodes.scc_graph
  by (rule digraph_nodes.scc_digraphI)

lemma edge_iff:
  "edge x y \<longleftrightarrow> x \<rightarrow>\<^bsub>digraph_nodes.scc_graph\<^esub> y"
  if "x \<in> digraph_nodes.sccs_verts" "y \<in> digraph_nodes.sccs_verts"
  unfolding edge_def
  apply rule
  subgoal
    using that unfolding digraph_nodes.scc_graph_def arcs_ends_def arc_to_ends_def
    unfolding G\<^sub>n_def G'_def E'_def by (auto simp add: vertices_def)
  using subgraph_nodes
  by (auto 4 3 dest!: digraph.adj_mono[rotated] elim!: digraph_nodes.scc_graph_edgeE)

lemma
  shows scc_num_inj: "inj_on scc_num {V. is_max_scc V}" (is ?thesis1)
    and scc_num_topological:
    "\<forall>V. \<forall>W. is_max_scc V \<and> is_max_scc W \<and> edge V W \<longrightarrow> scc_num V < scc_num W" (is ?thesis2)
proof -
  let ?P = "\<lambda>f :: (_ \<Rightarrow> nat).
    inj_on f {V. is_max_scc V} \<and> (\<forall>V. \<forall>W. is_max_scc V \<and> is_max_scc W \<and> edge V W \<longrightarrow> f V < f W)"
  from digraph_nodes.scc_num_inj digraph_nodes.scc_num_topological have "?thesis1 \<and> ?thesis2"
    unfolding scc_num_def by - (rule someI[where P = ?P], auto simp: is_max_scc_iff edge_iff)
  then show ?thesis1 and ?thesis2
    by auto
qed

end

end