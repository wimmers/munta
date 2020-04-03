section \<open>Additions to Lars Noschinski's Graph Library\<close>
theory More_Graph_Theory
  imports "Graph_Theory.Graph_Theory"
begin

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

end


locale dag = wf_digraph +
  assumes acyclic: "x \<rightarrow>\<^sup>+ x \<Longrightarrow> False"

locale fin_dag = fin_digraph + dag


context wf_digraph
begin

interpretation scc_digraph: loopfree_digraph scc_graph
  by (rule scc_digraphI)

interpretation scc_digraph: dag scc_graph
  by standard (auto elim: scc_graph_reachable1E)

lemmas scc_digraphI = scc_digraph.dag_axioms

end


context fin_digraph
begin

interpretation scc_digraph: dag scc_graph
  thm scc_digraphI
  by (rule scc_digraphI)

interpretation scc_digraph: fin_dag scc_graph
  apply standard
  unfolding scc_graph_def
  subgoal finite_verts
    by (simp add: finite_sccs_verts)
  subgoal finite_arcs
    using finite_sccs_verts
    by - (rule finite_subset[where B = "{(x, y). x \<in> sccs_verts \<and> y \<in> sccs_verts}"], auto)
  done

lemmas scc_digraphI = scc_digraph.fin_dag_axioms

end

end