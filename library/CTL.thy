theory CTL
  imports Graphs
begin

context Graph_Defs
begin

definition
  "Alw_ev \<phi> x \<equiv> \<forall> xs. run (x ## xs) \<longrightarrow> ev (holds \<phi>) (x ## xs)"

definition
  "Alw_alw \<phi> x \<equiv> \<forall> xs. run (x ## xs) \<longrightarrow> alw (holds \<phi>) (x ## xs)"

definition
  "Ex_ev \<phi> x \<equiv> \<exists> xs. run (x ## xs) \<and> ev (holds \<phi>) (x ## xs)"

definition
  "Ex_alw \<phi> x \<equiv> \<exists> xs. run (x ## xs) \<and> alw (holds \<phi>) (x ## xs)"

definition
  "leadsto \<phi> \<psi> x \<equiv> Alw_alw (\<lambda> x. \<phi> x \<longrightarrow> Alw_ev \<psi> x) x"

definition
  "deadlocked x \<equiv> \<not> (\<exists> y. x \<rightarrow> y)"

definition
  "deadlock x \<equiv> \<exists> y. reaches x y \<and> deadlocked y"

lemma no_deadlockD:
  "\<not> deadlocked y" if "\<not> deadlock x" "reaches x y"
  using that unfolding deadlock_def by auto

lemma not_deadlockedE:
  assumes "\<not> deadlocked x"
  obtains y where "x \<rightarrow> y"
  using assms unfolding deadlocked_def by auto

lemma holds_Not:
  "holds (Not \<circ> \<phi>) = (\<lambda> x. \<not> holds \<phi> x)"
  by auto

lemma Alw_alw_iff:
  "Alw_alw \<phi> x \<longleftrightarrow> \<not> Ex_ev (Not o \<phi>) x"
  unfolding Alw_alw_def Ex_ev_def holds_Not not_ev_not[symmetric] by simp

lemma Ex_alw_iff:
  "Ex_alw \<phi> x \<longleftrightarrow> \<not> Alw_ev (Not o \<phi>) x"
  unfolding Alw_ev_def Ex_alw_def holds_Not not_ev_not[symmetric] by simp

lemma leadsto_iff:
  "leadsto \<phi> \<psi> x \<longleftrightarrow> \<not> Ex_ev (\<lambda> x. \<phi> x \<and> \<not> Alw_ev \<psi> x) x"
  unfolding leadsto_def Alw_alw_iff by (simp add: comp_def)

lemma run_siterate_from:
  assumes "\<forall>y. x \<rightarrow>* y \<longrightarrow> (\<exists> z. y \<rightarrow> z)"
  shows "run (siterate (\<lambda> x. SOME y. x \<rightarrow> y) x)" (is "run (siterate ?f x)")
  using assms
proof (coinduction arbitrary: x)
  case (run x)
  let ?y = "SOME y. x \<rightarrow> y"
  from run have "x \<rightarrow> ?y"
    by (auto intro: someI)
  with run show ?case including graph_automation_aggressive by auto
qed

(* XXX Move *)
lemma extend_run':
  "run zs" if "steps xs" "run ys" "last xs = shd ys" "xs @- stl ys = zs"
  (* s/h *)
  by (metis
      Graph_Defs.run.cases Graph_Defs.steps_non_empty' extend_run
      stream.exhaust_sel stream.inject that)

lemma no_deadlock_run_extend:
  "\<exists> ys. run (x ## xs @- ys)" if "\<not> deadlock x" "steps (x # xs)"
proof -
  include graph_automation
  let ?x = "last (x # xs)" let ?f = "\<lambda> x. SOME y. x \<rightarrow> y" let ?ys = "siterate ?f ?x"
  have "\<exists>z. y \<rightarrow> z" if "?x \<rightarrow>* y" for y
  proof -
    from \<open>steps (x # xs)\<close> have "x \<rightarrow>* ?x"
    by auto
    from \<open>x \<rightarrow>* ?x\<close> \<open>?x \<rightarrow>* y\<close> have "x \<rightarrow>* y"
      by auto
    with \<open>\<not> deadlock x\<close> show ?thesis
      by (auto dest: no_deadlockD elim: not_deadlockedE)
  qed
  then have "run ?ys"
    by (blast intro: run_siterate_from)
  with \<open>steps (x # xs)\<close> show ?thesis
    by (fastforce intro: extend_run')
qed

lemma Ex_ev:
  "Ex_ev \<phi> x \<longleftrightarrow> (\<exists> y. x \<rightarrow>* y \<and> \<phi> y)" if "\<not> deadlock x"
  unfolding Ex_ev_def
proof safe
  fix xs assume prems: "run (x ## xs)" "ev (holds \<phi>) (x ## xs)"
  show "\<exists>y. x \<rightarrow>* y \<and> \<phi> y"
  proof (cases "\<phi> x")
    case True
    then show ?thesis
      by auto
  next
    case False
    with prems obtain y ys zs where
      "\<phi> y" "xs = ys @- y ## zs" "y \<notin> set ys"
      unfolding ev_holds_sset by (auto elim!:split_stream_first)
    with prems have "steps (x # ys @ [y])"
      by (auto intro: run_decomp[THEN conjunct1]) (* XXX *)
    with \<open>\<phi> y\<close> show ?thesis
      including graph_automation by (auto 4 3)
  qed
next
  fix y assume "x \<rightarrow>* y" "\<phi> y"
  then obtain xs where
    "\<phi> (last xs)" "x = hd xs" "steps xs" "y = last xs"
    by (auto dest: reaches_steps)
  then show "\<exists>xs. run (x ## xs) \<and> ev (holds \<phi>) (x ## xs)"
    by (cases xs)
       (auto split: if_split_asm simp: ev_holds_sset dest!: no_deadlock_run_extend[OF that])
qed

lemma Alw_ev:
  "Alw_ev \<phi> x \<longleftrightarrow> \<not> (\<exists> xs. run (x ## xs) \<and> alw (holds (Not o \<phi>)) (x ## xs))"
  unfolding Alw_ev_def
proof (safe, goal_cases)
  case prems: (1 xs)
  then have "ev (holds \<phi>) (x ## xs)" by auto
  then show ?case
    using prems(2,3) by induction (auto intro: run_stl)
next
  case prems: (2 xs)
  then have "\<not> alw (holds (Not \<circ> \<phi>)) (x ## xs)"
    by auto
  moreover have "(\<lambda> x. \<not> holds (Not \<circ> \<phi>) x) = holds \<phi>"
    by (rule ext) simp
  ultimately show ?case
    unfolding not_alw_iff by simp
qed

lemma leadsto_iff':
  "leadsto \<phi> \<psi> x \<longleftrightarrow> (\<nexists>y. x \<rightarrow>* y \<and> \<phi> y \<and> \<not> Alw_ev \<psi> y)" if "\<not> deadlock x"
  unfolding leadsto_iff Ex_ev[OF \<open>\<not> deadlock x\<close>] ..

end (* Graph Defs *)

end (* Theory *)