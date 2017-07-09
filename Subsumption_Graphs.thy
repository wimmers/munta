theory Subsumption_Graphs
  imports
    "library/Graphs"
    "library/More_List"
begin

chapter \<open>Subsumption Graphs\<close>

section \<open>Preliminaries\<close>

subsection \<open>Transitive Closure\<close>

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes R_trans[intro]: "\<And> x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
begin

lemma rtranclp_transitive_compress1: "R a c" if "R a b" "R\<^sup>*\<^sup>* b c"
  using that(2,1) by induction auto

lemma rtranclp_transitive_compress2: "R a c" if "R\<^sup>*\<^sup>* a b" "R b c"
  using that by induction auto

end (* Transitivity *)

(* XXX Move *)
lemma rtranclp_ev_induct[consumes 1, case_names irrefl trans step]:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes reachable_finite: "finite {x. R\<^sup>*\<^sup>* a x}"
  assumes R_irrefl: "\<And> x. \<not> R x x" and R_trans[intro]: "\<And> x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  assumes step: "\<And> x. R\<^sup>*\<^sup>* a x \<Longrightarrow> P x \<or> (\<exists> y. R x y)"
  shows "\<exists> x. P x \<and> R\<^sup>*\<^sup>* a x"
proof -
  let ?S = "{y. R\<^sup>*\<^sup>* a y}"
  from reachable_finite have "finite ?S"
    by auto
  then have "\<exists> x \<in> ?S. P x"
    using step
  proof (induction ?S arbitrary: a rule: finite_psubset_induct)
    case psubset
    let ?S = "{y. R\<^sup>*\<^sup>* a y}"
    from psubset have "finite ?S" by auto
    show ?case
    proof (cases "?S = {}")
      case True
      then show ?thesis by auto
    next
      case False
      then obtain y where "R\<^sup>*\<^sup>* a y"
        by auto
      from psubset(3)[OF this] show ?thesis
      proof
        assume "P y"
        with \<open>R\<^sup>*\<^sup>* a y\<close> show ?thesis by auto
      next
        assume "\<exists> z. R y z"
        then obtain z where "R y z" by safe
        let ?T = "{y. R\<^sup>*\<^sup>* z y}"
        from \<open>R y z\<close> \<open>R\<^sup>*\<^sup>* a y\<close> have "\<not> R\<^sup>*\<^sup>* z a"
          by (auto simp: R_irrefl dest!: rtranclp_transitive_compress2[of R, rotated])
        then have "a \<notin> ?T" by auto
        moreover have "?T \<subseteq> ?S"
          using \<open>R\<^sup>*\<^sup>* a y\<close> \<open>R y z\<close> by auto
        ultimately have "?T \<subset> ?S"
          by auto
        have "P x \<or> Ex (R x)" if "R\<^sup>*\<^sup>* z x" for x
          using that \<open>R y z\<close> \<open>R\<^sup>*\<^sup>* a y\<close> by (auto intro!: psubset.prems)
        from psubset.hyps(2)[OF \<open>?T \<subset> ?S\<close> this] psubset.prems \<open>R y z\<close> \<open>R\<^sup>*\<^sup>* a y\<close> obtain w
          where "R\<^sup>*\<^sup>* z w" "P w" by auto
        with \<open>R\<^sup>*\<^sup>* a y\<close> \<open>R y z\<close> have "R\<^sup>*\<^sup>* a w" by auto
        with \<open>P w\<close> show ?thesis by auto
      qed
    qed
  qed
  then show ?thesis by auto
qed

(* XXX Move *)
lemma rtranclp_ev_induct2[consumes 2, case_names irrefl trans step]:
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes Q_finite: "finite {x. Q x}" and Q_witness: "Q a"
  assumes R_irrefl: "\<And> x. \<not> R x x" and R_trans[intro]: "\<And> x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
  assumes step: "\<And> x. Q x \<Longrightarrow> P x \<or> (\<exists> y. R x y \<and> Q y)"
  shows "\<exists> x. P x \<and> Q x \<and> R\<^sup>*\<^sup>* a x"
proof -
  let ?R = "\<lambda> x y. R x y \<and> Q x \<and> Q y"
  have [intro]: "R\<^sup>*\<^sup>* a x" if "?R\<^sup>*\<^sup>* a x" for x
    using that by induction auto
  have [intro]: "Q x" if "?R\<^sup>*\<^sup>* a x" for x
    using that \<open>Q a\<close> by (auto elim: rtranclp.cases)
  have "{x. ?R\<^sup>*\<^sup>* a x} \<subseteq> {x. Q x}" by auto
  with \<open>finite _\<close> have "finite {x. ?R\<^sup>*\<^sup>* a x}" by - (rule finite_subset)
  then have "\<exists>x. P x \<and> ?R\<^sup>*\<^sup>* a x"
  proof (induction rule: rtranclp_ev_induct)
    case prems: (step x)
    with step[of x] show ?case by auto
  qed (auto simp: R_irrefl)
  then show ?thesis by auto
qed


section \<open>Definitions\<close>

subsection \<open>Definitions Subsumption Graphs\<close>

locale Subsumption_Graph_Pre_Defs =
  ord less_eq less for less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50) and less (infix "\<prec>" 50) +
  fixes E ::  "'a \<Rightarrow> 'a \<Rightarrow> bool" -- \<open>The full edge set\<close>
    and s\<^sub>0 :: 'a                 -- \<open>Start state\<close>
begin

sublocale Graph_Start_Defs E s\<^sub>0 .

end

(* XXX Merge with Worklist locales *)
locale Subsumption_Graph_Defs = Subsumption_Graph_Pre_Defs +
  fixes RE :: "'a \<Rightarrow> 'a \<Rightarrow> bool" -- \<open>Subgraph of the graph given by the full edge set\<close>
begin

sublocale G: Graph_Start_Defs RE s\<^sub>0 .

sublocale G': Graph_Start_Defs "\<lambda> x y. RE x y \<or> (x \<prec> y \<and> G.reachable y)" s\<^sub>0 .

abbreviation G'_E    ("_ \<rightarrow>\<^sub>G\<^sub>'* _" [100, 100] 40) where
  "G'_E x y \<equiv> RE x y \<or> (x \<prec> y \<and> G.reachable y)"

notation RE          ("_ \<rightarrow>\<^sub>G _"   [100, 100] 40)

notation G.reaches   ("_ \<rightarrow>\<^sub>G* _"  [100, 100] 40)

notation G.reaches1  ("_ \<rightarrow>\<^sub>G\<^sup>+ _"  [100, 100] 40)

notation G'.reaches  ("_ \<rightarrow>\<^sub>G*' _" [100, 100] 40)

notation G'.reaches1 ("_ \<rightarrow>\<^sub>G\<^sup>+' _" [100, 100] 40)

end (* Subsumption Graph Defs *)


locale Subsumption_Graph_Pre = Subsumption_Graph_Pre_Defs + order less_eq less +
  assumes mono:
    "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> reachable a \<Longrightarrow> reachable b \<Longrightarrow> \<exists> b'. E b b' \<and> a' \<preceq> b'"
begin

lemmas [intro] = order.trans

end (* Subsumption Graph Pre *)

locale Reachability_Compatible_Subsumption_Graph = Subsumption_Graph_Defs + Subsumption_Graph_Pre +
  assumes reachability_compatible:
    "\<forall> s. G.reachable s \<longrightarrow> (\<forall> s'. E s s' \<longrightarrow> RE s s') \<or> (\<exists> t. s \<prec> t \<and> G.reachable t)"
  assumes subgraph: "\<forall> s s'. RE s s' \<longrightarrow> E s s'"
  assumes finite_reachable: "finite {a. G.reachable a}"

locale Subsumption_Graph_View_Defs = Subsumption_Graph_Defs +
  fixes SE ::  "'a \<Rightarrow> 'a \<Rightarrow> bool" -- \<open>Subsumption edges\<close>
    and covered :: "'a \<Rightarrow> bool"

locale Reachability_Compatible_Subsumption_Graph_View =
  Subsumption_Graph_View_Defs + Subsumption_Graph_Pre +
  assumes reachability_compatible:
    "\<forall> s. G.reachable s \<longrightarrow>
      (if covered s then (\<exists> t. SE s t \<and> G.reachable t) else (\<forall> s'. E s s' \<longrightarrow> RE s s'))"
  assumes subsumption: "\<forall> s'. SE s s' \<longrightarrow> s \<prec> s'"
  assumes subgraph: "\<forall> s s'. RE s s' \<longrightarrow> E s s'"
  assumes finite_reachable: "finite {a. G.reachable a}"
begin

sublocale Reachability_Compatible_Subsumption_Graph
proof standard
  have "(\<forall>s'. E s s' \<longrightarrow> RE s s') \<or> (\<exists>t. s \<prec> t \<and> G.reachable t)" if "G.reachable s" for s
    using that reachability_compatible subsumption by (cases "covered s"; fastforce)
  then show "\<forall>s. G.reachable s \<longrightarrow> (\<forall>s'. E s s' \<longrightarrow> RE s s') \<or> (\<exists>t. s \<prec> t \<and> G.reachable t)"
    by auto
qed (use subgraph in \<open>auto intro: finite_reachable mono\<close>)

end (* Reachability Compatible Subsumption Graph View *)

locale Reachability_Compatible_Subsumption_Graph_Final = Reachability_Compatible_Subsumption_Graph +
  fixes F :: "'a \<Rightarrow> bool" -- \<open>Final states\<close>
  assumes F_mono[intro]: "F a \<Longrightarrow> a \<preceq> b \<Longrightarrow> F b"

locale Liveness_Compatible_Subsumption_Graph = Reachability_Compatible_Subsumption_Graph_Final +
  assumes no_subsumption_cycle:
    "G'.reachable x \<Longrightarrow> G'.steps (x # xs @ [x]) \<Longrightarrow> G.steps (x # xs @ [x])"

section \<open>Reachability\<close>

context Reachability_Compatible_Subsumption_Graph
begin

lemma subgraph'[intro]:
  "E s s'" if "RE s s'"
  using that subgraph by blast

lemma G_reachability_sound[intro]:
  "reachable a" if "G.reachable a"
  using that by (induction; blast)

lemma G_steps_sound[intro]:
  "steps xs" if "G.steps xs"
  using that by (induction; blast)

lemma G_run_sound[intro]:
  "run xs" if "G.run xs"
  using that by (coinduction arbitrary: xs) (auto 4 3 elim: G.run.cases)

lemma G'_reachability_sound[intro]:
  "reachable a" if "G'.reachable a"
  using that by (induction; blast)

lemma (in Subsumption_Graph_Defs) G'_reachable_G_reachable[intro]:
  "G.reachable a" if "G'.reachable a"
  using that by (induction; blast)

lemma (in Subsumption_Graph_Defs) G_reachable_G'_reachable[intro]:
  "G'.reachable a" if "G.reachable a"
  using that by (induction; blast)

lemma (in Subsumption_Graph_Defs) G_G'_reachable_iff:
  "G.reachable a \<longleftrightarrow> G'.reachable a"
  by blast

lemma G'_finite_reachable: "finite {a. G'.reachable a}"
  by (blast intro: finite_subset[OF _ finite_reachable])

lemma G_steps_G'_steps[intro]:
  "G'.steps as" if "G.steps as"
  using that by induction auto

lemma reachable_has_surrogate:
  "\<exists> t. G.reachable t \<and> s \<preceq> t \<and> (\<forall> s'. E t s' \<longrightarrow> RE t s')" if "G.reachable s"
proof -
  from finite_reachable \<open>G.reachable s\<close> obtain x where
    "\<forall>s'. E x s' \<longrightarrow> RE x s'" "G.reachable x" "op \<prec>\<^sup>*\<^sup>* s x"
    apply atomize_elim
    apply (induction rule: rtranclp_ev_induct2)
    using reachability_compatible by auto
  moreover from \<open>op \<prec>\<^sup>*\<^sup>* s x\<close> have "s \<prec> x \<or> s = x"
    by induction auto
  ultimately show ?thesis by auto
qed

lemma reachable_has_surrogate':
  "\<exists> t xs. G'.steps xs \<and> xs \<noteq> [] \<and> hd xs = s \<and> last xs = t \<and> s \<preceq> t \<and> (\<forall> s'. E t s' \<longrightarrow> RE t s')"
  if "G.reachable s"
proof -
  from \<open>G.reachable s\<close> have \<open>G.reachable s\<close> by auto
  from finite_reachable this obtain x where
    real_edges: "\<forall>s'. E x s' \<longrightarrow> RE x s'" and "G.reachable x" "op \<prec>\<^sup>*\<^sup>* s x"
    apply atomize_elim
    apply (induction rule: rtranclp_ev_induct2)
    using reachability_compatible by auto
  from \<open>op \<prec>\<^sup>*\<^sup>* s x\<close> have "s \<prec> x \<or> s = x"
    by induction auto
  then show ?thesis
  proof
    assume "s \<prec> x"
    with real_edges \<open>G.reachable x\<close> show ?thesis
      by (inst_existentials "x" "[s,x]") auto
  next
    assume "s = x"
    with real_edges show ?thesis
      by (inst_existentials "s" "[s]") auto
  qed
qed

lemma reachable_has_surrogate1:
  "\<exists> t. s \<preceq> t \<and> s \<rightarrow>\<^sub>G*' t \<and> (\<forall> s'. E t s' \<longrightarrow> RE t s')" if "G.reachable s"
  using reachable_has_surrogate'[OF that] by auto

lemma subsumption_step:
  "\<exists> a'' b'. a' \<preceq> a'' \<and> b \<preceq> b' \<and> RE a'' b' \<and> G.reachable a''" if
  "reachable a" "E a b" "G.reachable a'" "a \<preceq> a'"
proof -
  from mono[OF \<open>a \<preceq> a'\<close> \<open>E a b\<close> \<open>reachable a\<close>] \<open>G.reachable a'\<close> obtain b' where "E a' b'" "b \<preceq> b'"
    by auto
  from reachable_has_surrogate[OF \<open>G.reachable a'\<close>] obtain a''
    where "a' \<preceq> a''" "G.reachable a''" and *: "\<forall> s'. E a'' s' \<longrightarrow> RE a'' s'"
    by auto
  from mono[OF \<open>a' \<preceq> a''\<close> \<open>E a' b'\<close>] \<open>G.reachable a'\<close> \<open>G.reachable a''\<close> obtain b'' where
    "E a'' b''" "b' \<preceq> b''"
    by auto
  with * \<open>a' \<preceq> a''\<close> \<open>b \<preceq> b'\<close> \<open>G.reachable a''\<close> show ?thesis
    by auto
qed

lemma subsumption_step':
  "\<exists> b' xs. b \<preceq> b' \<and> G'.steps xs \<and> hd xs = a' \<and> last xs = b' \<and> length xs > 1" if
  "reachable a" "E a b" "G'.reachable a'" "a \<preceq> a'"
proof -
  from mono[OF \<open>a \<preceq> a'\<close> \<open>E a b\<close> \<open>reachable a\<close>] \<open>G'.reachable a'\<close> obtain b' where "E a' b'" "b \<preceq> b'"
    by auto
  from reachable_has_surrogate'[of a'] \<open>G'.reachable a'\<close> obtain a'' xs where *:
    "G'.steps xs" "xs \<noteq> []" "hd xs = a'" "last xs = a''" "a' \<preceq> a''" "(\<forall>s'. E a'' s' \<longrightarrow> RE a'' s')"
    by auto
  with \<open>G'.reachable a'\<close> have "G'.reachable a''"
    by (blast intro: G'.reachable_steps_append)
  with mono[OF \<open>a' \<preceq> a''\<close> \<open>E a' b'\<close>] \<open>G'.reachable a'\<close> obtain b'' where
    "E a'' b''" "b' \<preceq> b''"
    by auto
  with * \<open>a' \<preceq> a''\<close> \<open>b \<preceq> b'\<close> \<open>G'.reachable a''\<close> show ?thesis
    by (inst_existentials b'' "xs @ [b'']") auto
qed

lemma subsumption_step1:
  "\<exists> b'. b \<preceq> b' \<and> a' \<rightarrow>\<^sub>G\<^sup>+' b'" if "reachable a" "E a b" "G'.reachable a'" "a \<preceq> a'"
proof -
  from subsumption_step'[OF that] guess b' xs by safe
  then show ?thesis
    by - (subst (asm) (2) hd_butlast_last_id[symmetric], auto intro: G'.steps_reaches1)
qed

theorem reachability_complete':
  "\<exists> s'. s \<preceq> s' \<and> G.reachable s'" if "a \<rightarrow>* s" "G.reachable a"
  using that
proof (induction)
  case base
  then show ?case by auto
next
  case (step s t)
  then obtain s' where "s \<preceq> s'" "G.reachable s'"
    by auto
  with step(4) have "reachable a" "G.reachable s'"
    by auto
  with step(1) have "reachable s"
    by auto
  from subsumption_step[OF \<open>reachable s\<close> \<open>E s t\<close> \<open>G.reachable s'\<close> \<open>s \<preceq> s'\<close>] guess s'' t' by clarify
  with \<open>G.reachable s'\<close> show ?case
    by auto
qed

theorem steps_complete':
  "\<exists> ys. list_all2 (op \<preceq>) xs ys \<and> G.steps (a # ys)" if
  "steps (a # xs)" "G.reachable a"
  using that
proof (induction "a # xs" arbitrary: a xs rule: steps_alt_induct)
  case (Single x)
  then show ?case by auto
oops

theorem steps_complete':
  "\<exists> c ys. list_all2 (op \<preceq>) xs ys \<and> G.steps (c # ys) \<and> b \<preceq> c" if
  "steps (a # xs)" "reachable a" "a \<preceq> b" "G.reachable b"
oops

(* XXX Does this hold? *)
theorem run_complete':
  "\<exists> ys. stream_all2 (op \<preceq>) xs ys \<and> G.run (a ## ys)" if "run (a ## xs)" "G.reachable a"
proof -
  define f where "f = (\<lambda> x b. SOME y. x \<preceq> y \<and> RE b y)"
  define gen where "gen a xs = sscan f xs a" for a xs
  have gen_ctr: "gen x xs = f (shd xs) x ## gen (f (shd xs) x) (stl xs)" for x xs
    unfolding gen_def by (subst sscan.ctr) (rule HOL.refl)
  from that have "G.run (gen a xs)"
  proof (coinduction arbitrary: a xs)
    case run
    then show ?case
      apply (cases xs)
      apply auto
      apply (subst gen_ctr)
      apply simp
      apply (subst gen_ctr)
      apply simp
      apply rule
oops

corollary reachability_complete:
  "\<exists> s'. s \<preceq> s' \<and> G.reachable s'" if "reachable s"
  using reachability_complete'[of s\<^sub>0 s] that unfolding reachable_def by auto

corollary reachability_correct:
  "(\<exists> s'. s \<preceq> s' \<and> reachable s') \<longleftrightarrow> (\<exists> s'. s \<preceq> s' \<and> G.reachable s')"
  by (blast dest: reachability_complete)

lemma steps_G'_steps:
  "\<exists> ys ns. list_all2 (op \<preceq>) xs (sublist ys ns) \<and> G'.steps (b # ys)" if
  "steps (a # xs)" "reachable a" "a \<preceq> b" "G'.reachable b"
  using that
proof (induction "a # xs" arbitrary: a b xs)
  case (Single)
  then show ?case by force
next
  case (Cons x y xs)
  from subsumption_step'[OF \<open>reachable x\<close> \<open>E x y\<close> _ \<open>x \<preceq> b\<close>] \<open>G'.reachable b\<close> obtain b' as where
    "y \<preceq> b'" "G'.steps as" "hd as = b" "last as = b'" "length as > 1"
    by auto
  with \<open>reachable x\<close> Cons.hyps(1) Cons.prems(3) obtain ys ns where
    "list_all2 op \<preceq> xs (sublist ys ns)" "G'.steps (b' # ys)"
    by atomize_elim (rule Cons.hyps(3)[OF _ \<open>y \<preceq> b'\<close>]; auto intro: G'.reachable_steps_append)
  with \<open>G'.steps as\<close> \<open>last as = b'\<close> have "G'.steps (as @ ys)"
    using G'.steps_append by force
  with \<open>hd as = b\<close> \<open>y \<preceq> b'\<close> \<open>last as = b'\<close> \<open>length as > 1\<close> show ?case
    apply (inst_existentials "tl as @ ys" "{length as - 2} \<union> {n + length as - 1 | n. n \<in> ns}")
    subgoal
      apply (subst sublist_split)
       apply force
      apply (subst sublist_nth, (simp; fail))
      apply simp
      apply safe
      subgoal
        by (subst nth_append) (cases as; auto simp: last_conv_nth)
      apply (subst sublist_shift)
       apply force
      subgoal premises prems
      proof -
        from \<open>Suc 0 < _\<close> have
          "{x - length (tl as) |x. x \<in> {n + length as - Suc 0 |n. n \<in> ns}} = ns"
          by force
        with \<open>list_all2 _ _ _\<close> show ?thesis by auto
      qed
      done
    subgoal
      by (cases as) auto
    done
qed

lemma cycle_G'_cycle'':
  assumes "steps (s\<^sub>0 # ws @ x # xs @ [x])"
  shows "\<exists> x' xs' ys'. x \<preceq> x' \<and> G'.steps (s\<^sub>0 # xs' @ x' # ys' @ [x'])"
proof -
  let ?n  = "card {x. G'.reachable x} + 1"
  let ?xs = "x # concat (replicate ?n (xs @ [x]))"
  from assms(1) have "steps (x # xs @ [x])"
    by (auto dest: stepsD)
  with steps_replicate[of "x # xs @ [x]" ?n] have "steps ?xs"
    by auto
  then have "steps (s\<^sub>0 # ws @ ?xs)"
  proof -
    from assms have "steps ((s\<^sub>0 # ws @ [x]) @ xs @ [x])"
      by auto
    then have "steps (s\<^sub>0 # ws @ [x])"
      by (fastforce dest: stepsD)
    from steps_append[OF this \<open>steps ?xs\<close>] show ?thesis
      by auto
  qed
  from steps_G'_steps[OF this, of s\<^sub>0] obtain ys ns where ys:
    "list_all2 op \<preceq> (ws @ x # concat (replicate ?n (xs @ [x]))) (sublist ys ns)"
    "G'.steps (s\<^sub>0 # ys)"
    by auto
  then obtain x' ys' ns' ws' where ys':
    "G'.steps (x' # ys')" "G'.steps (s\<^sub>0 # ws' @ [x'])"
    "list_all2 op \<preceq> (concat (replicate ?n (xs @ [x]))) (sublist ys' ns')"
    apply atomize_elim
    apply auto
    apply (subst (asm) list_all2_append1)
    apply safe
    apply (subst (asm) list_all2_Cons1)
    apply safe
    apply (drule sublist_eq_appendD)
    apply safe
    apply (drule sublist_eq_ConsD)
    apply safe
    subgoal for ys1 ys2 z ys3 ys4 ys5 ys6 ys7 i
      apply (inst_existentials z ys7)
      subgoal
        by (auto dest: G'.stepsD)
      subgoal premises prems
      proof -
        from prems have "G'.steps ((s\<^sub>0 # ys4 @ ys6 @ [z]) @ ys7)"
          by auto
        moreover then have "G'.steps (s\<^sub>0 # ys4 @ ys6 @ [z])"
          by (fastforce dest: G'.stepsD)
        ultimately show ?thesis
          by (inst_existentials "ys4 @ ys6") auto
      qed
      by force
    done
  let ?ys = "filter (op \<preceq> x) ys'"
  have "length ?ys \<ge> ?n"
    using list_all2_replicate_elem_filter[OF ys'(3), of x]
    using filter_sublist_length[of "(op \<preceq> x)" ys' ns']
    by auto
  from \<open>G'.steps (s\<^sub>0 # ws' @ [x'])\<close> have "G'.reachable x'"
    by (auto intro: G'.steps_reachable)
  have "set ?ys \<subseteq> set ys'"
    by auto
  also have "\<dots> \<subseteq> {x. G'.reachable x}"
    using \<open>G'.steps (x' # _)\<close> \<open>G'.reachable x'\<close>
    by clarsimp (rule G'.reachable_steps_elem[rotated], assumption, auto)
  finally have "\<not> distinct ?ys"
    using distinct_card[of ?ys] \<open>_ >= ?n\<close>
    by - (rule ccontr; drule distinct_length_le[OF G'_finite_reachable]; simp)
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
  have "G'.steps (y # bs' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>G'.steps (x' # _)\<close> \<open>ys' = _\<close> have "G'.steps (x' # as' @ (y # bs' @ [y]) @ cs')"
      by auto
    then show ?thesis
      by - ((simp; fail) | drule G'.stepsD)+
  qed
  moreover have "G'.steps (s\<^sub>0 # ws' @ x' # as' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>G'.steps (x' # ys')\<close> \<open>ys' = _\<close> have "G'.steps ((x' # as' @ [y]) @ bs' @ y # cs')"
      by auto
    from G'.steps_appendD1[OF this] have "G'.steps (x' # as' @ [y])"
      by simp
    with \<open>G'.steps (s\<^sub>0 # ws' @ [x'])\<close> show ?thesis
      by (auto dest: G'.steps_append)
  qed
  moreover from \<open>?ys = _\<close> have "x \<preceq> y"
  proof -
    from \<open>?ys = _\<close> have "y \<in> set ?ys" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis
    by (inst_existentials y "ws' @ x' # as'" bs') (auto dest: G'.steps_append)
qed

lemma cycle_G'_cycle':
  assumes "steps (s\<^sub>0 # ws @ x # xs @ [x])"
  shows "\<exists> y ys. x \<preceq> y \<and> G'.steps (y # ys @ [y]) \<and> G'.reachable y"
proof -
  from cycle_G'_cycle''[OF assms] obtain x' xs' ys' where
    "x \<preceq> x'" "G'.steps (s\<^sub>0 # xs' @ x' # ys' @ [x'])"
    by auto
  then show ?thesis
    by (inst_existentials x' ys') (auto dest: G'.stepsD intro: G'.steps_reachable)
qed

lemma cycle_G'_cycle:
  assumes "steps (x # xs @ [x])" "G.reachable x"
  shows "\<exists> y ys. x \<preceq> y \<and> G'.steps (y # ys @ [y]) \<and> G'.reachable y"
proof -
  from steps_append[OF assms(1) assms(1)] have *: "steps (x # xs @ x # xs @ [x])"
    by simp
  from reachable_steps[of x] assms(2) obtain ws where "steps ws" "hd ws = s\<^sub>0" "last ws = x"
    by auto
  with steps_append[OF this(1) *] obtain us where "steps (s\<^sub>0 # (us @ xs) @ x # xs @ [x])"
    by (cases ws; auto)
  from cycle_G'_cycle'[OF this] show ?thesis .
qed

corollary G'_reachability_complete:
  "\<exists> s'. s \<preceq> s' \<and> G.reachable s'" if "G'.reachable s"
  using reachability_complete that by auto

end (* Reachability Compatible Subsumption Graph *)

corollary (in Reachability_Compatible_Subsumption_Graph_Final) reachability_correct:
  "(\<exists> s'. reachable s' \<and> F s') \<longleftrightarrow> (\<exists> s'. G.reachable s' \<and> F s')"
  using reachability_complete by blast


section \<open>Liveness\<close>

theorem (in Liveness_Compatible_Subsumption_Graph) cycle_iff:
  "(\<exists> x xs. steps   (x # xs @ [x]) \<and> reachable x   \<and> F x) \<longleftrightarrow>
   (\<exists> x xs. G.steps (x # xs @ [x]) \<and> G.reachable x \<and> F x)"
proof (safe, goal_cases)
  -- \<open>steps \<open>\<rightarrow>\<close> G.steps\<close>
  case prems: (1 x xs)
  with reachable_cycle_iff[of x xs] obtain ws where
    "steps (s\<^sub>0 # ws @ x # xs @ [x])"
    by auto
  from cycle_G'_cycle'[OF this] obtain y ys where
    "x \<preceq> y" "G'.steps (y # ys @ [y])" "G'.reachable y"
    by auto
  with \<open>F x\<close> show ?case
    by (auto intro: no_subsumption_cycle)
qed auto


section \<open>Appendix\<close>

context Subsumption_Graph_Pre
begin

lemma steps_mono:
  assumes "steps (x # xs)" "x \<preceq> y" "reachable x" "reachable y"
  shows "\<exists> ys. steps (y # ys) \<and> list_all2 (op \<preceq>) xs ys"
  using assms
proof (induction "x # xs" arbitrary: x y xs)
  case (Single x)
  then show ?case by auto
next
  case (Cons x y xs x')
  from mono[OF \<open>x \<preceq> x'\<close> \<open>E x y\<close>] Cons.prems obtain y' where "E x' y'" "y \<preceq> y'"
    by auto
  with Cons.hyps(3)[OF \<open>y \<preceq> y'\<close>] \<open>E x y\<close> Cons.prems obtain ys where
    "steps (y' # ys)" "list_all2 op \<preceq> xs ys"
    by auto
  with \<open>E x' y'\<close> \<open>y \<preceq> y'\<close> show ?case
    by auto
qed

lemma steps_append_subsumption:
  assumes "steps (x # xs)" "steps (y # ys)" "y \<preceq> last (x # xs)" "reachable x" "reachable y"
  shows "\<exists> ys'. steps (x # xs @ ys') \<and> list_all2 op \<preceq> ys ys'"
proof -
  from assms have "reachable (last (x # xs))"
    by - (rule reachable_steps_elem, auto)
  from steps_mono[OF \<open>steps (y # ys)\<close> \<open>y \<preceq> _\<close> \<open>reachable y\<close> this] obtain ys' where
    "steps (last (x # xs) # ys')" "list_all2 op \<preceq> ys ys'"
    by auto
  with steps_append[OF \<open>steps (x # xs)\<close> this(1)] show ?thesis
    by auto
qed

lemma steps_replicate_subsumption:
  assumes "x \<preceq> last (x # xs)" "steps (x # xs)" "n > 0" "reachable x"
  shows "\<exists> ys. steps (x # ys) \<and> list_all2 (op \<preceq>) (concat (replicate n xs)) ys"
  using assms
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    with Suc.prems show ?thesis
      by (inst_existentials xs) (auto intro: list_all2_refl)
  next
    case prems: (Suc n')
    with Suc \<open>n = _\<close> obtain ys where ys:
      "list_all2 op \<preceq> (concat (replicate n xs)) ys" "steps (x # ys)"
      by auto
    with \<open>n = _\<close> have "list_all2 op \<preceq> (concat (replicate n' xs) @ xs) ys"
      by (metis append_Nil2 concat.simps(1,2) concat_append replicate_Suc replicate_append_same)
    with \<open>x \<preceq> _\<close> have "x \<preceq> last (x # ys)"
      by (cases xs; auto dest: list_all2_last split: if_split_asm simp: list_all2_Cons1)
    from steps_append_subsumption[OF \<open>steps (x # ys)\<close> \<open>steps (x # xs)\<close> this] \<open>reachable x\<close> obtain
      ys' where "steps (x # ys @ ys')" "list_all2 op \<preceq> xs ys'"
      by auto
    with ys(1) \<open>n = _\<close> show ?thesis
      apply (inst_existentials "ys @ ys'")
      by auto
        (metis
          append_Nil2 concat.simps(1,2) concat_append list_all2_appendI replicate_Suc
          replicate_append_same
        )
  qed
qed

context
  assumes finite_reachable: "finite {x. reachable x}"
begin

(* XXX Unused *)
lemma wf_less_on_reachable_set:
  "wf {(x, y). y \<prec> x \<and> reachable x \<and> reachable y}" (is "wf ?S")
proof (rule finite_acyclic_wf)
  have "?S \<subseteq> {(x, y). reachable x \<and> reachable y}"
    by auto
  also have "finite \<dots>"
    using finite_reachable by auto
  finally show "finite ?S" .
next
  show "acyclicP (\<lambda>x y. y \<prec> x \<and> reachable x \<and> reachable y)"
    by (rule acyclicI_order[where f = id]) auto
qed

text \<open>
  This shows that looking for cycles and pre-cycles is equivalent in monotone subsumption graphs.
\<close>
(* XXX Duplication -- cycle_G'_cycle'' *)
lemma pre_cycle_cycle:
  (* XXX Move to different locale *)
  assumes A: "x \<preceq> x'" "steps (x # xs @ [x'])" "reachable x"
  shows "\<exists> x'' ys. x' \<preceq> x'' \<and> steps (x'' # ys @ [x'']) \<and> reachable x''"
proof -
  let ?n  = "card {x. reachable x} + 1"
  let ?xs = "concat (replicate ?n (xs @ [x']))"
  from steps_replicate_subsumption[OF _ \<open>steps _\<close>, of ?n] \<open>reachable x\<close> \<open>x \<preceq> x'\<close> obtain ys where
    "steps (x # ys)" "list_all2 (op \<preceq>) ?xs ys"
    by auto
  let ?ys = "filter (op \<preceq> x') ys"
  have "length ?ys \<ge> ?n"
    using list_all2_replicate_elem_filter[OF \<open>list_all2 (op \<preceq>) ?xs ys\<close>, of x']
    by auto
  have "set ?ys \<subseteq> set ys"
    by auto
  also have "\<dots> \<subseteq> {x. reachable x}"
    using \<open>steps (x # ys)\<close> \<open>reachable x\<close>
    by clarsimp (rule reachable_steps_elem[rotated], assumption, auto)
  finally have "\<not> distinct ?ys"
    using distinct_card[of ?ys] \<open>_ >= ?n\<close>
    by - (rule ccontr; drule distinct_length_le[OF finite_reachable]; simp)
  from not_distinct_decomp[OF this] obtain as y bs cs where "?ys = as @ [y] @ bs @ [y] @ cs"
    by auto
  then obtain as' bs' cs' where
    "ys = as' @ [y] @ bs' @ [y] @ cs'"
    apply atomize_elim
    apply simp
    apply (drule filter_eq_appendD filter_eq_ConsD filter_eq_appendD[OF sym], clarify)+
    apply clarsimp
    subgoal for as1 as2 bs1 bs2 cs'
      by (inst_existentials "as1 @ as2" "bs1 @ bs2") simp
    done
  have "steps (y # bs' @ [y])"
  proof -
    (* XXX Decision procedure? *)
    from \<open>steps (x # ys)\<close> \<open>ys = _\<close> have "steps (x # as' @ (y # bs' @ [y]) @ cs')"
      by auto
    then show ?thesis
      by - ((simp; fail) | drule stepsD)+
  qed
  moreover have "reachable y"
  proof -
    from \<open>steps (x # ys)\<close> \<open>ys = _\<close> have "steps ((x # as' @ [y]) @ (bs' @ y # cs'))" (* XXX *)
      by simp
    then have "steps (x # as' @ [y])"
      by (blast dest: stepsD)
    with \<open>reachable x\<close> show ?thesis
      by (auto 4 3)
  qed
  moreover from \<open>?ys = _\<close> have "x' \<preceq> y"
  proof -
    from \<open>?ys = _\<close> have "y \<in> set ?ys" by auto
    then show ?thesis by auto
  qed
  ultimately show ?thesis
    by auto
qed

end (* Finite Reachable Subgraph *)

end (* Subsumption Graph Pre *)


context Subsumption_Graph_Defs
begin

sublocale G'': Graph_Start_Defs "\<lambda> x y. \<exists> z. G.reachable z \<and> x \<preceq> z \<and> RE z y" s\<^sub>0 .

lemma G''_reachable_G'[intro]:
  "G'.reachable x" if "G''.reachable x"
  using that
  unfolding G'.reachable_def G''.reachable_def G_G'_reachable_iff Graph_Start_Defs.reachable_def
proof (induction)
  case base
  then show ?case
    by blast
next
  case (step y z)
  then obtain z' where
    "RE\<^sup>*\<^sup>* s\<^sub>0 z'" "y \<preceq> z'" "RE z' z"
    by auto
  from this(1) have "(\<lambda>x y. RE x y \<or> x \<prec> y \<and> RE\<^sup>*\<^sup>* s\<^sub>0 y)\<^sup>*\<^sup>* s\<^sub>0 z'"
    by (induction; blast intro: rtranclp.intros(2))
  with \<open>RE z' z\<close> show ?case
    by (blast intro: rtranclp.intros(2))
qed

end (* Subsumption Graph Defs *)

locale Reachability_Compatible_Subsumption_Graph_Total = Reachability_Compatible_Subsumption_Graph +
  assumes total: "reachable a \<Longrightarrow> reachable b \<Longrightarrow> a \<preceq> b \<or> b \<preceq> a"
begin

sublocale G''_pre: Subsumption_Graph_Pre "op \<preceq>" "op \<prec>" "\<lambda> x y. \<exists> z. G.reachable z \<and> x \<preceq> z \<and> RE z y"
proof (standard, safe, goal_cases)
  case prems: (1 a b a' z)
  show ?case
  proof (cases "b \<preceq> z")
    case True
    with prems show ?thesis
      by auto
  next
    case False
    with total[of b z] prems have "z \<preceq> b"
      by auto
    with subsumption_step[of z a' b] prems obtain a'' b' where
      "b \<preceq> a''" "a' \<preceq> b'" "RE a'' b'" "G.reachable a''"
      by auto
    then show ?thesis
      by (inst_existentials b' a'') auto
  qed
qed

end (* Reachability Compatible Subsumption Graph Total *)

section \<open>Old Material\<close>

locale Reachability_Compatible_Subsumption_Graph' = Subsumption_Graph_Defs + order "op \<preceq>" "op \<prec>" +
  assumes reachability_compatible:
    "\<forall> s. G.reachable s \<longrightarrow> (\<forall> s'. E s s' \<longrightarrow> RE s s') \<or> (\<exists> t. s \<prec> t \<and> G.reachable t)"
  assumes subgraph: "\<forall> s s'. RE s s' \<longrightarrow> E s s'"
  assumes finite_reachable: "finite {a. G.reachable a}"
  assumes mono:
    "a \<preceq> b \<Longrightarrow> E a a' \<Longrightarrow> reachable a \<Longrightarrow> G.reachable b \<Longrightarrow> \<exists> b'. E b b' \<and> a' \<preceq> b'"
begin

lemmas [intro] = order.trans

lemma subgraph'[intro]:
  "E s s'" if "RE s s'"
  using that subgraph by blast

lemma G_reachability_sound[intro]:
  "reachable a" if "G.reachable a"
  using that unfolding reachable_def G.reachable_def by (induction; blast intro: rtranclp.intros(2))

lemma G_steps_sound[intro]:
  "steps xs" if "G.steps xs"
  using that by induction auto

lemma G_run_sound[intro]:
  "run xs" if "G.run xs"
  using that by (coinduction arbitrary: xs) (auto 4 3 elim: G.run.cases)

lemma reachable_has_surrogate:
  "\<exists> t. G.reachable t \<and> s \<preceq> t \<and> (\<forall> s'. E t s' \<longrightarrow> RE t s')" if "G.reachable s"
  using that
proof -
  from finite_reachable \<open>G.reachable s\<close> obtain x where
    "\<forall>s'. E x s' \<longrightarrow> RE x s'" "G.reachable x" "op \<prec>\<^sup>*\<^sup>* s x"
    apply atomize_elim
    apply (induction rule: rtranclp_ev_induct2)
    using reachability_compatible by auto
  moreover from \<open>op \<prec>\<^sup>*\<^sup>* s x\<close> have "s \<prec> x \<or> s = x"
    by induction auto
  ultimately show ?thesis by auto
qed

lemma subsumption_step:
  "\<exists> a'' b'. a' \<preceq> a'' \<and> b \<preceq> b' \<and> RE a'' b' \<and> G.reachable a''" if
  "reachable a" "E a b" "G.reachable a'" "a \<preceq> a'"
proof -
  from mono[OF \<open>a \<preceq> a'\<close> \<open>E a b\<close> \<open>reachable a\<close> \<open>G.reachable a'\<close>] obtain b' where "E a' b'" "b \<preceq> b'"
    by auto
  from reachable_has_surrogate[OF \<open>G.reachable a'\<close>] obtain a''
    where "a' \<preceq> a''" "G.reachable a''" and *: "\<forall> s'. E a'' s' \<longrightarrow> RE a'' s'"
    by auto
  from mono[OF \<open>a' \<preceq> a''\<close> \<open>E a' b'\<close>] \<open>G.reachable a'\<close> \<open>G.reachable a''\<close> obtain b'' where
    "E a'' b''" "b' \<preceq> b''"
    by auto
  with * \<open>a' \<preceq> a''\<close> \<open>b \<preceq> b'\<close> \<open>G.reachable a''\<close> show ?thesis by auto
qed

theorem reachability_complete':
  "\<exists> s'. s \<preceq> s' \<and> G.reachable s'" if "E\<^sup>*\<^sup>* a s" "G.reachable a"
  using that
proof (induction)
  case base
  then show ?case by auto
next
  case (step s t)
  then obtain s' where "s \<preceq> s'" "G.reachable s'"
    by auto
  with step(4) have "reachable a" "G.reachable s'"
    by auto
  with step(1) have "reachable s"
    by (auto simp: reachable_def)
  from subsumption_step[OF \<open>reachable s\<close> \<open>E s t\<close> \<open>G.reachable s'\<close> \<open>s \<preceq> s'\<close>] guess s'' t' by clarify
  with \<open>G.reachable s'\<close> show ?case
    by (auto simp: reachable_def)
qed

theorem steps_complete':
  "\<exists> ys. list_all2 (op \<preceq>) xs ys \<and> G.steps (a # ys)" if
  "steps (a # xs)" "G.reachable a"
  using that
proof (induction "a # xs" arbitrary: a xs rule: steps_alt_induct)
  case (Single x)
  then show ?case by auto
oops

theorem steps_complete':
  "\<exists> c ys. list_all2 (op \<preceq>) xs ys \<and> G.steps (c # ys) \<and> b \<preceq> c" if
  "steps (a # xs)" "reachable a" "a \<preceq> b" "G.reachable b"
  using that
proof (induction "a # xs" arbitrary: a b xs)
  case (Single x)
  then show ?case by auto
next
  case (Cons x y xs)
  from subsumption_step[OF \<open>reachable x\<close> \<open>E _ _\<close> \<open>G.reachable b\<close> \<open>x \<preceq> b\<close>] guess b' y' by clarify
  with Cons obtain y'' ys where "list_all2 op \<preceq> xs ys" "G.steps (y'' # ys)" "y' \<preceq> y''"
    oops

(* XXX Does this hold? *)
theorem run_complete':
  "\<exists> ys. stream_all2 (op \<preceq>) xs ys \<and> G.run (a ## ys)" if "run (a ## xs)" "G.reachable a"
proof -
  define f where "f = (\<lambda> x b. SOME y. x \<preceq> y \<and> RE b y)"
  define gen where "gen a xs = sscan f xs a" for a xs
  have gen_ctr: "gen x xs = f (shd xs) x ## gen (f (shd xs) x) (stl xs)" for x xs
    unfolding gen_def by (subst sscan.ctr) (rule HOL.refl)
  from that have "G.run (gen a xs)"
  proof (coinduction arbitrary: a xs)
    case run
    then show ?case
      apply (cases xs)
      apply auto
      apply (subst gen_ctr)
      apply simp
      apply (subst gen_ctr)
      apply simp
      apply rule
oops

corollary reachability_complete:
  "\<exists> s'. s \<preceq> s' \<and> G.reachable s'" if "reachable s"
  using reachability_complete'[of s\<^sub>0 s] that unfolding reachable_def by auto

corollary reachability_correct:
  "(\<exists> s'. s \<preceq> s' \<and> reachable s') \<longleftrightarrow> (\<exists> s'. s \<preceq> s' \<and> G.reachable s')"
  using reachability_complete by blast

lemma G'_reachability_sound[intro]:
  "reachable a" if "G'.reachable a"
  using that by induction auto

corollary G'_reachability_complete:
  "\<exists> s'. s \<preceq> s' \<and> G.reachable s'" if "G'.reachable s"
  using reachability_complete that by auto

end (* Reachability Compatible Subsumption Graph' *)