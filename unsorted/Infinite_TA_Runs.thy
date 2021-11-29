theory Infinite_TA_Runs
  imports
    TA.Normalized_Zone_Semantics
    TA_Library.Stream_More
    TA_Library.Instantiate_Existentials
begin

type_synonym ('s, 'c, 't) run = "('s * ('c, 't) cval) stream"
type_synonym ('s, 'c, 't) zrun = "('s * ('c, 't) zone) stream"
type_synonym ('a, 's, 'c, 't) trun = "('a, 'c, 't, 's) transition stream"

coinductive is_run for A where
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> is_run A ((l', u') ## xs) \<Longrightarrow> is_run A ((l, u) ## (l', u') ## xs)"

coinductive is_trun for A where
  "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> is_trun A ((l', g', a', r', l'') ## xs)
  \<Longrightarrow> is_trun A ((l, g, a, r, l') ## (l', g', a', r', l'') ## xs)"

(* definition "is_run' A xs ts \<equiv> is_run A xs \<and> smap fst xs = smap fst ts" *)

definition zone_step ::
  "('a, 'c, 't :: time, 's) ta \<Rightarrow> ('a, 'c, 't, 's) transition \<Rightarrow> ('c, 't) zone \<Rightarrow> ('c, 't) zone"
where
  "zone_step A \<equiv> \<lambda> (l, g, a, r, l') Z.
    zone_set ((Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}) \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}"

coinductive is_zrun for A where
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle> \<Longrightarrow> is_zrun A ((l'', Z'') ## xs)
  \<Longrightarrow> is_zrun A ((l, Z) ## (l'', Z'') ## xs)"

definition step_from ::
  "('a, 'c, 't :: time, 's) ta \<Rightarrow> ('c, 't) cval \<Rightarrow> ('a, 'c, 't, 's) transition \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> _ \<rightarrow>\<^bsub>_\<^esub> _" [61,61] 61)
where
"A \<turnstile> u \<rightarrow>\<^bsub>t\<^esub> u' \<equiv> case t of (l, g, a, r, l') \<Rightarrow> \<exists> d \<ge> 0.
  u \<oplus> d \<turnstile> inv_of A l \<and> d \<ge> 0 \<and> A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<and> u \<oplus> d \<turnstile> g \<and> u' \<turnstile> inv_of A l'
  \<and> u' = [r \<rightarrow> 0](u \<oplus> d)"

lemma step_from_cases:
  assumes "A \<turnstile> u \<rightarrow>\<^bsub>t\<^esub> u'"
  obtains l g a r l' d where
    "t = (l, g, a, r, l')"
    "u \<oplus> d \<turnstile> inv_of A l" "d \<ge> 0" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "u \<oplus> d \<turnstile> g" "u' \<turnstile> inv_of A l'"
    "u' = [r \<rightarrow> 0](u \<oplus> d)"
  apply atomize_elim
  using assms unfolding step_from_def by (cases t) auto

lemma step_from_step':
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" if "A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'"
  using that by (auto intro: step_a.intros elim!: step_from_cases)

lemma stepz_from_steps:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>" if "A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'" "A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"
  using that by (blast intro: step_from_step')

lemma step_from_complete:
  "A \<turnstile> u \<rightarrow>\<^bsub>t\<^esub> u' \<Longrightarrow> u \<in> Z \<Longrightarrow> u' \<in> zone_step A t Z"
  by (auto 4 4 simp: zone_delay_def zone_step_def zone_set_def elim!: step_from_cases)

coinductive is_run_from for A where
  "A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u' \<Longrightarrow> is_run_from A ((l', u') ## xs) ts
  \<Longrightarrow> is_run_from A ((l, u) ## (l', u') ## xs) ((l, g, a, r, l') ## ts)"

inductive stepz_from ::
  "('a, 'c, 't, 's) ta \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> _ \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> _ \<leadsto>\<^bsub>_\<^esub> _" [61,61,61,61] 61)
where
  "A \<turnstile> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> zone_step A (l, g, a, r, l') Z"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"

coinductive is_zrun_from for A where
  "A \<turnstile> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z' \<Longrightarrow> is_zrun_from A ((l', Z'') ## xs) ts
  \<Longrightarrow> is_zrun_from A ((l, Z) ## (l', Z') ## xs) ((l, g, a, r, l') ## ts)"

lemma
 "\<exists> u' \<in> zone_step A (l, g, a, r, l') Z. A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'"
 if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "zone_step A (l, g, a, r, l') Z \<noteq> {}"
proof -
  define thesis where "thesis = ?thesis"
  from that show ?thesis
    unfolding zone_step_def
 oops

lemma zstep_from_prestable:
  "\<exists> u' \<in> Z'. A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'" if "A \<turnstile> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'" "Z' \<noteq> {}" "u \<in> Z"
  using that
  apply cases
    apply simp
  apply (simp add: zone_delay_def zone_step_def zone_set_def step_from_def)
  oops

lemma
 "\<exists> u \<in> Z. A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'"
 if "u' \<in> zone_step A (l, g, a, r, l') Z" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using that by (auto simp: zone_delay_def zone_step_def zone_set_def step_from_def)

lemma stepz_from_poststable:
 "\<exists> u \<in> Z. A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'"
 if "u' \<in> Z'" "A \<turnstile> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'"
  using that(2,1) by cases (auto simp: zone_delay_def zone_step_def zone_set_def step_from_def)

lemma is_run_from_locs:
  "is_run_from A xs ts \<Longrightarrow> smap fst xs = smap fst ts"
  apply (coinduction arbitrary: xs ts rule: stream.coinduct)
  subgoal for xs ts
    by (inst_existentials "stl xs" "stl ts") (auto elim: is_run_from.cases)
  done
term "(\<lambda> (l, g, a, r, l') (_, u). (l', SOME u'. A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u'))"
term "sscan"
definition
  "gen_run A xs x =
    x ## sscan (\<lambda> (l, g, a, r, l') (_, u). (l', SOME u'. A \<turnstile> u \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u')) xs x"

definition
  "gen_zrun A xs x = x ##
  sscan (
    \<lambda> (l, g, a, r, l') (_, Z).
      (l', zone_set ((Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}) \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'})
  ) xs x"

lemma is_run_from_is_zrun:
  "is_run_from A ((l, u) ## xs) ts \<Longrightarrow> u \<in> Z \<Longrightarrow> is_zrun A (gen_zrun A ts (l, Z))"
proof (coinduction arbitrary: l u Z ts xs)
  case prems: is_zrun
  from is_run_from.cases[OF prems(1)] obtain uu ll g a1 r l2 u2 xs1 ts' where guessed:
    "(l, u) ## xs = (ll, uu) ## (l2, u2) ## xs1"
    "ts = (ll, g, a1, r, l2) ## ts'"
    "A \<turnstile> uu \<rightarrow>\<^bsub>(ll, g, a1, r, l2)\<^esub> u2"
    "is_run_from A ((l2, u2) ## xs1) ts'" .
  then obtain l' Z' l'' Z'' xs' a where
    "gen_zrun A ts (l, Z) = (l, Z) ## (l'', Z'') ## xs'"
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>"
    "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>"
    "(l'', Z'') ## xs' = gen_zrun A (stl ts) (l'', Z'')"
    "Z'' = zone_step A (l, g, a1, r, l2) Z"
    "l2 = l''"
    apply atomize_elim
    unfolding gen_zrun_def zone_step_def
    apply (subst stream.collapse[symmetric])
    apply (simp add: step_z.simps)
    apply (cases "shd ts")
    by (auto elim: step_from_cases)
  with guessed prems(2) show ?case
    apply simp
    apply (inst_existentials l' Z' a l'' Z'' xs')
    by (fastforce dest: step_from_complete)+
qed

lemma is_run_from_abstract:
  "is_run_from A ((l, u) ## xs) ts \<Longrightarrow> u \<in> Z
  \<Longrightarrow> stream_all2 (\<lambda> (l, u) (l', Z). l = l' \<and> u \<in> Z) ((l, u) ## xs) (gen_zrun A ts (l, Z))"
proof (coinduction arbitrary: l u Z ts xs rule: stream.rel_coinduct)
  case prems: Eq_stream
  from is_run_from.cases[OF prems(1)] obtain uu ll g a1 r l2 u2 xs1 ts' where guessed:
    "(l, u) ## xs = (ll, uu) ## (l2, u2) ## xs1"
    "ts = (ll, g, a1, r, l2) ## ts'"
    "A \<turnstile> uu \<rightarrow>\<^bsub>(ll, g, a1, r, l2)\<^esub> u2"
    "is_run_from A ((l2, u2) ## xs1) ts'" .
  then obtain l' Z' l'' Z'' xs' a where
    "gen_zrun A ts (l, Z) = (l, Z) ## (l'', Z'') ## xs'"
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>"
    "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>"
    "(l'', Z'') ## xs' = gen_zrun A (stl ts) (l'', Z'')"
    "Z'' = zone_step A (l, g, a1, r, l2) Z"
    "l2 = l''"
    apply atomize_elim
    unfolding gen_zrun_def zone_step_def
    apply (subst stream.collapse[symmetric])
    apply (simp add: step_z.simps)
    apply (cases "shd ts")
    by (auto elim: step_from_cases)
  with guessed prems(2) show ?case
    apply simp
    apply (inst_existentials l' Z' a l'' Z'' xs')
    by (fastforce dest: step_from_complete)+
qed

locale Zone_Step_Defs =
  fixes A :: "('a, 'c, 't :: time, 's) ta"
    and step :: "('a, 'c, 't, 's) transition \<Rightarrow> ('c, 't) zone \<Rightarrow> ('c, 't) zone"
begin

inductive stepz_from ::
  "('c, ('t::time)) zone \<Rightarrow> _ \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
  ("_ \<leadsto>\<^bsub>_\<^esub> _" [61,61,61] 61)
where
  "Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> step (l, g, a, r, l') Z"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"

inductive is_stepsz_from where
  Single: "is_stepsz_from [x] []" |
  Cons: "Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z' \<Longrightarrow> is_stepsz_from ((l', Z') # xs) ts
  \<Longrightarrow> is_stepsz_from ((l, Z) # (l', Z') # xs) ((l, g, a, r, l') # ts)"

lemmas [intro] = is_stepsz_from.intros

coinductive is_zrun_from where
  "Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z' \<Longrightarrow> is_zrun_from ((l', Z') ## xs) ts
  \<Longrightarrow> is_zrun_from ((l, Z) ## (l', Z') ## xs) ((l, g, a, r, l') ## ts)"

end (* End of Zone Step Defs *)


locale Zone_Step = Zone_Step_Defs +
  fixes Z\<^sub>0
  assumes poststable: "u' \<in> Z' \<Longrightarrow> Z \<leadsto>\<^bsub>t\<^esub> Z' \<Longrightarrow> \<exists> u. u \<in> Z \<and> A \<turnstile> u \<rightarrow>\<^bsub>t\<^esub> u'"
      and finite_reachable: "finite {Z. (\<lambda> Z Z'. \<exists> t. Z \<leadsto>\<^bsub>t\<^esub> Z')\<^sup>*\<^sup>* Z\<^sub>0 Z}"
      and finite_transitions: "finite {(l, g, a, r, l'). A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'}"
begin

lemma is_zrun_from_transitions:
  assumes "is_zrun_from xs ts"
  shows "pred_stream (\<lambda> (l, g, a, r, l'). A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l') ts"
  using assms by (coinduction arbitrary: xs ts) (auto elim: stepz_from.cases is_zrun_from.cases)

lemma is_zrun_from_reachable':
  assumes "is_zrun_from ((l, Z) ## xs) ts" "(\<lambda> Z Z'. \<exists> t. Z \<leadsto>\<^bsub>t\<^esub> Z')\<^sup>*\<^sup>* Z\<^sub>0 Z"
  shows
    "pred_stream (\<lambda> (l', Z). (\<lambda> Z Z'. \<exists> t. Z \<leadsto>\<^bsub>t\<^esub> Z')\<^sup>*\<^sup>* Z\<^sub>0 Z \<and> (\<exists> l g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l')) xs"
  using assms
  by (coinduction arbitrary: l Z xs ts)
     (force elim: is_zrun_from.cases stepz_from.cases intro: rtranclp.intros(2)) (* Slow *)

lemma is_zrun_from_reachable:
  assumes "is_zrun_from ((l\<^sub>0, Z\<^sub>0) ## xs) ts"
  shows
    "pred_stream (\<lambda> (l', Z). (\<lambda> Z Z'. \<exists> t. Z \<leadsto>\<^bsub>t\<^esub> Z')\<^sup>*\<^sup>* Z\<^sub>0 Z \<and> (\<exists> l g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l')) xs"
  by (rule is_zrun_from_reachable'[OF assms]) blast

lemma is_zrun_from_finite_state_set:
  assumes "is_zrun_from ((l\<^sub>0, Z\<^sub>0) ## xs) ts"
  shows "finite (sset ((l\<^sub>0, Z\<^sub>0) ## xs))"
proof -
  let ?S = "{(l', Z). (\<lambda> Z Z'. \<exists> t. Z \<leadsto>\<^bsub>t\<^esub> Z')\<^sup>*\<^sup>* Z\<^sub>0 Z \<and> (\<exists> l g a r. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l')}"
  from is_zrun_from_reachable[OF assms] have "sset xs \<subseteq> ?S" unfolding stream.pred_set by auto
  moreover have "finite ?S"
    using finite_reachable finite_transitions [[simproc add: finite_Collect]] by auto
  ultimately show ?thesis by (auto intro: finite_subset)
qed

lemma is_zrun_from_decomp:
  assumes "is_zrun_from (xs @- ys) ts" "xs \<noteq> []"
  shows
    "is_stepsz_from xs (stake (length xs - 1) ts) \<and> is_zrun_from ys (sdrop (length xs) ts)
     \<and> (case last xs of (l, Z) \<Rightarrow> case shd ys of (l', Z') \<Rightarrow> \<exists> g a r. Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z' \<and> snth ts (length xs - 1) = (l, g, a, r, l'))"
using assms(2,1)
proof (induction xs arbitrary: ts rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: is_zrun_from.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: is_zrun_from.cases)
qed

lemma is_zrun_from_decomp':
  assumes "is_zrun_from (xs @- ys) ts" "xs \<noteq> []"
  shows "\<exists> ts'. is_stepsz_from xs ts' \<and> set ts' \<subseteq> sset ts"
  using is_zrun_from_decomp[OF assms] by (inst_existentials "stake (length xs - 1) ts", blast) rule

lemma is_stepsz_from_append_single:
  assumes
    "is_stepsz_from xs ts"
    "case last xs of (l, Z) \<Rightarrow> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'"
    "xs \<noteq> []"
  shows "is_stepsz_from (xs @ [(l', Z')]) (ts @ [(fst (last xs), g, a, r, l')])"
  using assms(3,1,2)
  by (induction xs arbitrary: ts rule: list_nonempty_induct) (auto 4 4 elim: is_stepsz_from.cases)

lemma is_stepsz_from_extend_run:
  assumes
    "is_stepsz_from xs ts"
    "case last xs of (l, Z) \<Rightarrow> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'"
    "is_zrun_from ((l', Z') ## ys) ts'"
    "xs \<noteq> []"
  shows "is_zrun_from (xs @- (l', Z') ## ys) (ts @- (fst (last xs), g, a, r, l') ## ts')"
  using assms(4,1-3)
  by (induction xs arbitrary: ts rule: list_nonempty_induct)
     (auto 4 4 elim: is_stepsz_from.cases intro: is_zrun_from.intros)

lemma is_stepsz_from_cycle:
  assumes
    "is_stepsz_from xs ts"
    "case last xs of (l, Z) \<Rightarrow> case hd xs of (l', Z') \<Rightarrow> Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'"
    "xs \<noteq> []"
  shows "is_zrun_from (cycle xs) (cycle (ts @ [(fst (last xs), g, a, r, fst (hd xs))]))"
  using assms
proof (coinduction arbitrary: g a r xs ts)
  case is_zrun_from
  then show ?case
    apply (rewrite at \<open>cycle xs\<close> stream.collapse[symmetric])
    apply (rewrite at \<open>stl (cycle xs)\<close> stream.collapse[symmetric])
    apply clarsimp
    subgoal for l' Z' l Z
      apply (erule is_stepsz_from.cases)
      subgoal for x
        apply simp
        apply (inst_existentials g a r "cycle [(l, g, a, r, l)]")
          apply (subst cycle_Cons, simp; fail)
         apply assumption
        apply (rule disjI1)
        apply (inst_existentials g a r "[(l, Z)]")
         apply (subst (2) cycle_Cons, simp; fail)
        apply (rule exI[where x = "[]"])
        by auto
      apply simp
      subgoal for _ _ g' a' r' l'' Z'' xs' ts'
        apply (inst_existentials g' a' r' "cycle (ts' @ [(l', g, a, r, l), (l, g', a', r', l'')])")
          apply (subst cycle_Cons, simp; fail)
         apply assumption
        apply (rule disjI1)
        apply (inst_existentials g' a' r' "(l'', Z'') # xs' @ [(l, Z)]")
         apply (subst cycle_Cons, simp; fail)
        apply (inst_existentials "ts' @ [(l', g, a, r, l)]")
        using is_stepsz_from_append_single by fastforce+
      done
    done
qed

lemma is_zrun_from_stl:
  "is_zrun_from (stl xs) (stl ts)" if "is_zrun_from xs ts"
  using that by (auto elim: is_zrun_from.cases)

lemma is_zrun_from_sdrop:
  "is_zrun_from (sdrop n xs) (sdrop n ts)" if "is_zrun_from xs ts"
  using that by (induction n arbitrary: xs ts) (auto intro: is_zrun_from_stl)

paragraph \<open>Infinte Paths in the Simulation Graph contain cycles\<close>

lemma is_zrun_from_finite_state_set_cycle:
  assumes "is_zrun_from ((l\<^sub>0, Z\<^sub>0) ## xs) ts"
  shows
  "\<exists> ys zs ts'.
    is_zrun_from ((l\<^sub>0, Z\<^sub>0) ## ys @- cycle zs) ts'
  \<and> set ys \<union> set zs \<subseteq> {(l\<^sub>0, Z\<^sub>0)} \<union> sset xs \<and> sset ts' \<subseteq> sset ts"
proof -
  from is_zrun_from_finite_state_set[OF assms] have "finite (sset ((l\<^sub>0, Z\<^sub>0) ## xs))" .
  then have "\<not> sdistinct ((l\<^sub>0, Z\<^sub>0) ## xs)"
    by (auto dest: sdistinct_infinite_sset)
  from not_sdistinct_decomp[OF this] obtain ws ys x zs where
    "(l\<^sub>0, Z\<^sub>0) ## xs = ws @- x ## ys @- x ## zs" .
  then have decomp: "(l\<^sub>0, Z\<^sub>0) ## xs = (ws @ [x]) @- ys @- x ## zs"
    by simp
  then have *: "(l\<^sub>0, Z\<^sub>0) ## tl (ws @ [x]) @- xs = (ws @ [x]) @- xs" for xs
    by (metis append_is_Nil_conv list.simps(3) shift_simps(1,2) stream.exhaust_sel stream.sel(1))
  from is_zrun_from_decomp[OF assms[unfolded decomp]] obtain l Z  l' Z'  g a r where decomp_first:
    "is_stepsz_from (ws @ [(l, Z)]) (stake (length ws) ts)"
    "is_zrun_from (ys @- (l, Z) ## zs) (sdrop (length ws) (stl ts))"
    "x = (l, Z)"
    "(if ys = [] then shd ((l, Z) ## zs) else hd ys) = (l', Z')"
    "Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'"
    "ts !! length ws = (l, g, a, r, l')"
    by clarsimp
  from is_zrun_from_sdrop[OF assms, of "length (ws @ [x])"] have
    "is_zrun_from (sdrop (length ws) xs) (sdrop (length ws) (stl ts))"
    by clarsimp
  moreover from decomp have "sdrop (length ws) xs = ys @- x ## zs"
    apply (cases ws)
     apply simp
    apply simp
    by (subst sdrop_shift, simp, simp add: Nitpick.size_list_simp(2))
  ultimately have "is_zrun_from ((ys @ [x]) @- zs) (sdrop (length ws) (stl ts))" by simp
  from is_zrun_from_decomp'[OF this] obtain ts' where
    "is_stepsz_from (ys @ [x]) ts'"
    "set ts' \<subseteq> sset (sdrop (length ws) (stl ts))"
    by clarsimp
  from is_stepsz_from_cycle[OF this(1)] decomp_first have
    "is_zrun_from (cycle (ys @ [x]))
     (cycle (ts' @ [(fst (last (ys @ [x])), g, a, r, fst (hd (ys @ [x])))]))"
    by (force split: if_split_asm)
  with
    is_stepsz_from_extend_run[
      of "(ws @ [x])" "(stake (length ws) ts)" g a r l' Z' "stl (cycle (ys @ [x]))"
         "cycle (ts' @ [(fst (last (ys @ [x])), g, a, r, fst (hd (ys @ [x])))])"
    ] decomp_first
  have
    "is_zrun_from ((ws @ [x]) @- cycle (ys @ [x]))
      (stake (
          length (ws @ [x])) ts
          @- cycle (ts' @ [(fst (last (ys @ [x])), g, a, r, fst (hd (ys @ [x])))]
      ))"
    apply (simp split: if_split_asm)
    subgoal premises prems
    proof -
      have "stake (length ws) ts @ [(l', g, a, r, l')] = shd ts # stake (length ws) (stl ts)"
        by (metis prems(2) stake.simps(2) stake_Suc)
      then have
        "stake (length ws) ts @- [(l', g, a, r, l')] @- cycle (ts' @ [(l', g, a, r, l')])
       = shd ts ## stake (length ws) (stl ts) @- cycle (ts' @ [(l', g, a, r, l')])"
        by (simp del: shift.simps(2) add: shift.simps(2)[symmetric] shift_append[symmetric])
      with prems show ?thesis
        using cycle_Cons[of "(l', Z')" "[]", simplified] by auto
    qed
    subgoal premises prems
    proof -
      have
        "ws @- (l, Z) ## (l', Z') ## cycle (tl ys @ [(l, Z), (l', Z')])
       = ws @- (l, Z) ## cycle (ys @ [(l, Z)])"
        unfolding \<open>hd ys = _\<close>[symmetric] using \<open>ys \<noteq> []\<close> by (subst (2) cycle.ctr) simp
      moreover have
        "shd ts ## stake (length ws) (stl ts) @- cycle (ts' @ [(l, g, a, r, l')])
       = stake (length ws) ts @- (l, g, a, r, l') ## cycle (ts' @ [(l, g, a, r, l')])"
        unfolding \<open>ts !! _ = _\<close>[symmetric]  stake_Suc[symmetric] using stake_Suc[of "length ws" ts]
        by simp (metis (no_types) scons_eq_shift shift.simps(1) shift_append)
      ultimately show ?thesis using prems by simp
    qed
    done
  with decomp show ?thesis
    apply (inst_existentials
        "tl (ws @ [x])" "(ys @ [x])"
        "(stake (length (ws @ [x])) ts
      @- cycle (ts' @ [(fst (last (ys @ [x])), g, a, r, fst (hd (ys @ [x])))]))"
        )
      apply (simp add: *)
     apply (cases ws; force)
    apply (auto intro: shd_sset)
      apply (metis (no_types, lifting)
        Cons_eq_append_conv decomp_first(3,4,6) fst_conv hd_append2 list.sel(1) snth_sset
        stream.sel(1)
        )
    using set_sset_stake[of "length ws"] sset_sdrop \<open>set ts' \<subseteq> _\<close> by - (rule stl_sset, fastforce)+
qed

paragraph \<open>Cycles in the Simulation Graph Contain Pre-stable Cycles\<close>

lemma is_stepsz_from_prestable:
  "\<exists> u \<in> Z. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" if
  "is_stepsz_from xs ts" "hd xs = (l, Z)" "last xs = (l', Z')" "u' \<in> Z'"
using that
proof (induction arbitrary: l Z l' Z')
  case (Single x)
  then show ?case by auto
next
  case (Cons Z l g a r l' Z' xs ts)
  then show ?case
    by (clarsimp split: if_split_asm) (blast intro: stepz_from_steps dest: poststable[rotated])+
qed

lemma
  "\<exists> u \<in> Z. \<exists> l' u'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<and> A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l, u\<rangle>" if
  assms: "is_stepsz_from xs ts" "hd xs = last xs" "hd xs = (l, Z)" "Z \<noteq> {}" "length xs > 1"
proof -
  from that obtain g a r l' Z' ts' where tail:
    "xs = (l, Z) # (l', Z') # tl (tl xs)" "Z \<leadsto>\<^bsub>(l, g, a, r, l')\<^esub> Z'"
    "is_stepsz_from ((l', Z') # tl (tl xs)) ts'"
    by - (erule is_stepsz_from.cases, auto)
  obtain u u' where
    "A \<turnstile>' \<langle>l', u\<rangle> \<rightarrow>* \<langle>l, u'\<rangle>" "u \<in> Z'" "u' \<in> Z"
    using is_stepsz_from_prestable[OF tail(3), of l' Z' l Z] \<open>xs = _\<close> assms(2-)
    by atomize_elim (cases "tl (tl xs)", auto)
  moreover from poststable[OF \<open>u \<in> Z'\<close> tail(2)] obtain u1 where
    "u1 \<in> Z" "A \<turnstile> u1 \<rightarrow>\<^bsub>(l, g, a, r, l')\<^esub> u"
    by atomize_elim
  ultimately show ?thesis
oops

end (* Zone Step *)

end (* Theory *)
