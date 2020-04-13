theory Simulation_Graphs_TA
  imports Simulation_Graphs DBM_Zone_Semantics Approx_Beta
begin

section \<open>Instantiation of Simulation Locales\<close>

inductive step_trans ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> (('c, 't) cconstraint \<times> 'a \<times> 'c list)
  \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>t \<langle>_, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<lbrakk>A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'; u \<turnstile> g; u' \<turnstile> inv_of A l'; u' = [r \<rightarrow> 0]u\<rbrakk>
  \<Longrightarrow> (A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>(g,a,r)\<^esub> \<langle>l', u'\<rangle>)"

inductive step_trans' ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> ('c, 't) cconstraint \<times> 'a \<times> 'c list
  \<Rightarrow> 's \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>'' \<langle>_, _\<rangle> \<rightarrow>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  step': "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile>\<^sub>t \<langle>l', u'\<rangle> \<rightarrow>\<^bsub>t\<^esub> \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l'', u''\<rangle>"

inductive step_trans_z ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone
  \<Rightarrow> (('c, 't) cconstraint \<times> 'a \<times> 'c list) action \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  step_trans_t_z:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l, Z\<^sup>\<up> \<inter> {u. u \<turnstile> inv_of A l}\<rangle>" |
  step_trans_a_z:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l', zone_set (Z \<inter> {u. u \<turnstile> g}) r \<inter> {u. u \<turnstile> inv_of A l'}\<rangle>"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"

inductive step_trans_z' ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, ('t::time)) zone \<Rightarrow> (('c, 't) cconstraint \<times> 'a \<times> 'c list)
  \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile>'' \<langle>_, _\<rangle> \<leadsto>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  step_trans_z':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l, Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z'\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>t\<^esup> \<langle>l', Z''\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z''\<rangle>"

lemmas [intro] =
  step_trans.intros
  step_trans'.intros
  step_trans_z.intros
  step_trans_z'.intros

context
  notes [elim!]  =
    step.cases step_t.cases
    step_trans.cases step_trans'.cases step_trans_z.cases step_trans_z'.cases
begin

lemma step_trans_t_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l',Z'\<rangle> \<Longrightarrow> \<forall> u' \<in> Z'. \<exists> u \<in> Z. \<exists> d.  A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l',u'\<rangle>"
  by (auto 4 5 simp: zone_delay_def zone_set_def)

lemma step_trans_a_z_sound:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>t\<^esup> \<langle>l',Z'\<rangle> \<Longrightarrow> \<forall> u' \<in> Z'. \<exists> u \<in> Z. \<exists> d.  A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>t\<^esub> \<langle>l',u'\<rangle>"
  by (auto 4 4 simp: zone_delay_def zone_set_def)

lemma step_trans_a_z_complete:
  "A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>t\<^esub> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>t\<^esup> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  by (auto 4 4 simp: zone_delay_def zone_set_def elim!: step_a.cases)

lemma step_trans_t_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  by (auto 4 4 simp: zone_delay_def zone_set_def elim!: step_a.cases)

lemma step_trans_t_z_iff:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l', Z'\<rangle> = A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>"
  by auto

lemma step_z_complete:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<Longrightarrow> u \<in> Z \<Longrightarrow> \<exists> Z' t. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  by (auto 4 4 simp: zone_delay_def zone_set_def elim!: step_a.cases)

lemma step_trans_a_z_exact:
  "u' \<in> Z'" if "A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>t\<^esub> \<langle>l', u'\<rangle>" "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>t\<^esup> \<langle>l', Z'\<rangle>" "u \<in> Z"
  using that by (auto 4 4 simp: zone_delay_def zone_set_def)

lemma step_trans_t_z_exact:
  "u' \<in> Z'" if "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', u'\<rangle>" "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l', Z'\<rangle>" "u \<in> Z"
  using that by (auto simp: zone_delay_def)

lemma step_trans_z'_exact:
  "u' \<in> Z'" if "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l', u'\<rangle>" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>" "u \<in> Z"
  using that by (auto 4 4 simp: zone_delay_def zone_set_def)

lemma step_trans_z_step_z_action:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l',Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l', Z'\<rangle>"
  using that by auto

lemma step_trans_z_step_z:
  "\<exists> a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>"
  using that by auto

lemma step_z_step_trans_z_action:
  "\<exists> g r. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l', Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l',Z'\<rangle>"
  using that by (auto 4 4)

lemma step_z_step_trans_z:
  "\<exists> t. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle>"
  using that by cases auto

end (* Automation *)

lemma step_z'_step_trans_z':
  "\<exists> t. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z''\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z''\<rangle>"
  using that unfolding step_z'_def
  by (auto dest!: step_z_step_trans_z_action simp: step_trans_t_z_iff[symmetric])

lemma step_trans_z'_step_z':
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z''\<rangle>" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z''\<rangle>"
  using that unfolding step_z'_def
  by (auto elim!: step_trans_z'.cases dest!: step_trans_z_step_z_action simp: step_trans_t_z_iff)

lemma step_trans_z_determ:
  "Z1 = Z2" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z1\<rangle>" "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z2\<rangle>"
  using that by (auto elim!: step_trans_z.cases)

lemma step_trans_z'_determ:
  "Z1 = Z2" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z1\<rangle>" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z2\<rangle>"
  using that by (auto elim!: step_trans_z'.cases step_trans_z.cases)

lemma (in Alpha_defs) step_trans_z_V: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l',Z'\<rangle> \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> Z' \<subseteq> V"
  by (induction rule: step_trans_z.induct; blast intro!: reset_V le_infI1 up_V)

subsection \<open>Additional Lemmas on Regions\<close>

context AlphaClosure
begin

inductive step_trans_r ::
  "('a, 'c, t, 's) ta \<Rightarrow> _ \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> (('c, t) cconstraint \<times> 'a \<times> 'c list) action
  \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_,_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61,61,61] 61)
where
  step_trans_t_r:
  "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l,R'\<rangle>" if
  "valid_abstraction A X (\<lambda> x. real o k x)" "R \<in> \<R> l" "R' \<in> Succ (\<R> l) R" "R' \<subseteq> \<lbrace>inv_of A l\<rbrace>" |
  step_trans_a_r:
  "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l', R'\<rangle>" if
  "valid_abstraction A X (\<lambda> x. real o k x)" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "R \<in> \<R> l"
  "R \<subseteq> \<lbrace>g\<rbrace>" "region_set' R r 0 \<subseteq> R'" "R' \<subseteq> \<lbrace>inv_of A l'\<rbrace>" "R' \<in> \<R> l'"

lemmas [intro] = step_trans_r.intros

lemma step_trans_t_r_iff[simp]:
  "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l',R'\<rangle> = A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l',R'\<rangle>"
  by (auto elim!: step_trans_r.cases)

lemma step_trans_r_step_r_action:
  "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l',R'\<rangle>" if "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l',R'\<rangle>"
  using that by (auto elim: step_trans_r.cases)

lemma step_r_step_trans_r_action:
  "\<exists> g r. A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l',R'\<rangle>" if "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l',R'\<rangle>"
  using that by (auto elim: step_trans_r.cases)

inductive step_trans_r' ::
  "('a, 'c, t, 's) ta \<Rightarrow> _ \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> ('c, t) cconstraint \<times> 'a \<times> 'c list
  \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_,_ \<turnstile>'' \<langle>_, _\<rangle> \<leadsto>\<^bsup>_\<^esup> \<langle>_, _\<rangle>" [61,61,61,61,61] 61)
where
  "A,\<R> \<turnstile>' \<langle>l,R\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l',R''\<rangle>" if "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l,R'\<rangle>" "A,\<R> \<turnstile> \<langle>l,R'\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>t\<^esup> \<langle>l', R''\<rangle>"

lemma step_trans_r'_step_r':
  "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^sub>a \<langle>l',R'\<rangle>" if "A,\<R> \<turnstile>' \<langle>l,R\<rangle> \<leadsto>\<^bsup>(g,a,r)\<^esup> \<langle>l',R'\<rangle>"
  using that by cases (auto dest: step_trans_r_step_r_action intro!: step_r'.intros)

lemma step_r'_step_trans_r':
  "\<exists> g r. A,\<R> \<turnstile>' \<langle>l,R\<rangle> \<leadsto>\<^bsup>(g,a,r)\<^esup> \<langle>l',R'\<rangle>" if "A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^sub>a \<langle>l',R'\<rangle>"
  using that by cases (auto dest: step_r_step_trans_r_action intro!: step_trans_r'.intros)

lemma step_trans_a_r_sound:
  assumes "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>a\<^esup> \<langle>l',R'\<rangle>"
  shows "\<forall> u \<in> R. \<exists> u' \<in> R'. A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l',u'\<rangle>"
using assms proof cases
  case A: (step_trans_a_r g a r)
  show ?thesis
  unfolding A(1) proof
    fix u assume "u \<in> R"
    from \<open>u \<in> R\<close> A have "u \<turnstile> g" "[r\<rightarrow>0]u \<turnstile> inv_of A l'" "[r\<rightarrow>0]u \<in> R'"
      unfolding region_set'_def ccval_def by auto
    with A show "\<exists>u'\<in>R'. A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>(g,a,r)\<^esub> \<langle>l',u'\<rangle>"
      by auto
  qed
qed

lemma step_trans_r'_sound:
  assumes "A,\<R> \<turnstile>' \<langle>l, R\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', R'\<rangle>"
  shows "\<forall>u\<in>R. \<exists>u'\<in>R'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l', u'\<rangle>"
  using assms by cases (auto 6 0 dest!: step_trans_a_r_sound step_t_r_sound)

end (* Alpha Closure *)

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

lemma regions_poststable1:
  assumes
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsup>a\<^esup> \<langle>l',Z'\<rangle>" "Z \<subseteq> V" "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}"
  shows "\<exists> R \<in> \<R> l. A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsup>a\<^esup> \<langle>l',R'\<rangle> \<and> R \<inter> Z \<noteq> {}"
using assms proof (induction A \<equiv> A l \<equiv> l _ _ l' \<equiv> l' _rule: step_trans_z.induct)
  case A: (step_trans_t_z Z)
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
  case A: (step_trans_a_z g a r Z)
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
  from A valid_abstraction \<open>R \<in> _\<close> * have "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>(g,a,r)\<^esup> \<langle>l', R'\<rangle>"
    by (auto simp: comp_def \<open>_ = R'\<close> \<open>_ = R\<close>)
  with \<open>R \<in> _\<close> \<open>u \<in> R\<close> \<open>u \<in> Z\<close> show ?case by - (rule bexI[where x = R]; auto)
qed

lemma regions_poststable':
  assumes
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',Z'\<rangle>" "Z \<subseteq> V" "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}"
  shows "\<exists> R \<in> \<R> l. A,\<R> \<turnstile> \<langle>l,R\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',R'\<rangle> \<and> R \<inter> Z \<noteq> {}"
  using assms
  by (cases a)
     (auto dest!: regions_poststable1 dest: step_trans_r_step_r_action step_z_step_trans_z_action
           simp: step_trans_t_z_iff[symmetric]
     )

end (* End of context for fixed locations *)

lemma regions_poststable2:
  assumes valid_abstraction: "valid_abstraction A X k"
  and prems: "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>a\<^esup> \<langle>l',Z'\<rangle>" "Z \<subseteq> V" "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}"
    shows "\<exists> R \<in> \<R> l. A,\<R> \<turnstile>' \<langle>l,R\<rangle> \<leadsto>\<^bsup>a\<^esup> \<langle>l',R'\<rangle> \<and> R \<inter> Z \<noteq> {}"
using prems(1) proof (cases)
  case steps: (step_trans_z' Z1)
  with prems have "Z1 \<subseteq> V"
    by (blast dest: step_trans_z_V)
  from regions_poststable1[OF valid_abstraction steps(2) \<open>Z1 \<subseteq> V\<close> prems(3,4)] obtain R1 where R1:
    "R1 \<in> \<R> l" "A,\<R> \<turnstile> \<langle>l, R1\<rangle> \<leadsto>\<^bsup>\<upharpoonleft>a\<^esup> \<langle>l', R'\<rangle>" "R1 \<inter> Z1 \<noteq> {}"
    by auto
  from regions_poststable1[OF valid_abstraction steps(1) \<open>Z \<subseteq> V\<close> R1(1,3)] obtain R where
    "R\<in>\<R> l" "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsup>\<tau>\<^esup> \<langle>l, R1\<rangle>" "R \<inter> Z \<noteq> {}"
    by auto
  with R1(2) show ?thesis
    by (auto intro: step_trans_r'.intros)
qed

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

lemma step_t_r_loc:
  "l' = l" if "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', R'\<rangle>"
  using that by cases auto

lemma \<R>_V:
  "u \<in> V" if "R \<in> \<R> l" "u \<in> R"
  using that unfolding \<R>_def V_def by auto

lemma step_r'_complete:
  assumes "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" "valid_abstraction A X (\<lambda> x. real o k x)" "u \<in> V"
  shows "\<exists> a R'. u' \<in> R' \<and> A,\<R> \<turnstile> \<langle>l, [u]\<^sub>l\<rangle> \<leadsto>\<^sub>a \<langle>l',R'\<rangle>"
  using assms
  apply cases
  apply (drule step_t_r_complete, (rule assms; fail), simp add: V_def)
  apply clarify
  apply (frule step_a_r_complete)
  by (auto dest: step_t_r_loc simp: \<R>_def simp: region_unique intro!: step_r'.intros)

lemma step_r_\<R>:
  "R' \<in> \<R> l'" if "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', R'\<rangle>"
  using that by (auto elim: step_r.cases)

lemma step_r'_\<R>:
  "R' \<in> \<R> l'" if "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^sub>a \<langle>l', R'\<rangle>"
  using that by (auto intro: step_r_\<R> elim: step_r'.cases)

end (* End of Alpha Closure *)

context Regions
begin

lemma closure_parts_mono:
  "{R \<in> \<R> l. R \<inter> Z \<noteq> {}} \<subseteq> {R \<in> \<R> l. R \<inter> Z' \<noteq> {}}" if "Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z \<subseteq> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z'"
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

paragraph \<open>More lemmas on regions\<close>

(* XXX All of these should be considered for moving into the locales for global sets of regions *)
context
  fixes l' :: 's
begin

interpretation regions: Regions_global _ _ _ "k l'"
  by standard (rule finite clock_numbering not_in_X non_empty)+

context
  fixes A :: "('a, 'c, t, 's) ta"
  assumes valid_abstraction: "valid_abstraction A X k"
begin

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
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<alpha>(a)\<^esub> \<langle>l', Closure\<^sub>\<alpha>\<^sub>,\<^sub>l' Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>" "Z \<in> V'"
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
  "\<exists> a. \<exists> R \<in> \<R> l. R \<inter> Z \<noteq> {} \<and> A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^sub>a \<langle>l', R'\<rangle>" if
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle>" "Z \<in> V'" "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}"
proof -
  from that(1) obtain l'' a Z'' where steps:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l'', Z''\<rangle>" "A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<beta>(\<upharpoonleft>a)\<^esub> \<langle>l', Z'\<rangle>"
    unfolding step_z_beta'_def by metis
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

lemmas step_z_beta'_V' = step_z_beta'_V'[OF valid_abstraction clock_numbering_le]

lemma step_trans_z'_closure_subs:
  assumes
    "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>" "Z \<subseteq> V" "\<forall> R \<in> \<R> l. R \<inter> Z \<noteq> {} \<longrightarrow> R \<inter> W \<noteq> {}"
  shows
    "\<exists> W'. A \<turnstile>' \<langle>l, W\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', W'\<rangle> \<and> (\<forall> R \<in> \<R> l'. R \<inter> Z' \<noteq> {} \<longrightarrow> R \<inter> W' \<noteq> {})"
proof -
  from assms(1) obtain W' where step: "A \<turnstile>' \<langle>l, W\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', W'\<rangle>"
    by (auto elim!: step_trans_z.cases step_trans_z'.cases)
  have "R' \<inter> W' \<noteq> {}" if "R' \<in> \<R> l'" "R' \<inter> Z' \<noteq> {}" for R'
  proof -
    from regions_poststable2[OF valid_abstraction assms(1) _ that] \<open>Z \<subseteq> V\<close> obtain R where R:
      "R\<in>\<R> l" "A,\<R> \<turnstile>' \<langle>l, R\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', R'\<rangle>" "R \<inter> Z \<noteq> {}"
      by auto
    with assms(3) obtain u where "u \<in> R" "u \<in> W"
      by auto
    with step_trans_r'_sound[OF R(2)] obtain u' where "u' \<in> R'" "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l', u'\<rangle>"
      by auto
    with step_trans_z'_exact[OF this(2) step \<open>u \<in> W\<close>] show ?thesis
      by auto
  qed
  with step show ?thesis
    by auto
qed

lemma step_trans_z'_closure_eq:
  assumes
    "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>" "Z \<subseteq> V" "W \<subseteq> V" "\<forall> R \<in> \<R> l. R \<inter> Z \<noteq> {} \<longleftrightarrow> R \<inter> W \<noteq> {}"
  shows
    "\<exists> W'. A \<turnstile>' \<langle>l, W\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', W'\<rangle> \<and> (\<forall> R \<in> \<R> l'. R \<inter> Z' \<noteq> {} \<longleftrightarrow> R \<inter> W' \<noteq> {})"
proof -
  from assms(4) have *:
    "\<forall> R \<in> \<R> l. R \<inter> Z \<noteq> {} \<longrightarrow> R \<inter> W \<noteq> {}" "\<forall> R \<in> \<R> l. R \<inter> W \<noteq> {} \<longrightarrow> R \<inter> Z \<noteq> {}"
    by auto
  from step_trans_z'_closure_subs[OF assms(1,2) *(1)] obtain W' where W':
    "A \<turnstile>' \<langle>l, W\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', W'\<rangle>" "(\<forall>R\<in>\<R> l'. R \<inter> Z' \<noteq> {} \<longrightarrow> R \<inter> W' \<noteq> {})"
    by auto
  with step_trans_z'_closure_subs[OF W'(1) \<open>W \<subseteq> V\<close> *(2)] assms(1) show ?thesis
    by (fastforce dest: step_trans_z'_determ)
qed

lemma step_z'_closure_subs:
  assumes 
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" "Z \<subseteq> V" "\<forall> R \<in> \<R> l. R \<inter> Z \<noteq> {} \<longrightarrow> R \<inter> W \<noteq> {}"
  shows
    "\<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<leadsto> \<langle>l', W'\<rangle> \<and> (\<forall> R \<in> \<R> l'. R \<inter> Z' \<noteq> {} \<longrightarrow> R \<inter> W' \<noteq> {})"
  using assms(1)
  by (auto
      dest: step_trans_z'_step_z'
      dest!: step_z'_step_trans_z' step_trans_z'_closure_subs[OF _ assms(2,3)]
     )

end (* Context for automaton *)

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
  "Z' = {}" if "A \<turnstile> \<langle>l, {}\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle>"
  using that
  by (auto
      elim!: step_z.cases
      simp: step_z_beta'_def regions.beta_interp.apx_empty zone_delay_def zone_set_def
     )

end (* End of context for fixed location *)

lemma step_z_beta'_complete:
  assumes "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" "u \<in> Z" "Z \<subseteq> V"
  shows "\<exists> Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
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
  ultimately show ?thesis
    unfolding step_z_beta'_def using \<open>Z \<subseteq> V\<close> apx_subset by blast
qed

end (* End of Regions *)


subsection \<open>Instantiation of Double Simulation\<close>

subsection \<open>Auxiliary Definitions\<close>

definition state_set :: "('a, 'c, 'time, 's) ta \<Rightarrow> 's set" where
  "state_set A \<equiv> fst ` (fst A) \<union> (snd o snd o snd o snd) ` (fst A)"

lemma finite_trans_of_finite_state_set:
  "finite (state_set A)" if "finite (trans_of A)"
  using that unfolding state_set_def trans_of_def by auto

lemma state_setI1:
  "l \<in> state_set A" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using that unfolding state_set_def trans_of_def image_def by (auto 4 4)

lemma state_setI2:
  "l' \<in> state_set A" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'"
  using that unfolding state_set_def trans_of_def image_def by (auto 4 4)

lemma (in AlphaClosure) step_r'_state_set:
  "l' \<in> state_set A" if "A,\<R> \<turnstile> \<langle>l, R\<rangle> \<leadsto>\<^sub>a \<langle>l', R'\<rangle>"
  using that by (blast intro: state_setI2 elim: step_r'.cases)

lemma (in Regions) step_z_beta'_state_set2:
  "l' \<in> state_set A" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle>"
  using that unfolding step_z_beta'_def by (force simp: state_set_def trans_of_def)

subsection \<open>Instantiation\<close>

locale Regions_TA = Regions X _ _  k for X :: "'c set" and k :: "'s \<Rightarrow> 'c \<Rightarrow> nat" +
  fixes A :: "('a, 'c, t, 's) ta"
  assumes valid_abstraction: "valid_abstraction A X k"
    and finite_state_set: "finite (state_set A)"
begin

(* XXX Bundle this? *)
no_notation Regions_Beta.part ("[_]\<^sub>_" [61,61] 61)
notation part'' ("[_]\<^sub>_" [61,61] 61)

(* XXX Move *)
lemma step_z_beta'_state_set1:
  "l \<in> state_set A" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle>"
  using that unfolding step_z_beta'_def by (force simp: state_set_def trans_of_def)

sublocale sim: Double_Simulation_paired
  "\<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"  \<comment> \<open>Concrete step relation\<close>
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A,\<R> \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>a \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  \<comment> \<open>Step relation for the first abstraction layer\<close>
  "\<lambda> (l, R). l \<in> state_set A \<and> R \<in> \<R> l" \<comment> \<open>Valid states of the first abstraction layer\<close>
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  \<comment> \<open>Step relation for the second abstraction layer\<close>
  "\<lambda> (l, Z). l \<in> state_set A \<and> Z \<in> V' \<and> Z \<noteq> {}" \<comment> \<open>Valid states of the second abstraction layer\<close>
proof (standard, goal_cases)
  case (1 S T)
  then show ?case
    by (auto dest!: step_r'_sound)
next
  case prems: (2 R' l' Z' l Z)
  from prems(3) have "l \<in> state_set A"
    by (blast intro: step_z_beta'_state_set1)
  from prems show ?case
    unfolding Double_Simulation_paired_Defs.closure'_def
    by (blast dest: beta_alpha_region_step[OF valid_abstraction] step_z_beta'_state_set1)
next
  case prems: (3 l R R')
  then show ?case
    using \<R>_regions_distinct[OF \<R>_def'] by auto
next
  case 4
  have *: "finite (\<R> l)" for l
    unfolding \<R>_def by (intro finite_\<R> finite)
  have
    "{(l, R). l \<in> state_set A \<and> R \<in> \<R> l} = (\<Union> l \<in> state_set A. ((\<lambda> R. (l, R)) ` {R. R \<in> \<R> l}))"
    by auto
  also have "finite \<dots>"
    by (auto intro: finite_UN_I[OF finite_state_set] *)
  finally show ?case by auto
next
  case (5 l Z)
  then show ?case
    apply safe
    subgoal for u
      using region_cover'[of u l] by (auto dest!: V'_V, auto simp: V_def)
    done
qed

sublocale Graph_Defs
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}" .

lemmas step_z_beta'_V' = step_z_beta'_V'[OF valid_abstraction]

lemma step_r'_complete_spec:
  assumes "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l',u'\<rangle>" "u \<in> V"
  shows "\<exists> a R'. u' \<in> R' \<and> A,\<R> \<turnstile> \<langle>l, [u]\<^sub>l\<rangle> \<leadsto>\<^sub>a \<langle>l',R'\<rangle>"
  using assms valid_abstraction by (auto simp: comp_def V_def intro!: step_r'_complete)

end (* Regions TA *)


subsection \<open>Büchi Runs\<close>

locale Regions_TA_Start_State = Regions_TA _ _ _ _ _ A for A :: "('a, 'c, t, 's) ta" +
  fixes l\<^sub>0 :: "'s" and Z\<^sub>0 :: "('c, t) zone"
  assumes start_state: "l\<^sub>0 \<in> state_set A" "Z\<^sub>0 \<in> V'" "Z\<^sub>0 \<noteq> {}"
begin

definition "a\<^sub>0 = from_R l\<^sub>0 Z\<^sub>0"

sublocale sim_complete': Double_Simulation_Finite_Complete_paired
  "\<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"  \<comment> \<open>Concrete step relation\<close>
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A,\<R> \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>a \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  \<comment> \<open>Step relation for the first abstraction layer\<close>
  "\<lambda> (l, R). l \<in> state_set A \<and> R \<in> \<R> l" \<comment> \<open>Valid states of the first abstraction layer\<close>
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  \<comment> \<open>Step relation for the second abstraction layer\<close>
  "\<lambda> (l, Z). l \<in> state_set A \<and> Z \<in> V' \<and> Z \<noteq> {}" \<comment> \<open>Valid states of the second abstraction layer\<close>
  l\<^sub>0 Z\<^sub>0
proof (standard, goal_cases)
  case (1 x y S)
  \<comment> \<open>Completeness\<close>
  then show ?case
    by (force dest: step_z_beta'_complete[rotated 2, OF V'_V])
next
  case 4
  \<comment> \<open>Finiteness\<close>
  (* XXX *)
  have *: "Z \<in> V'" if "A \<turnstile> \<langle>l\<^sub>0, Z\<^sub>0\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l, Z\<rangle>" for l Z
    using that start_state step_z_beta'_V' by (induction rule: rtranclp_induct2) blast+
  have "Z \<in> {Approx\<^sub>\<beta> l Z | Z. Z \<subseteq> V} \<or> (l, Z) = (l\<^sub>0, Z\<^sub>0)"
    if "reaches (l\<^sub>0, Z\<^sub>0) (l, Z)" for l Z
    using that proof (induction rule: rtranclp_induct2)
    case refl
    then show ?case
      by simp
  next
    case prems: (step l Z l' Z')
    from prems(1) have "A \<turnstile> \<langle>l\<^sub>0, Z\<^sub>0\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l, Z\<rangle>"
      by induction (auto intro: rtranclp_trans)
    then have "Z \<in> V'"
      by (rule *)
    with prems show ?case
      unfolding step_z_beta'_def using start_state(2) by (auto 0 1 dest!: V'_V elim!: step_z_V)
  qed
  then have "{(l, Z). reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<and> l \<in> state_set A \<and> Z \<in> V' \<and> Z \<noteq> {}}
    \<subseteq> {(l, Z) | l Z. l \<in> state_set A \<and> Z \<in> {Approx\<^sub>\<beta> l Z | Z. Z \<subseteq> V}} \<union> {(l\<^sub>0, Z\<^sub>0)}"
    by auto
  also have "finite \<dots>" (is "finite ?S")
  proof -
    have "?S = {(l\<^sub>0, Z\<^sub>0)} \<union> \<Union> ((\<lambda> l. (\<lambda> Z. (l, Z)) ` {Approx\<^sub>\<beta> l Z | Z. Z \<subseteq> V}) ` (state_set A))"
      by blast
    also have "finite \<dots>"
      by (blast intro: apx_finite finite_state_set)
    finally show ?thesis .
  qed
  finally show ?case
    by simp
next
  case prems: (2 a a')
  then show ?case
    by (auto intro: step_z_beta'_V' step_z_beta'_state_set2)
next
  case 3
  from start_state show ?case unfolding a\<^sub>0_def by (auto simp: from_R_fst)
qed

sublocale sim_complete_bisim': Double_Simulation_Finite_Complete_Bisim_Cover_paired
  "\<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"  \<comment> \<open>Concrete step relation\<close>
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A,\<R> \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>a \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  \<comment> \<open>Step relation for the first abstraction layer\<close>
  "\<lambda> (l, R). l \<in> state_set A \<and> R \<in> \<R> l" \<comment> \<open>Valid states of the first abstraction layer\<close>
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  \<comment> \<open>Step relation for the second abstraction layer\<close>
  "\<lambda> (l, Z). l \<in> state_set A \<and> Z \<in> V' \<and> Z \<noteq> {}" \<comment> \<open>Valid states of the second abstraction layer\<close>
  l\<^sub>0 Z\<^sub>0
proof (standard, goal_cases)
  case (1 l x l' y S)
  then show ?case
    apply clarify
    apply (drule step_r'_complete_spec, (auto intro: \<R>_V; fail))
    by (auto simp: \<R>_def region_unique)
next
  case (2 l S l' T)
  then show ?case
    by (auto simp add: step_r'_state_set step_r'_\<R>)
next
  case prems: (3 l Z u)
  then show ?case
    using region_cover'[of u l] by (auto dest!: V'_V simp: V_def)+
qed

subsection \<open>State Formulas\<close>

context
  fixes P :: "'s \<Rightarrow> bool" \<comment> \<open>The state property we want to check\<close>
begin

definition "\<phi> = P o fst"

paragraph \<open>State formulas are compatible with closures.\<close>

paragraph \<open>Runs satisfying a formula all the way long\<close>

interpretation G\<^sub>\<phi>: Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> P l'" "(l\<^sub>0, Z\<^sub>0)" .

theorem Alw_ev_mc1:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.sim.Alw_ev (Not \<circ> \<phi>) x\<^sub>0) \<longleftrightarrow> \<not> (P l\<^sub>0 \<and> (\<exists>a. G\<^sub>\<phi>.reachable a \<and> G\<^sub>\<phi>.reaches1 a a))"
  using sim_complete_bisim'.Alw_ev_mc1
  unfolding G\<^sub>\<phi>.reachable_def a\<^sub>0_def sim_complete_bisim'.\<psi>_def \<phi>_def
  by auto

end (* Context for State Formula *)

subsection \<open>Leads-To Properties\<close>

context
  fixes P Q :: "'s \<Rightarrow> bool" \<comment> \<open>The state properties we want to check\<close>
begin

definition "\<psi> = Q o fst"

interpretation G\<^sub>\<psi>: Graph_Defs
  "\<lambda> (l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> Q l'" .

theorem leadsto_mc1:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.sim.leadsto (\<phi> P) (Not \<circ> \<psi>) x\<^sub>0) \<longleftrightarrow>
   (\<nexists>x. reaches (l\<^sub>0, Z\<^sub>0) x \<and> P (fst x) \<and> Q (fst x) \<and> (\<exists>a. G\<^sub>\<psi>.reaches x a \<and> G\<^sub>\<psi>.reaches1 a a))"
  if "\<forall>x\<^sub>0\<in>a\<^sub>0. \<not> sim.sim.deadlock x\<^sub>0"
proof -
  from that have *: "\<forall>x\<^sub>0\<in>Z\<^sub>0. \<not> sim.sim.deadlock (l\<^sub>0, x\<^sub>0)"
    unfolding a\<^sub>0_def by auto
  show ?thesis
    using sim_complete_bisim'.leadsto_mc1[OF *, symmetric, of P Q]
    unfolding \<psi>_def \<phi>_def sim_complete_bisim'.\<phi>'_def sim_complete_bisim'.\<psi>_def a\<^sub>0_def
    by (auto dest: from_R_D from_R_loc)
qed

end (* Context for State Formulae *)

lemma from_R_reaches:
  assumes "sim.sim.Steps.reaches (from_R l\<^sub>0 Z\<^sub>0) b"
  obtains l Z where "b = from_R l Z"
  using assms by cases (fastforce simp: sim.A2'_def dest!: from_R_R_of)+

lemma ta_reaches_ex_iff:
  assumes compatible:
    "\<And>l u u' R.
      u \<in> R \<Longrightarrow> u' \<in> R \<Longrightarrow> R \<in> \<R> l \<Longrightarrow> l \<in> state_set A \<Longrightarrow> P (l, u) = P (l, u')"
  shows
    "(\<exists> x\<^sub>0 \<in> a\<^sub>0. \<exists> l u. sim.sim.reaches x\<^sub>0 (l, u) \<and> P (l, u)) \<longleftrightarrow>
     (\<exists> l Z. \<exists> u \<in> Z. reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<and> P (l, u))"
proof -
  have *: "(\<exists>x\<^sub>0 \<in> a\<^sub>0. \<exists> l u. sim.sim.reaches x\<^sub>0 (l, u) \<and> P (l, u))
    \<longleftrightarrow> (\<exists>y. \<exists>x\<^sub>0\<in>from_R l\<^sub>0 Z\<^sub>0. sim.sim.reaches x\<^sub>0 y \<and> P y)"
    unfolding a\<^sub>0_def by auto
  show ?thesis
    unfolding *
    apply (subst sim_complete_bisim'.sim_reaches_equiv)
    subgoal
      by (simp add: start_state)
    apply (subst sim_complete_bisim'.reaches_ex'[of P])
    unfolding a\<^sub>0_def
     apply clarsimp
    subgoal
      unfolding sim.P1'_def by (clarsimp simp: fst_simp) (metis R_ofI compatible fst_conv)
    apply safe
     apply (rule from_R_reaches, assumption)
    using from_R_fst by (force intro: from_R_val)+
qed

lemma ta_reaches_all_iff:
  assumes compatible:
    "\<And>l u u' R.
      u \<in> R \<Longrightarrow> u' \<in> R \<Longrightarrow> R \<in> \<R> l \<Longrightarrow> l \<in> state_set A \<Longrightarrow> P (l, u) = P (l, u')"
  shows
    "(\<forall> x\<^sub>0 \<in> a\<^sub>0. \<forall> l u. sim.sim.reaches x\<^sub>0 (l, u) \<longrightarrow> P (l, u)) \<longleftrightarrow>
     (\<forall> l Z. reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<longrightarrow> (\<forall> u \<in> Z. P (l, u)))"
proof -
  have *: "(\<forall>x\<^sub>0 \<in> a\<^sub>0. \<forall> l u. sim.sim.reaches x\<^sub>0 (l, u) \<longrightarrow> P (l, u))
    \<longleftrightarrow> (\<forall>y. \<forall>x\<^sub>0\<in>from_R l\<^sub>0 Z\<^sub>0. sim.sim.reaches x\<^sub>0 y \<longrightarrow> P y)"
    unfolding a\<^sub>0_def by auto
  show ?thesis
    unfolding *
    apply (subst sim_complete_bisim'.sim_reaches_equiv)
    subgoal
      by (simp add: start_state)
    apply (subst sim_complete_bisim'.reaches_all''[of P])
    unfolding a\<^sub>0_def
     apply clarsimp
    subgoal
      unfolding sim.P1'_def by (clarsimp simp: fst_simp) (metis R_ofI compatible fst_conv)
    apply auto
    apply (rule from_R_reaches, assumption)
    using from_R_fst by (force intro: from_R_val)+
qed

end (* Reachability Problem precompiled *)

end (* Theory *)