theory Simulation_Graphs_TA
  imports Simulation_Graphs Normalized_Zone_Semantics_Impl_Semantic_Refinement
begin

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

(* XXX Move *)
paragraph \<open>More theorems on closures -- to be moved?\<close>

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
  "Z' = {}" if "A \<turnstile>' \<langle>l, {}\<rangle> \<leadsto>\<^bsub>\<beta>a\<^esub> \<langle>l', Z'\<rangle>"
  using that
  by (auto
      elim!: step_z_beta'.cases step_z.cases
      simp: regions.beta_interp.apx_empty zone_delay_def zone_set_def
     )

end (* End of context for fixed location *)

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

lemma (in Regions) step_z_beta'_state_set:
  "l' \<in> state_set A" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>"
  using that by (force elim!: step_z_beta'.cases simp: state_set_def trans_of_def)

paragraph \<open>\<open>R_of\<close>/\<open>from_R\<close>\<close>

definition "R_of lR = snd ` lR"

definition "from_R l R = {(l, u) | u. u \<in> R}"

lemma from_R_fst:
  "\<forall>x\<in>from_R l R. fst x = l"
  unfolding from_R_def by auto

lemma R_of_from_R [simp]:
  "R_of (from_R l R) = R"
  unfolding R_of_def from_R_def image_def by auto

lemma from_R_loc:
  "l' = l" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

lemma from_R_val:
  "u \<in> Z" if "(l', u) \<in> from_R l Z"
  using that unfolding from_R_def by auto

lemma from_R_R_of:
  "from_R l (R_of S) = S" if "\<forall> x \<in> S. fst x = l"
  using that unfolding from_R_def R_of_def by force

lemma R_ofI[intro]:
  "Z \<in> R_of S" if "(l, Z) \<in> S"
  using that unfolding R_of_def by force

lemma from_R_I[intro]:
  "(l', u') \<in> from_R l' Z'" if "u' \<in> Z'"
  using that unfolding from_R_def by auto

lemma R_of_non_emptyD:
  "a \<noteq> {}" if "R_of a \<noteq> {}"
  using that unfolding R_of_def by simp

subsection \<open>Instantiation\<close>

locale Regions_TA = Regions X _ _  k for X :: "'c set" and k :: "'s \<Rightarrow> 'c \<Rightarrow> nat" +
  fixes A :: "('a, 'c, t, 's) ta"
  assumes valid_abstraction: "valid_abstraction A X k"
    and finite_state_set: "finite (state_set A)"
begin

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

sublocale Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}" "(l\<^sub>0, Z\<^sub>0)" .

lemmas step_z_beta'_V' = step_z_beta'_V'[OF valid_abstraction]

inductive
  steps_z_beta' :: "('a, 'c, t, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> 's \<Rightarrow> ('c, t) zone \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  init: "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>" if "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle>" |
  step: "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>" if "A \<turnstile>' \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l'', Z''\<rangle>" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^sub>\<beta>* \<langle>l', Z'\<rangle>"

paragraph \<open>Lemmas on \<open>P1\<close> and \<open>P2\<close>\<close>

lemma A1_P1 [intro]:
  "P1 b" if "A1 a b"
  using that unfolding P1_def A1_def by (auto elim: step_r'_\<R> step_r'_state_set)

lemma A2_P2 [intro]:
  "P2 b" if "A2 a b"
  using that by (meson P2_def sim_defs(3) step_z_beta'_V' step_z_beta'_state_set)

lemma P2_from_R:
  "\<exists> l' Z'. x = from_R l' Z'" if "P2 x"
  using that unfolding P2_def by (fastforce dest: from_R_R_of)

lemma P2_from_R':
  "\<exists> Z. u \<in> Z \<and> from_R l Z = a" if "P2 a" "(l, u) \<in> a"
  by (metis P2_def R_ofI from_R_R_of fst_eqD that)

lemma P2_non_empty:
  "a \<noteq> {}" if "P2 a"
  using that unfolding P2_def by (auto intro!: R_of_non_emptyD)

lemma P2_V':
  "R_of a \<in> V'" if "P2 a"
  using \<open>P2 a\<close> unfolding P2_def by simp

lemma P1_fst:
  "fst x = fst y" if "x \<in> a" "y \<in> a" "P1 a"
  using that unfolding P1_def by auto

paragraph \<open>Equivalence of step relations\<close>

sublocale Bisimulation_Invariants
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}" A2 "\<lambda> (l, Z) b. b = from_R l Z"
  "\<lambda> (l, Z). Z \<in> V'" "\<lambda> (l, Z). Z \<in> V' \<and> Z \<noteq> {}"
  "\<lambda> lZ. R_of lZ \<in> V'" P2
  apply standard
     apply simp_all
  subgoal for a b a'
    unfolding A2_def
      apply auto
    using from_R_fst by fastforce
  subgoal for a a' b'
    unfolding A2_def
      apply auto
    subgoal premises prems for l1 R l l' aa xa
  proof -
    from prems(6,8) have "R \<noteq> {}"
      by (auto dest: step_z_beta'_empty)
    from prems have "b' = from_R l' (R_of b')"
      by (simp add: from_R_R_of)
    moreover from prems \<open>R \<noteq> {}\<close> from_R_fst[of l1 R] have "l1 = l"
      by (auto 4 3)
    moreover from prems have "R_of b' \<in> V'"
      by (auto intro: step_z_beta'_V')
    ultimately show False
      using prems by fastforce
  qed
  done
  by (auto 4 4 intro: P2_V' step_z_beta'_V' dest:  A2_P2)

sublocale P1_invariant: Graph_Invariant_Strong A1 P1 by standard auto

sublocale P2_invariant: Graph_Invariant_Strong A2 P2 by standard auto

(* XXX Move *)
lemma inj_from_R:
  "inj_on (\<lambda>(l, Z). from_R l Z) {(l, Z). Z \<noteq> {}}"
  unfolding from_R_def by (standard, auto)

(* XXX Move *)
lemma inj:
  "\<forall>a b.
    P2 (case a of (l, Z) \<Rightarrow> from_R l Z) \<and>
    (case b of (l, Z) \<Rightarrow> Z \<in> V' \<and> Z \<noteq> {}) \<and>
    (case a of (l, Z) \<Rightarrow> from_R l Z) = (case b of (l, Z) \<Rightarrow> from_R l Z) \<longrightarrow> a = b"
  unfolding from_R_def by auto

(* XXX Obsolete *)
lemma steps_empty_start:
  "xs = []" if "steps ((l, Z) # xs)" "Z = {}"
  using that by cases (auto dest: step_z_beta'_empty)

(* XXX Obsolete *)
lemma sim_Steps_empty_start:
  "xs = []" if "sim.Steps (from_R l Z # xs)" "Z = {}"
  using that by cases (auto dest: step_z_beta'_empty simp: A2_def)

lemma sim_steps_equiv:
  "steps ((l, Z) # xs) \<longleftrightarrow> sim.Steps (map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs))"
  if "Z \<in> V'"
  using that steps_map_equiv[of "\<lambda> (l, Z). from_R l Z" "(l, Z)" "from_R l Z" xs, OF _ inj] by auto

lemma steps_sim_Steps:
  "sim.Steps (map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs))" if "steps ((l, Z) # xs)" "Z \<in> V'"
  using sim_steps_equiv[OF \<open>Z \<in> V'\<close>] \<open>steps _\<close> by auto

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


paragraph \<open>Auxiliary Lemmas\<close>

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

lemma P2_state_set:
  "l \<in> state_set A" if "P2 (from_R l Z)"
   using that sim.closure_non_empty sim_closure_from_R by fastforce

(* Unused *)
lemma run_map_from_R:
  "map (\<lambda>(x, y). from_R x y) (map (\<lambda> lR. ((THE l. \<forall> x \<in> lR. fst x = l), R_of lR)) xs) = xs"
  if "sim.Steps (x # xs)"
  using P2_invariant.P_invariant_steps[OF that]
  apply (induction xs)
   apply (simp; fail)
  apply simp
  apply (subst (asm) P2_def)
  apply clarify
  apply (rule from_R_R_of)
  apply (rule theI)
  unfolding R_of_def by force+

lemma sim_Steps_from_R:
  "\<exists> ys. xs = map (\<lambda>(l, Z). from_R l Z) ys" if "sim.Steps (from_R l Z # xs)" "Z \<in> V'"
  using steps_map[of "\<lambda> (l, Z). from_R l Z", OF _ inj, of "(l, Z)" xs] that by auto

(* Unused *)
lemma sim_Steps_from_R':
  "\<exists> ys. xs = map (\<lambda>(l, Z). from_R l Z) ys" if "sim.Steps (from_R l Z # xs)"
  using that proof cases
  case Single
  then show ?thesis by simp
next
  case (Cons y ys)
  then have "P2 y" by auto
  then obtain l' Z' where "y = from_R l' Z'"
    by (auto dest: P2_from_R)
  from
    Post_Bisim.steps_map[of "\<lambda> (l, Z). from_R l Z", OF _ inj, of "(l', Z')" ys]
    \<open>sim.Steps (y # ys)\<close> \<open>P2 y\<close>
  obtain zs where "ys = map (\<lambda>(l, Z). from_R l Z) zs"
    by (auto simp: \<open>y = _\<close> P2_def)
  with \<open>xs = _\<close> \<open>y = _\<close> show ?thesis
    by (inst_existentials "(l', Z') # zs") simp
qed

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
  then show ?case by auto
next
  case 4
  from start_state show ?case unfolding a\<^sub>0_def by (auto simp: sim_defs from_R_fst)
qed

sublocale sim_complete_bisim: Double_Simulation_Finite_Complete_Bisim_Cover
  C  -- "Concrete step relation"
  A1 -- "Step relation for the first abstraction layer"
  P1 -- "Valid states of the first abstraction layer"
  A2 -- "Step relation for the second abstraction layer"
  P2 -- "Valid states of the second abstraction layer"
  a\<^sub>0 -- "Start state"
proof (standard, goal_cases)
  case (1 x y S)
  then show ?case
    unfolding C_def P1_def A1_def
    apply clarify
    apply (drule step_r'_complete_spec, (auto intro: \<R>_V; fail))
    apply safe
    subgoal for l1 u1 l2 u2 l a R'
      apply (inst_existentials "from_R l2 R'")
       apply (subst (asm) region_unique[of _ _ _ u1 "R_of S"], simp add: \<R>_def)
      by (auto 4 3 simp: from_R_fst)
    done
next
  case (2 S T)
  then show ?case by auto
next
  case prems: (3 a x)
  then obtain l where l:
    "l \<in> state_set A" "\<forall>x\<in>a. fst x = l"
    unfolding P2_def by auto
  with region_cover'[of "snd x" l] prems have *: "snd x \<in> [snd x]\<^sub>l" "[snd x]\<^sub>l \<in> \<R> l"
    by (fastforce dest: V'_V simp: P2_def V_def R_of_def)+
  with l have "x \<in> from_R l ([snd x]\<^sub>l)"
    unfolding from_R_def using prems(2) by (cases x) auto
  with prems * show ?case
    unfolding P1_def P2_def
    by (inst_existentials "from_R l ([snd x]\<^sub>l)" l) (auto simp: from_R_fst)
qed

context
  fixes \<phi> :: "'s \<times> ('c \<Rightarrow> real) \<Rightarrow> bool" -- "The property we want to check"
  assumes \<phi>_closure_compatible: "x \<in> a \<Longrightarrow> \<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union> sim.closure a. \<phi> x)"
      and sim_closure: "\<Union>sim.closure a\<^sub>0 = a\<^sub>0"
begin

lemma infinite_buechi_run_cycle_iff':
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> sim.run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as a bs. sim.Steps (a\<^sub>0 # as @ a # bs @ [a]) \<and> (\<forall> x \<in> \<Union> sim.closure a. \<phi> x))"
  using sim_complete.infinite_buechi_run_cycle_iff[OF \<phi>_closure_compatible, OF _ sim_closure] .

lemma P2_from_R_list:
  "\<exists> as'. map (\<lambda>(x, y). from_R x y) as' = as" if "list_all P2 as"
  by (rule list_all_map[OF _ that]) (auto dest!: P2_from_R)

theorem infinite_buechi_run_cycle_iff:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> sim.run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> as l Z bs. steps ((l\<^sub>0, Z\<^sub>0) # as @ (l, Z) # bs @ [(l, Z)]) \<and> (\<forall> x \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z. \<phi> (l, x)))"
  unfolding infinite_buechi_run_cycle_iff' sim_steps_equiv[OF start_state(2)]
  apply (simp add: a\<^sub>0_def)
proof (safe, goal_cases)
  case prems: (1 as a bs)
  let ?f = "\<lambda>(x, y). from_R x y"
  from P2_invariant.P_invariant_steps[OF prems(2)] have "list_all P2 (as @ a # bs @ [a])" .
  then have "list_all P2 as" "P2 a" "list_all P2 bs"
    by auto
  then obtain as' l Z bs' where "map ?f as' = as" "a = from_R l Z" "map ?f bs' = bs"
    by atomize_elim (auto dest: P2_from_R_list P2_from_R)
  moreover from \<open>a = _\<close> prems(1) have "\<forall> x \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z. \<phi> (l, x)"
    unfolding cla_def
  proof (clarify, goal_cases)
    case prems2: (1 u R)
    with \<open>P2 a\<close> have "P1 (from_R l R)"
      unfolding P1_def by (auto simp: from_R_fst dest: P2_state_set)
    with prems2 have "from_R l R \<in> sim.closure (from_R l Z)"
      unfolding sim.closure_def by auto
    moreover have "(l, u) \<in> from_R l R"
      using prems2 unfolding from_R_def by auto
    ultimately show ?case
      using prems2(1) by auto
  qed
  ultimately show ?case
    using prems by auto
next
  case (2 as l Z bs)
  then show ?case
    by (inst_existentials "map (\<lambda>(x, y). from_R x y) as")
       (force simp: sim_closure_from_R cla_def dest: from_R_loc from_R_val)
qed

theorem infinite_buechi_run_cycle_iff1:
  "(\<exists> x\<^sub>0 xs. x\<^sub>0 \<in> a\<^sub>0 \<and> sim.run (x\<^sub>0 ## xs) \<and> alw (ev (holds \<phi>)) (x\<^sub>0 ## xs))
  \<longleftrightarrow> (\<exists> l Z. reachable (l, Z) \<and> reaches1 (l, Z) (l, Z) \<and> (\<forall> x \<in> Closure\<^sub>\<alpha>\<^sub>,\<^sub>l Z. \<phi> (l, x)))"
  unfolding infinite_buechi_run_cycle_iff
  apply safe
  subgoal for as l Z bs
    using reachable_cycle_iff[of "(l, Z)"] by auto
  subgoal for l Z
    using reachable_cycle_iff[of "(l, Z)"] by auto
  done

end (* Context for Formula *)


subsection \<open>State Formulas\<close>

context
  fixes P :: "'s \<Rightarrow> bool" -- "The state property we want to check"
begin

definition "\<phi> = P o fst"

paragraph \<open>State formulas are compatible with closures.\<close>

lemma closure_location:
  "\<exists> l. \<forall> x \<in> \<Union> sim.closure a. fst x = l" if "P2 a"
proof (cases "\<Union> sim.closure a = {}")
  case True
  then show ?thesis
    by auto
next
  case False
  then obtain x b where "a \<inter> b \<noteq> {}" "P1 b" "b \<in> sim.closure a" "x \<in> a" "x \<in> b"
    unfolding sim.closure_def by auto
  from \<open>P1 b\<close> \<open>x \<in> b\<close> obtain l where "\<forall>x\<in>b. fst x = l"
    unfolding P1_def by auto
  with \<open>x \<in> a\<close> \<open>x \<in> b\<close> \<open>P2 a\<close> show ?thesis
    unfolding sim.closure_def
    unfolding P1_def P2_def
    by (inst_existentials l) (auto, metis fst_conv)
qed

lemma P2_closure:
  "x \<in> \<Union> sim.closure a" if "x \<in> a" "P2 a"
  using that unfolding P2_def
proof (clarify, goal_cases)
  case prems: (1 l)
  then have "snd x \<in> V"
    by (auto simp: R_of_def dest: V'_V)
  then have "snd x \<in> [snd x]\<^sub>l" "[snd x]\<^sub>l \<in> \<R> l"
    by (auto simp: V_def intro: region_cover')
  with prems have "x \<in> from_R l ([snd x]\<^sub>l)" "P1 (from_R l ([snd x]\<^sub>l))"
     apply -
    subgoal
      unfolding from_R_def by auto
    subgoal
      by (auto simp: from_R_fst P1_def)
    done
  with prems show ?case
    unfolding sim.closure_def by auto
qed

lemma \<phi>_closure_compatible: "\<phi> x \<longleftrightarrow> (\<forall> x \<in> \<Union> sim.closure a. \<phi> x)" if "x \<in> a" "P2 a"
  using closure_location[OF \<open>P2 a\<close>] P2_closure[OF that] unfolding \<phi>_def by (simp, fastforce)


paragraph \<open>Runs satisfying a formula all the way long\<close>

lemma P_a\<^sub>0_phi: "a\<^sub>0 \<subseteq> Collect \<phi>" if "P l\<^sub>0"
  using that unfolding a\<^sub>0_def \<phi>_def by (auto simp: from_R_def)

lemma P2_\<phi>:
  "a \<inter> Collect \<phi> = a" if "P2 a" "a \<inter> Collect \<phi> \<noteq> {}"
  using that \<phi>_closure_compatible by auto

lemma sim_Steps_P2:
  "P2 a" if "sim.Steps.reaches a\<^sub>0 a"
  using that sim_complete.P2_a\<^sub>0 by cases auto

lemma \<phi>_A1_compatible:
  "b \<subseteq> Collect \<phi> \<or> b \<inter> Collect \<phi> = {}" if "A1 a b"
  using that unfolding A1_def \<phi>_def by auto (metis fst_conv)

interpretation Double_Simulation_Finite_Complete_Abstraction_Prop C A1 P1 A2 P2 a\<^sub>0 \<phi>
  apply standard
  subgoal for x y S
    by (rule sim_complete.complete)
  subgoal
    by (rule sim_complete.finite_abstract_reachable)
  subgoal
    by (rule sim_complete.P2_invariant)
  subgoal
    by (rule sim_complete.P2_a\<^sub>0)
  subgoal for a b
    by (rule \<phi>_A1_compatible)
  subgoal for a
    by (frule P2_\<phi>, auto)
  subgoal for a
    by (metis P2_\<phi> sim_Steps_P2)
  subgoal for a
    unfolding P2_def R_of_def by auto
  done

interpretation G\<^sub>\<phi>: Graph_Start_Defs
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> P l'" "(l\<^sub>0, Z\<^sub>0)" .

interpretation \<phi>_bisim: Bisimulation_Invariants
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> P l'" A2_\<phi>
  "\<lambda> (l, Z) b. b = from_R l Z"
  "\<lambda> (l, Z). Z \<in> V'" "\<lambda> (l, Z). Z \<in> V' \<and> Z \<noteq> {}"
  "\<lambda> lZ. R_of lZ \<in> V'" P2
  apply standard
     apply simp_all
  subgoal for a b a'
    unfolding A2_\<phi>_def
    apply safe
    subgoal premises prems for x y xa ya aa xb
    proof -
      have "from_R xa ya \<inter> Collect \<phi> = from_R xa ya"
        unfolding \<phi>_def from_R_def using \<open>P xa\<close> by auto
      with prems A_B_step[of a b a'] show ?thesis
        by auto
    qed
    done
  subgoal for a a' b'
    unfolding A2_\<phi>_def by (clarify, drule B_A_step, auto 4 3 simp: \<phi>_def from_R_def)
   apply (force intro: step_z_beta'_V')
  unfolding A2_\<phi>_def by (clarify, drule A2_P2, frule P2_\<phi>, auto dest: P2_V')

(* Obsolete *)
lemma \<phi>_steps_empty_start:
  "xs = []" if "G\<^sub>\<phi>.steps ((l, Z) # xs)" "Z = {}"
  using that by cases (auto dest: step_z_beta'_empty)

(* Obsolete *)
lemma phi_Steps_empty_start:
  "xs = []" if "phi.Steps (from_R l Z # xs)" "Z = {}"
  using that by (cases, unfold A2_\<phi>_def, auto dest: step_z_beta'_empty simp: A2_def)

lemma sim_phi_steps_equiv:
  "G\<^sub>\<phi>.steps((l, Z) # xs) \<longleftrightarrow> phi.Steps (map (\<lambda> (l, Z). from_R l Z) ((l, Z) # xs))"
  if "Z \<in> V'"
  using that \<phi>_bisim.steps_map_equiv[of "\<lambda> (l, Z). from_R l Z", OF _ inj, of "(l, Z)" "from_R l Z"]
  by auto

(* XXX Unused *)
lemma from_R_\<phi>:
  "S = from_R l Z \<and> P l" if "S \<inter> Collect \<phi> = from_R l Z" "from_R l Z \<noteq> {}" "\<forall>x \<in> S. fst x = l''"
proof (safe, goal_cases)
  case (1 a b)
  from that have S_l: "\<forall>x \<in> S. fst x = l"
    by (metis IntE all_not_in_conv from_R_fst)
  from that(1) have *: "S \<inter> Collect \<phi> = {(l, u) | u. u \<in> R_of (S \<inter> Collect \<phi>)}"
    unfolding from_R_def R_of_def by force
  moreover have "R_of (S \<inter> Collect \<phi>) = R_of S"
    unfolding R_of_def \<phi>_def
    by auto (metis IntI Int_emptyI \<phi>_def comp_apply image_iff mem_Collect_eq snd_conv that(1,2) S_l)
  ultimately have "{(l, u) | u. u \<in> R_of S} = from_R l Z"
    using that(1) by metis
  then have "from_R l Z = S"
    apply (simp only: from_R_def R_of_def)
    using that(1) apply auto
    subgoal
      using S_l unfolding \<phi>_def by auto
    subgoal
      using \<open>R_of (S \<inter> Collect \<phi>) = R_of S\<close> by auto
    done
  with \<open>_ \<in> _\<close> show ?case
    by auto
next
  case (2 a b)
  with that(1) show ?case by auto
next
  case 3
  with that show ?case
    by (force simp: from_R_def \<phi>_def)
qed

interpretation Double_Simulation_Finite_Complete_Abstraction_Prop_Bisim C A1 P1 A2 P2 a\<^sub>0 \<phi> ..

lemma P2_from_R_list':
  "\<exists> as'. map (\<lambda>(x, y). from_R x y) as' = as" if "list_all P2 as"
  by (rule list_all_map[OF _ that]) (auto dest!: P2_from_R)

theorem Alw_ev_mc:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) x\<^sub>0) \<longleftrightarrow>
    \<not> P l\<^sub>0 \<or> (\<nexists>as a bs. G\<^sub>\<phi>.steps ((l\<^sub>0, Z\<^sub>0) # as @ a # bs @ [a]))"
proof (subst sim_phi_steps_equiv[OF start_state(2)], cases "P l\<^sub>0", goal_cases)
  case 1
  then show ?case
    apply (subst Alw_ev_mc[OF P_a\<^sub>0_phi])
     apply (auto simp del: map_map simp add: a\<^sub>0_def)
    apply (frule phi.P2_invariant.invariant_steps[unfolded a\<^sub>0_def])
    by (auto dest!: P2_from_R P2_from_R_list')
next
  case 2
  then have "\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) x\<^sub>0"
    unfolding sim.Alw_ev_def using from_R_fst by (force simp add: holds_Stream \<phi>_def a\<^sub>0_def)
  with \<open>\<not> P l\<^sub>0\<close> show ?case
    by auto
qed

theorem Alw_ev_mc1:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.Alw_ev (Not \<circ> \<phi>) x\<^sub>0) \<longleftrightarrow> \<not> (P l\<^sub>0 \<and> (\<exists>a. G\<^sub>\<phi>.reachable a \<and> G\<^sub>\<phi>.reaches1 a a))"
  unfolding Alw_ev_mc using G\<^sub>\<phi>.reachable_cycle_iff by auto

end (* Context for State Formula *)

lemma sim_reaches_equiv:
  "reaches (l, Z) (l', Z') \<longleftrightarrow> sim.Steps.reaches (from_R l Z) (from_R l' Z')" if "P2 (from_R l Z)"
  apply (subst Post_Bisim.reaches_equiv[of "\<lambda> (l, Z). from_R l Z", OF _ inj, of "(l, Z)"])
  using that apply safe
  subgoal
    using PB_QB by force
  subgoal
    by (simp add: P2_def)
  done

lemma Alw_ev_compatible:
  fixes \<phi> :: "'s \<times> ('c \<Rightarrow> real) \<Rightarrow> bool" -- "The property we want to check"
  assumes \<phi>_closure_compatible: "\<And> x y a. \<phi> x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> \<phi> y"
  assumes that: "u \<in> R" "u' \<in> R" "R \<in> \<R> l" "l \<in> state_set A"
  shows "sim.Alw_ev \<phi> (l, u) \<longleftrightarrow> sim.Alw_ev \<phi> (l, u')"
  apply (rule sim_complete_bisim.bisim.Alw_ev_compatible[of _ _ "from_R l R"])
     apply (rule \<phi>_closure_compatible; assumption; fail)
    apply (intro from_R_I that; fail)+
  apply (subst P1_def; inst_existentials l; auto simp add: that intro!: from_R_fst)
  done

lemma reaches_all:
  assumes
    "\<And> u u' R l. u \<in> R \<Longrightarrow> u' \<in> R \<Longrightarrow> R \<in> \<R> l \<Longrightarrow> l \<in> state_set A \<Longrightarrow> P l u \<longleftrightarrow> P l u'"
  shows
    "(\<forall> u. (\<exists> x\<^sub>0\<in>\<Union>sim.closure a\<^sub>0. sim.reaches x\<^sub>0 (l, u)) \<longrightarrow> P l u) \<longleftrightarrow>
     (\<forall> Z u. reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<and> u \<in> Z \<longrightarrow> P l u)"
proof -
  let ?P = "\<lambda> (l, u). P l u"
  have *: "\<And>a x y. x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> ?P x = ?P y"
    unfolding P1_def by clarsimp (subst assms[rotated 2], force+, metis fst_conv)+
  let ?P = "\<lambda> (l', u). l' = l \<longrightarrow> P l u"
  have *: "x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> ?P x = ?P y" for a x y
    by (frule *[of x a y], assumption+) (auto dest: P1_fst)
  have
    "(\<forall>b. (\<exists>y\<in>sim.closure a\<^sub>0. \<exists>x\<^sub>0\<in>y. sim.reaches x\<^sub>0 (l, b)) \<longrightarrow> P l b) \<longleftrightarrow>
     (\<forall>b ba. sim.Steps.reaches a\<^sub>0 b \<and> (l, ba) \<in> b \<longrightarrow> P l ba)"
    unfolding sim.reaches_steps_iff sim.Steps.reaches_steps_iff
    apply safe
    subgoal for b b' xs
      apply (rule sim_complete_bisim.reaches_all_1[of ?P xs "(l, b')", simplified])
          apply (rule *; force; fail)
      by auto
    subgoal premises prems for b y a b' xs
      apply (rule
          sim_complete_bisim.reaches_all_2[of ?P xs y, unfolded \<open>last xs = (l, b)\<close>, simplified]
          )
          apply (rule *; force; fail)
      using prems by auto
    done
  then show ?thesis
    unfolding sim_reaches_equiv[OF sim_complete.P2_a\<^sub>0[unfolded a\<^sub>0_def]]
    apply (simp add: a\<^sub>0_def[symmetric])
    subgoal premises prems
      apply safe
      subgoal for Z u
        unfolding from_R_def by auto
      subgoal for a u
        by (frule sim_Steps_P2) (auto dest: P2_from_R')
      done
    done
qed


subsection \<open>Leads-To Properties\<close>

context
  fixes P Q :: "'s \<Rightarrow> bool" -- "The state property we want to check"
  assumes sim_closure: "\<Union>sim.closure a\<^sub>0 = a\<^sub>0"
  assumes Q_closure_compatible: "\<phi> Q x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> \<phi> Q y"
begin

definition "\<psi> = Q o fst"

lemma \<psi>_closure_compatible:
  "\<psi> x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> \<psi> y"
  using Q_closure_compatible unfolding \<phi>_def \<psi>_def by auto

lemma \<psi>_closure_compatible':
  "(Not o \<psi>) x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> P1 a \<Longrightarrow> (Not o \<psi>) y"
  by (auto dest: \<psi>_closure_compatible)

lemma \<psi>_Alw_ev_compatible:
  assumes "u \<in> R" "u' \<in> R" "R \<in> \<R> l" "l \<in> state_set A"
  shows "sim.Alw_ev (Not \<circ> \<psi>) (l, u) = sim.Alw_ev (Not \<circ> \<psi>) (l, u')"
  by (assumption | rule Alw_ev_compatible \<psi>_closure_compatible' assms)+

interpretation G\<^sub>\<psi>: Graph_Defs
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> Q l'" .

theorem leadsto_mc1:
  "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.leadsto (\<phi> P) (Not \<circ> \<psi>) x\<^sub>0) \<longleftrightarrow>
   (\<nexists>x. reaches (l\<^sub>0, Z\<^sub>0) x \<and> P (fst x) \<and> Q (fst x) \<and> (\<exists>a. G\<^sub>\<psi>.reaches x a \<and> G\<^sub>\<psi>.reaches1 a a))"
  if "\<forall>x\<^sub>0\<in>a\<^sub>0. \<not> sim.deadlock x\<^sub>0"
proof -
  have *: "l \<in> state_set A" "Z \<in> V'" "Z \<noteq> {}" if "reaches (l\<^sub>0, Z\<^sub>0) (l, Z)" for l Z
    subgoal
      using that by cases (auto intro: start_state step_z_beta'_state_set)
    subgoal
      using that
      by (induction "(l\<^sub>0, Z\<^sub>0)" "(l, Z)" arbitrary: l Z rule: rtranclp.induct;
          auto intro: step_z_beta'_V' start_state)
    subgoal
      using that start_state by cases auto
    done

  have Alw_ev_mc1:
    "(\<forall>x\<^sub>0\<in>from_R l Z. sim.Alw_ev (Not \<circ> \<psi>) x\<^sub>0) \<longleftrightarrow>
      \<not> (Q l \<and> (\<exists>a. G\<^sub>\<psi>.reaches (l, Z) a \<and> G\<^sub>\<psi>.reaches1 a a))"
    if "reaches (l\<^sub>0, Z\<^sub>0) (l, Z)" for l Z
  proof -
    interpret Start: Regions_TA_Start_State v n not_in_X X k A l Z
      by standard (rule * that)+
    show ?thesis
      using Start.Alw_ev_mc1[unfolded Start.a\<^sub>0_def Start.\<phi>_def, of Q]
      unfolding \<psi>_def Graph_Start_Defs.reachable_def .
  qed

  have "(\<forall>x\<^sub>0\<in>a\<^sub>0. sim.leadsto (\<phi> P) (Not \<circ> \<psi>) x\<^sub>0)
    \<longleftrightarrow> (\<forall>x\<^sub>0\<in>a\<^sub>0. \<nexists>y. sim.reaches x\<^sub>0 y \<and> \<phi> P y \<and> \<not> sim.Alw_ev (Not \<circ> \<psi>) y)"
    using that by (simp add: sim.Ex_ev sim.leadsto_iff)
  also have
    "\<dots> \<longleftrightarrow> (\<forall> l u. (\<exists> x\<^sub>0\<in>a\<^sub>0. sim.reaches x\<^sub>0 (l, u)) \<longrightarrow> \<not> (P l \<and> \<not> sim.Alw_ev (Not \<circ> \<psi>) (l, u)))"
    unfolding \<phi>_def by auto
  also have
    "\<dots> \<longleftrightarrow> (\<forall> l Z. reaches (l\<^sub>0, Z\<^sub>0) (l, Z) \<longrightarrow> (\<forall> u \<in> Z. \<not> (P l \<and> \<not> sim.Alw_ev (Not \<circ> \<psi>) (l, u))))"
    by (subst sim_closure[symmetric], subst reaches_all)
       (auto simp: \<phi>_def \<psi>_def comp_def dest: \<psi>_Alw_ev_compatible)
  also have
    "\<dots> \<longleftrightarrow> (\<nexists> x. reaches (l\<^sub>0, Z\<^sub>0) x \<and> P (fst x) \<and>
              (case x of (l, Z) \<Rightarrow> \<not> (\<forall> y \<in> from_R l Z. sim.Alw_ev (Not \<circ> \<psi>) y)))"
    unfolding from_R_def \<phi>_def by auto
  also have
    "\<dots> \<longleftrightarrow> (\<nexists>x. reaches (l\<^sub>0, Z\<^sub>0) x \<and> P (fst x) \<and> Q (fst x) \<and> (\<exists>a. G\<^sub>\<psi>.reaches x a \<and> G\<^sub>\<psi>.reaches1 a a))"
    by (auto simp: Alw_ev_mc1)
  finally show ?thesis .
qed

end (* Context for State Formulae *)


subsection \<open>Connection with implementation semantics\<close>

definition (in Regions) step_z_norm'' ("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<N>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)
where
  "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l'', D''\<rangle> \<equiv>
  \<exists> l' D'. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle> \<and> A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^bsub>\<N>(\<upharpoonleft>a)\<^esub> \<langle>l'', D''\<rangle>"

sublocale DBM: Graph_Start_Defs
  "\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {}" "(l\<^sub>0, D\<^sub>0)" .

context
  assumes global_clock_numbering: "global_clock_numbering A v n"
  notes [intro] = step_z_valid_dbm'[OF global_clock_numbering valid_abstraction]
begin

lemma norm_beta_sound'':
  assumes "A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l'', D''\<rangle>"
      and "valid_dbm D"
    shows "A \<turnstile>' \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l'', [D'']\<^bsub>v,n\<^esub>\<rangle>"
proof -
  from assms(1) obtain l' D' where
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>" "A \<turnstile> \<langle>l', D'\<rangle> \<leadsto>\<^bsub>\<N>(\<upharpoonleft>a)\<^esub> \<langle>l'', D''\<rangle>"
    by (auto simp: step_z_norm''_def)
  moreover with \<open>valid_dbm D\<close> have "valid_dbm D'"
    by auto
  ultimately have "A \<turnstile> \<langle>l', [D']\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>\<upharpoonleft>a\<^esub> \<langle>l'', [D'']\<^bsub>v,n\<^esub>\<rangle>"
    by - (rule norm_beta_sound'[OF global_clock_numbering valid_abstraction])
  with step_z_dbm_sound[OF \<open>A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>\<close> global_clock_numbering] show ?thesis ..
qed

lemma norm_beta_complete:
  assumes "A \<turnstile>' \<langle>l,[D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l'',Z''\<rangle>"
  and     "valid_dbm D"
  obtains D'' where "A \<turnstile>' \<langle>l,D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l'',D''\<rangle>" "[D'']\<^bsub>v,n\<^esub> = Z''" "valid_dbm D''"
proof -
  from assms(1) obtain l' Z' where steps:
    "A \<turnstile> \<langle>l, [D]\<^bsub>v,n\<^esub>\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>" "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<beta>(\<upharpoonleft>a)\<^esub> \<langle>l'', Z''\<rangle>"
    by (auto elim!: step_z_beta'.cases)
  from step_z_dbm_DBM[OF this(1) global_clock_numbering] obtain D' where D':
    "A \<turnstile> \<langle>l, D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l', D'\<rangle>" "Z' = [D']\<^bsub>v,n\<^esub>"
    by auto
  with \<open>valid_dbm D\<close> have "valid_dbm D'"
    by auto
  from steps D' show ?thesis
    by (auto
        intro!: that[unfolded step_z_norm''_def]
        elim!: norm_beta_complete'[OF global_clock_numbering valid_abstraction _ \<open>valid_dbm D'\<close>]
        )
qed

lemma bisim:
  "Bisimulation_Invariant
  (\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {})
  (\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {})
  (\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>)
  (\<lambda> _. True) (\<lambda> (l, D). valid_dbm D)"
proof (standard, goal_cases)
  -- \<open>\<beta> \<Rightarrow> \<N>\<close>
  case (1 a b a')
  then show ?case
    by (blast elim: norm_beta_complete)
next
  -- \<open>\<N> \<Rightarrow> \<beta>\<close>
  case (2 a a' b')
  then show ?case
    by (blast intro: norm_beta_sound'')
next
  -- \<open>\<beta> invariant\<close>
  case (3 a b)
  then show ?case
    by simp
next
  -- \<open>\<N> invariant\<close>
  case (4 a b)
  then show ?case
    unfolding step_z_norm''_def
    by (auto intro: step_z_norm_valid_dbm'[OF global_clock_numbering valid_abstraction])
qed

interpretation Bisimulation_Invariant
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}"
  "\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {}"
  "\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>"
  "\<lambda> _. True" "\<lambda> (l, D). valid_dbm D"
  by (rule bisim)

context
  fixes P Q :: "'s \<Rightarrow> bool" -- "The state property we want to check"
begin

interpretation bisim_\<psi>: Bisimulation_Invariant
  "\<lambda> (l, Z) (l', Z'). \<exists> a. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {} \<and> Q l'"
  "\<lambda> (l, D) (l', D'). \<exists> a. A \<turnstile>' \<langle>l, D\<rangle> \<leadsto>\<^bsub>\<N>(a)\<^esub> \<langle>l', D'\<rangle> \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {} \<and> Q l'"
  "\<lambda> (l, Z) (l', D). l = l' \<and> Z = [D]\<^bsub>v,n\<^esub>"
  "\<lambda> _. True" "\<lambda> (l, D). valid_dbm D"
  by (rule Bisimulation_Invariant_filter[OF bisim, of "\<lambda> (l, _). Q l" "\<lambda> (l, _). Q l"]) auto

end (* Context for State Formulae *)

end (* Context for Global Clock Numbering *)

end (* Regions TA with Start State *)

context Reachability_Problem_Defs
begin

abbreviation step_impl' ("\<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  "\<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'', Z'''\<rangle> \<equiv> \<exists> l' Z' Z''.
    A \<turnstile>\<^sub>I \<langle>l, Z\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', Z'\<rangle>
    \<and> A \<turnstile>\<^sub>I \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>
    \<and> FW' (norm_upd Z'' (k' l'') n) n = Z'''"

sublocale Graph_Defs "\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" .

end (* Reachability Problem Defs *)


subsubsection \<open>Misc\<close>

lemma finite_conv_A:
  "finite (trans_of (conv_A A))" if "finite (trans_of A)"
  using that unfolding trans_of_def by (cases A) auto

(* XXX Move *)
lemma real_of_int_inj:
  "inj real_of_int"
  by standard auto

(* XXX Move *)
lemma map_DBMEntry_real_of_int_inj:
  "a = b" if "map_DBMEntry real_of_int a = map_DBMEntry real_of_int b"
proof -
  have "inj (map_DBMEntry real_of_int)"
    by (intro DBMEntry.inj_map real_of_int_inj)
  with that show ?thesis
    by - (erule injD)
qed

(* XXX Move *)
lemma (in -) n_eq_conv_MI:
  "curry D =\<^sub>n (curry D')" if "curry (conv_M D) =\<^sub>n curry (conv_M D')"
  using that unfolding n_eq_def by (auto intro: map_DBMEntry_real_of_int_inj)

(* XXX Move? *)
lemma (in Reachability_Problem) check_diag_conv_M_iff:
  "check_diag n D \<longleftrightarrow> check_diag n (conv_M D)"
  using check_diag_conv_M check_diag_conv_M_rev by fast

(* XXX Move *)
lemma (in Regions) \<R>_regions_distinct:
  "R = R'" if "u \<in> R" "u \<in> R'" "R \<in> \<R> l" "R' \<in> \<R> l"
  using that unfolding \<R>_def by clarsimp (rule valid_regions_distinct; auto)

(* XXX Move *)
lemma step_impl_delay_loc_eq:
  "l' = l" if "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l', D'\<rangle>"
  using that by cases auto



context Reachability_Problem
begin

sublocale TA: Regions_TA v n "Suc n" "{1..<Suc n}" k "conv_A A"
  by (standard; intro valid_abstraction' finite_conv_A finite_trans_of_finite_state_set finite_trans)


subsubsection \<open>@{term init_dbm}\<close>

(* XXX Move *)
lemma init_dbm_semantics:
  "u \<in> [(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub> \<longleftrightarrow> (\<forall>c\<in>{1..n}. u c = 0)"
  by (safe elim!: init_dbm_semantics' init_dbm_semantics'')

lemma init_dbm_non_empty:
  "[(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub> \<noteq> {}"
proof -
  let ?u = "\<lambda> c. 0 :: real"
  have "?u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>"
    by (rule init_dbm_semantics'', auto)
  then show ?thesis by auto
qed

(* XXX Move *)
lemma cla_init_dbm_id:
  "cla l\<^sub>0 ([curry init_dbm]\<^bsub>v,n\<^esub>) = ([curry init_dbm]\<^bsub>v,n\<^esub>)"
proof -
  let ?u = "\<lambda> c. 0 :: real"
  let ?I = "\<lambda> _. Const 0"
  let ?R = "region X ?I {}"
  have "valid_region X (k l\<^sub>0) ?I {}"
    by standard auto
  then have "?R \<in> \<R> l\<^sub>0"
    unfolding \<R>_def X_alt_def by blast
  have region: "u \<in> ?R" if "u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>" for u
    using that unfolding init_dbm_semantics X_def by - (standard; fastforce)
  have iff: "u \<in> ?R \<longleftrightarrow> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>" for u
    apply standard
    subgoal
      unfolding init_dbm_semantics X_def[symmetric]
      by (auto elim: Regions.intv_elem.cases elim!: Regions.region.cases)
    by (rule region)
  have single: "R = ?R" if "u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>" "u \<in> R" "R \<in> \<R> l\<^sub>0" for u R
    using that \<open>?R \<in> \<R> l\<^sub>0\<close> by - (rule \<R>_regions_distinct; auto intro: region)
  show ?thesis
    using \<open>?R \<in> _\<close>
    unfolding cla_def
    apply safe
     apply (drule single, assumption+)
     apply (subst (asm) iff[symmetric], simp; fail)
    apply (frule region)
    by auto
qed


subsubsection \<open>@{term dbm_default}\<close>

lemma dbm_default_n_eq_eqI:
  assumes "dbm_default (curry D) n" "dbm_default (curry D') n" "curry D' =\<^sub>n curry D"
  shows "D' = D"
  using assms
    apply (intro ext)
      apply safe
      subgoal for a b
        by (cases "a \<le> n"; cases "b \<le> n"; simp add: n_eq_def)
      done

(* XXX Move *)
lemma E_op''_dbm_default':
  "dbm_default (curry (E_op'' l r g l' M)) n"
  if "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l'" "dbm_default (curry M) n"
proof -
  note default_intros =
    filter_diag_default up_canonical_upd_default reset'_upd_default abstr_repair_default
  (* XXX Duplication *)
  have "\<forall>c\<in>constraint_clk ` set (inv_of A l). c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l] unfolding collect_clks_def by blast
  moreover have
    "\<forall>c\<in>constraint_clk ` set (inv_of A l'). c \<le> n"
    using clock_range collect_clks_inv_clk_set[of A l'] unfolding collect_clks_def by blast
  moreover have "\<forall>c\<in>constraint_clk ` set g. c \<le> n"
    using clock_range collect_clocks_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover have "\<forall>i\<in>set r. i \<le> n"
    using clock_range reset_clk_set[OF that(1)] unfolding collect_clks_def by blast
  moreover note side_conds = calculation that(2)
  let ?M = "
    filter_diag (\<lambda>M. abstr_repair (inv_of A l') (reset'_upd M n r 0))
      (filter_diag (abstr_repair g) (abstr_repair (inv_of A l) (up_canonical_upd M n)))"
  have "dbm_default (curry ?M) n"
    by (intro default_intros[unfolded collect_clks_def] side_conds)
  then have "dbm_default (curry (filter_diag (\<lambda>M. FW' (norm_upd M (k' l') n) n) ?M)) n"
    by - (rule default_intros, intro FW'_default norm_upd_default)
  then show ?thesis
    unfolding E_op''_def by (auto simp: Let_def filter_diag_def)
qed

(* XXX Move *)
lemma E_op''_dbm_default:
  assumes
    "E_op''.E_from_op (l, D) (l', D')"
    "dbm_default (curry D) n"
  shows
    "dbm_default (curry D') n"
  using assms E_op''_dbm_default' unfolding E_op''.E_from_op_def by auto


subsubsection \<open>@{term check_diag}\<close>

(* XXX Move? *)
lemma canonical_empty_check_diag':
  assumes "wf_dbm D" "[curry (conv_M D)]\<^bsub>v,n\<^esub> = {}"
  shows "check_diag n D"
  apply (rule canonical_empty_check_diag[OF _ assms(2)])
  using wf_dbm_D(1)[OF assms(1)] unfolding check_diag_def neutral by auto

subsubsection \<open>Stronger invariant on DBMs\<close>

definition
  "dbm_inv D \<equiv>
    canonical' (conv_M D) \<and> \<not> check_diag n D \<and> (\<forall>i\<le>n. conv_M D (i, i) \<le> 0)
    \<and> valid_dbm (curry (conv_M D))
    \<and> dbm_default (curry D) n"

lemma dbm_inv_equvi_eqI:
  assumes "dbm_inv D" "dbm_inv D'" "[curry (conv_M D')]\<^bsub>v,n\<^esub> = [curry (conv_M D)]\<^bsub>v,n\<^esub>"
  shows "D = D'"
proof -
  from assms have "wf_dbm D" "\<not> check_diag n D"
    unfolding dbm_inv_def wf_dbm_def by auto
  then have *: "[curry (conv_M D)]\<^bsub>v,n\<^esub> \<noteq> {}"
    by (auto dest!: canonical_empty_check_diag')
  from assms have
    "curry (conv_M D) =\<^sub>n curry (conv_M D')"
    apply -
    apply (rule canonical_eq_upto[OF clock_numbering(1) surj_numbering _ _ * assms(3)[symmetric]])
    unfolding dbm_inv_def
       apply (simp; fail)+
    subgoal
      unfolding check_diag_conv_M_iff
      unfolding check_diag_def neutral[symmetric] by fastforce
    subgoal
      unfolding check_diag_conv_M_iff
      unfolding check_diag_def neutral[symmetric] by fastforce
    done
  then have "curry D =\<^sub>n curry D'"
    by (rule n_eq_conv_MI)
  moreover from assms have "dbm_default (curry D) n" "dbm_default (curry D') n"
    unfolding dbm_inv_def by simp+
  ultimately show ?thesis
    by - (rule dbm_default_n_eq_eqI)
qed

lemma dbm_invI:
  "dbm_inv D" if "wf_dbm D" "\<not> check_diag n D" "dbm_default (curry D) n"
  using that unfolding dbm_inv_def wf_dbm_def by auto

lemma init_dbm_dbm_inv[intro, simp]:
  "dbm_inv init_dbm"
proof -
  have "\<not> check_diag n init_dbm"
    unfolding init_dbm_def check_diag_def by auto
  moreover have "dbm_default (curry init_dbm) n"
    unfolding init_dbm_def neutral by auto
  ultimately show ?thesis
    using wf_dbm_init_dbm by - (rule dbm_invI)
qed


subsection \<open>Bridging the semantic gap\<close>

lemma step_impl'_E:
  "(\<lambda> (l, D) (l', D'). \<exists> a. \<langle>l, D\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', D'\<rangle>) = E"
  unfolding E_def by (intro ext) auto

lemma step_z_norm''_step_impl'_equiv:
  "Bisimulation_Invariant
     (\<lambda> (l, D) (l', D'). \<exists> a. step_z_norm'' (conv_A A) l D a l' D')
     (\<lambda>(l, D) (l', D'). \<exists>a. \<langle>l, D\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', D'\<rangle>)
     (\<lambda>(l, M) (l', D). l = l' \<and> [curry (conv_M D)]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y)
     wf_state"
proof (standard, goal_cases)
  case prems: (1 a b a')
  obtain l M l' M' l1 D where unfolds[simp]: "a = (l, M)" "b = (l', M')" "a' = (l1, D)"
    by force+
  from prems have [simp]: "l1 = l"
    by auto
  from prems obtain a1 where
    "step_z_norm'' (conv_A A) l M a1 l' M'"
    by auto
  then obtain l2 M1 where steps:
    "conv_A A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l2, M1\<rangle>"
    "step_z_norm' (conv_A A) l2 M1 \<upharpoonleft>a1 l' M'"
    unfolding step_z_norm''_def by auto
  from step_z_dbm_equiv'[OF steps(1), of "curry (conv_M D)"] prems(2-) obtain M2 where
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l2, M2\<rangle>" "wf_dbm D" "[M1]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
    by (auto simp: wf_state_def)
  with step_impl_complete''_improved[OF this(1)] obtain D2 where D2:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l2, D2\<rangle>" "[curry (conv_M D2)]\<^bsub>v,n\<^esub> = [M1]\<^bsub>v,n\<^esub>"
    by auto
  from step_impl_wf_dbm[OF D2(1) \<open>wf_dbm D\<close>] have "wf_dbm D2" .
  then have *:
    "canonical' (conv_M D2) \<or> check_diag n D2"
    "\<forall>i\<le>n. conv_M D2 (i, i) \<le> 0"
    "valid_dbm (curry (conv_M D2))"
    using wf_dbm_D by blast+
  have "valid_dbm M1"
    using prems steps(1) by - (rule step_z_valid_dbm', auto)
  from step_z_norm_equiv'[OF steps(2), OF this *(3) sym[OF D2(2)]] guess D3 by (elim conjE exE)
  note D3 = this
  from step_impl_norm_complete''[OF D3(1) *(3,1,2)] obtain D4 where D4:
    "A \<turnstile>\<^sub>I \<langle>l2, D2\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a1\<^esub> \<langle>l', D4\<rangle>"
    "[curry (conv_M (FW' (norm_upd D4 (k' l') n) n))]\<^bsub>v,n\<^esub> = [D3]\<^bsub>v,n\<^esub>"
    by auto
  with D2(1) have "\<langle>l, D\<rangle> \<leadsto>\<^bsub>a1\<^esub> \<langle>l', FW' (norm_upd D4 (k' l') n) n\<rangle>"
    by auto
  with D4(2) D3(2) show ?case
    by force
next
  case prems: (2 a a' b')
  obtain l M l' D' l1 D where unfolds[simp]: "a = (l, M)" "b' = (l', D')" "a' = (l1, D)"
    by force+
  from prems have [simp]: "l1 = l"
    by auto
  from prems obtain a1 where "\<langle>l, D\<rangle> \<leadsto>\<^bsub>a1\<^esub> \<langle>l', D'\<rangle>"
    by auto
  then obtain D1 D2 where steps:
    "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l, D1\<rangle>" "A \<turnstile>\<^sub>I \<langle>l, D1\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a1\<^esub> \<langle>l', D2\<rangle>"
    "D' = FW' (norm_upd D2 (k' l') n) n"
    by (auto dest: step_impl_delay_loc_eq)
  from prems have "wf_dbm D"
    by (auto simp: wf_state_def)
  with steps have "wf_dbm D1"
    by (blast intro: step_impl_wf_dbm)
  from \<open>wf_dbm D\<close> have
    "canonical' (conv_M D) \<or> check_diag n D"
    "\<forall>i\<le>n. conv_M D (i, i) \<le> 0"
    "valid_dbm (curry (conv_M D))"
    using wf_dbm_D by blast+
  from step_impl_sound'[OF steps(1) this] obtain M2 where M2:
    "conv_A A \<turnstile> \<langle>l, curry (conv_M D)\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l, M2\<rangle>"
    "[curry (conv_M D1)]\<^bsub>v,n\<^esub> = [M2]\<^bsub>v,n\<^esub>"
    by auto
  from step_impl_sound_wf[OF steps(2) \<open>wf_dbm D1\<close>] obtain M3 where M3:
    "step_z_norm' (conv_A A) l (curry (conv_M D1)) \<upharpoonleft>a1 l' M3"
    "[curry (conv_M (FW' (norm_upd D2 (k' l') n) n))]\<^bsub>v,n\<^esub> = [M3]\<^bsub>v,n\<^esub>"
    by auto
  from step_z_dbm_equiv'[OF M2(1), of M] prems(2) obtain M2' where M2':
    "conv_A A \<turnstile> \<langle>l, M\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l, M2'\<rangle>" "[M2]\<^bsub>v,n\<^esub> = [M2']\<^bsub>v,n\<^esub>"
    by auto
  have "valid_dbm (curry (conv_M D1))" "valid_dbm M2'"
    subgoal
      using \<open>wf_dbm D1\<close> wf_dbm_D(3) by auto
    subgoal
      using prems M2'(1) by - (rule step_z_valid_dbm', auto)
    done
  from step_z_norm_equiv'[OF M3(1), of M2', OF this] M2(2) M2'(2) obtain M3' where
    "step_z_norm' (conv_A A) l M2' \<upharpoonleft>a1 l' M3'" "[M3]\<^bsub>v,n\<^esub> = [M3']\<^bsub>v,n\<^esub>"
    by auto
  with M2'(1) M3(2) steps(3) show ?case
    unfolding step_z_norm''_def by auto
next
  case (3 a b)
  then show ?case
    unfolding step_z_norm''_def using step_z_norm_valid_dbm'_spec step_z_valid_dbm' by auto
next
  case (4 a b)
  then show ?case
    by (clarsimp simp: norm_step_wf_dbm step_impl_wf_dbm wf_state_def)
qed

context
  assumes "l\<^sub>0 \<in> state_set A"
begin

lemma l\<^sub>0_state_set:
  "l\<^sub>0 \<in> state_set (conv_A A)"
  using \<open>l\<^sub>0 \<in> state_set A\<close> unfolding state_set_def trans_of_def by (cases A; force)

interpretation start:
  Regions_TA_Start_State v n "Suc n" "{1..<Suc n}" k "conv_A A"
  l\<^sub>0 "[(curry init_dbm :: real DBM)]\<^bsub>v,n\<^esub>"
  apply standard
  subgoal
    by (rule l\<^sub>0_state_set)
  subgoal
    using valid_dbm_V' by blast
  subgoal
    by (rule init_dbm_non_empty)
  done

lemma start_closure:
  "\<Union>TA.sim.closure start.a\<^sub>0 = start.a\<^sub>0"
  using l\<^sub>0_state_set cla_init_dbm_id
  unfolding start.a\<^sub>0_def TA.sim_closure_from_R
  unfolding cla_def from_R_def
  by simp blast

lemma norm_final_bisim:
  "Bisimulation_Invariant
     (\<lambda>(l, D) (l', D'). \<exists>a. step_z_norm'' (conv_A A) l D a l' D')
     E_op''.E_from_op
     (\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y) wf_state"
  by (rule
    Bisimulation_Invariant_sim_replace[OF
      Bisimulation_Invariant_composition[OF
        step_z_norm''_step_impl'_equiv[unfolded step_impl'_E] E_op''.E_from_op_bisim
      ]
    ])
    (auto simp add: state_equiv_def dbm_equiv_def)

lemma norm_final_bisim_empty:
  "Bisimulation_Invariant
     (\<lambda>(l, D) (l', D'). \<exists>a. step_z_norm'' (conv_A A) l D a l' D' \<and> [D']\<^bsub>v,n\<^esub> \<noteq> {})
     (\<lambda> a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))
     (\<lambda> (l, M) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = [M]\<^bsub>v,n\<^esub>)
     (\<lambda>(l, y). valid_dbm y) wf_state"
  by (rule
    Bisimulation_Invariant_filter[OF
      norm_final_bisim, of "\<lambda> (l, D). [D]\<^bsub>v,n\<^esub> \<noteq> {}" "\<lambda> a. \<not> check_diag n (snd a)"]
    )
    (auto
      intro!: canonical_empty_check_diag' simp: wf_state_def
      dest: check_diag_empty_spec[OF check_diag_conv_M]
    )

lemma beta_final_bisim_empty:
  "Bisimulation_Invariant
     (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {})
     (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))
     (\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z)
     (\<lambda>_. True) wf_state"
  by (rule
    Bisimulation_Invariant_sim_replace[OF
      Bisimulation_Invariant_composition[OF
        start.bisim[OF global_clock_numbering'] norm_final_bisim_empty
      ]
    ]
    )
    (auto dest!: wf_dbm_D(3) simp: wf_state_def)

lemma beta_final_bisim_empty_strong:
  "Bisimulation_Invariant
     (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {})
     (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))
     (\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z)
     (\<lambda>_. True) (\<lambda> (l, D). dbm_inv D)"
  apply (rule Bisimulation_Invariant_strengthen_post'[OF beta_final_bisim_empty])
  subgoal for a b
    unfolding dbm_inv_def wf_state_def wf_dbm_def by (fastforce dest!: E_op''_dbm_default)
  subgoal for a
    unfolding wf_state_def dbm_inv_def wf_dbm_def by auto
  done

interpretation bisim:
  Bisimulation_Invariant
    "\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {}"
    "\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b)"
    "\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z"
    "\<lambda>_. True" "\<lambda> (l, D). dbm_inv D"
  by (rule beta_final_bisim_empty_strong)

context
  fixes P Q :: "'s \<Rightarrow> bool" -- "The state property we want to check"
begin

lemma beta_final_bisim_empty_Q:
  "Bisimulation_Invariant
     (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l')
     (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))
     (\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z)
     (\<lambda>_. True) (\<lambda> (l, D). dbm_inv D)"
  by (rule
      Bisimulation_Invariant_filter[
        OF beta_final_bisim_empty_strong, of "\<lambda> (l, _). Q l" "\<lambda> (l, _). Q l"
      ]
    ) auto

interpretation bisim_Q:
  Bisimulation_Invariant
    "\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l'"
    "\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b)"
    "\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z"
    "\<lambda>_. True" "(\<lambda> (l, D). dbm_inv D)"
  by (rule beta_final_bisim_empty_Q)

interpretation bisims_Q:
  Bisimulation_Invariants
    "\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l'"
    "\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b)"
    "\<lambda>(l, Z) (l', D'). l' = l \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> = Z"
    "\<lambda>_. True" "\<lambda>_. True" "\<lambda> (l, D). dbm_inv D" "\<lambda> (l, D). dbm_inv D"
  by (intro Bisimulation_Invariant_Bisimulation_Invariants beta_final_bisim_empty_Q)

(* XXX Why do we need this? *)
lemma Q_compatible:
  "start.\<phi> Q x \<Longrightarrow> x \<in> a \<Longrightarrow> y \<in> a \<Longrightarrow> TA.P1 a \<Longrightarrow> start.\<phi> Q y" for x
  unfolding start.\<phi>_def by (auto dest: TA.P1_fst)

(* XXX Clean *)
lemma \<psi>_def:
  "start.\<psi> Q = Q \<circ> fst"
  by (rule start.\<psi>_def[OF start_closure Q_compatible])

lemma leadsto_sem_equiv:
  "(\<forall>x\<^sub>0\<in>start.a\<^sub>0. leadsto (start.\<phi> P) ((Not \<circ>\<circ> start.\<psi>) Q) x\<^sub>0)
  = (\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> leadsto (\<lambda> (l, u). P l) (\<lambda> (l, u). \<not> Q l) (l\<^sub>0, u\<^sub>0))
  "
proof -
  have unfold: "(\<lambda>(l, u). P l) = (\<lambda> x. P (fst x))" "(\<lambda>(l, u). \<not> Q l) = (\<lambda>x. \<not> Q (fst x))"
    by auto
  show ?thesis
    unfolding TA.C_def start.a\<^sub>0_def from_R_def init_dbm_semantics start.\<phi>_def \<psi>_def comp_def unfold
    by auto
qed

lemma leadsto_mc2:
  "(\<exists>x.
    TA.reaches (l\<^sub>0, [curry init_dbm]\<^bsub>v,n\<^esub>) x \<and>
    P (fst x) \<and>
    Q (fst x) \<and>
    (\<exists>a. (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l')\<^sup>*\<^sup>* x a \<and>
         (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l')\<^sup>+\<^sup>+ a a))
   \<longleftrightarrow>
   (\<exists>x.
    (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) x \<and>
    P (fst x) \<and>
    Q (fst x) \<and>
    (\<exists>a. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>*\<^sup>* x a \<and>
         (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>+\<^sup>+ a a))
  "
  apply safe
   apply (drule bisim.A_B.simulation_reaches[where b = "(l\<^sub>0, init_dbm)"], (simp; fail)+)
   apply clarify
   apply (drule bisim_Q.A_B.simulation_reaches)
      apply blast
     apply blast
    apply blast
   apply clarify
   apply (frule bisims_Q.A_B.reaches1_unique[rotated], blast+)
    apply (auto dest: dbm_inv_equvi_eqI; fail)
   apply force
  apply (drule bisim.B_A.simulation_reaches[where b = "(l\<^sub>0, [curry init_dbm]\<^bsub>v,n\<^esub>)"], (simp; fail)+)
  apply (drule bisim_Q.B_A.simulation_reaches)
     apply blast
    apply blast
   apply blast
  apply (drule bisims_Q.B_A.reaches1_unique[rotated]; force)
  done

context
  assumes no_deadlock: "\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0)"
begin

lemma no_deadlock':
  "\<forall>x\<^sub>0\<in>start.a\<^sub>0. \<not> TA.sim.deadlock x\<^sub>0"
  unfolding TA.C_def start.a\<^sub>0_def from_R_def using no_deadlock by (auto dest: init_dbm_semantics')

lemma leadsto_mc1:
  "(\<forall>u\<^sub>0. (\<forall>c \<in> {1..n}. u\<^sub>0 c = 0) \<longrightarrow> leadsto (\<lambda> (l, u). P l) (\<lambda> (l, u). \<not> Q l) (l\<^sub>0, u\<^sub>0)) =
   (\<nexists>x. TA.reaches (l\<^sub>0, [curry init_dbm]\<^bsub>v,n\<^esub>) x \<and>
       P (fst x) \<and>
       Q (fst x) \<and>
       (\<exists>a. (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l')\<^sup>*\<^sup>* x a \<and>
            (\<lambda>(l, Z) (l', Z'). \<exists>a. step_z_beta' (conv_A A) l Z a l' Z' \<and> Z' \<noteq> {} \<and> Q l')\<^sup>+\<^sup>+ a a))"
  unfolding leadsto_sem_equiv[symmetric]
  by (rule start.leadsto_mc1[OF start_closure Q_compatible no_deadlock', unfolded TA.C_def])

lemmas leadsto_mc = leadsto_mc1[unfolded leadsto_mc2]

end (* No deadlock *)

end (* State properties *)

end (* Start State *)

end (* Reachability Problem *)

context Reachability_Problem_precompiled
begin

lemma start_in_state_set:
  "0 \<in> state_set A"
  unfolding state_set_def A_def T_def using n_gt_0 start_has_trans by fastforce

thm leadsto_mc[OF start_in_state_set]

end (* Reachability Problem precompiled *)

end (* Theory *)