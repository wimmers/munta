theory TA_Simulation
  imports
    TA.Timed_Automata
    TA.Normalized_Zone_Semantics
    TA.Simulation_Graphs_TA
    "HOL-Eisbach.Eisbach"
    Simulation_Graphs2
    "HOL-ex.Sketch_and_Explore"
    TA_Impl.Normalized_Zone_Semantics_Impl_Semantic_Refinement
begin

no_notation dbm_le ("_ \<preceq> _" [51, 51] 50)

lemma
  step_z_state_setI1: "l \<in> state_set A" and
  step_z_state_setI2: "l' \<in> state_set A" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>"
  using that unfolding step_z'_def by (force simp: state_set_def trans_of_def)+

lemma step_trans_z'_sound:
  "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle> \<Longrightarrow> \<forall>u' \<in> Z'. \<exists>u \<in> Z. \<exists>d.  A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l',u'\<rangle>"
  by (fastforce dest!: step_trans_a_z_sound step_trans_t_z_sound elim!: step_trans_z'.cases)

lemma step_trans_z'_exact_strong:
  assumes "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>"
  shows "Z' = {u'. \<exists>u \<in> Z. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l', u'\<rangle>}"
  using step_trans_z'_sound assms by (auto dest: step_trans_z'_exact step_trans_z'_sound)

lemma step_a_step_trans_iff:
  "A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle> \<longleftrightarrow> (\<exists>g r. A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>(g,a,r)\<^esub> \<langle>l', u'\<rangle>)"
  unfolding step_a.simps step_trans.simps by fast

lemma step_trans'_step_trans_iff:
  "(\<exists>t. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l', u'\<rangle>) \<longleftrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
  unfolding step_trans'.simps step'.simps step_a_step_trans_iff by fast

locale Time_Abstract_Simulation =
  fixes A :: "('a, 'c, 't :: time, 'l) ta"
  fixes sim :: "'l \<times> ('c \<Rightarrow> 't :: time) \<Rightarrow> 'l \<times> ('c \<Rightarrow> 't) \<Rightarrow> bool" (infix "\<preceq>" 60)
  assumes sim:
  "\<And>l l' l\<^sub>1 u u' u\<^sub>1 t. (l, u) \<preceq> (l', u') \<Longrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1\<rangle>
    \<Longrightarrow> \<exists>u\<^sub>1'. A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1'\<rangle> \<and> (l\<^sub>1, u\<^sub>1) \<preceq> (l\<^sub>1, u\<^sub>1')"
  assumes refl: "\<And>u. u \<preceq> u" and trans: "\<And>u v w. u \<preceq> v \<Longrightarrow> v \<preceq> w \<Longrightarrow> u \<preceq> w"
begin

lemma simE:
  assumes "(l, u) \<preceq> (l', u')" "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1\<rangle>"
  obtains u\<^sub>1' where "A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1'\<rangle>" "(l\<^sub>1, u\<^sub>1) \<preceq> (l\<^sub>1, u\<^sub>1')"
  using assms sim by blast

definition abs :: "'l \<Rightarrow> ('c, 't) zone \<Rightarrow> ('c, 't) zone" ("\<alpha> _ _" [71,71] 71) where
  "\<alpha> l W = {v. \<exists>v' \<in> W. (l, v) \<preceq> (l, v')}"

lemma simulation_mono:
  assumes "\<alpha> l Z \<subseteq> \<alpha> l Z'" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l\<^sub>1, Z\<^sub>1\<rangle>" "A \<turnstile>' \<langle>l, Z'\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l\<^sub>1, Z\<^sub>1'\<rangle>"
  shows "\<alpha> l\<^sub>1 Z\<^sub>1 \<subseteq> \<alpha> l\<^sub>1 Z\<^sub>1'"
proof -
  have
    "Z\<^sub>1 = {u'. \<exists>u \<in> Z. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u'\<rangle>}" "Z\<^sub>1' = {u'. \<exists>u \<in> Z'. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u'\<rangle>}"
    by (intro step_trans_z'_exact_strong assms(2,3))+
  show ?thesis
    unfolding abs_def
  proof clarsimp
    fix u v
    assume "v \<in> Z\<^sub>1" "(l\<^sub>1, u) \<preceq> (l\<^sub>1, v)"
    with \<open>Z\<^sub>1 = _\<close> obtain u\<^sub>0 where "u\<^sub>0 \<in> Z" and step: "A \<turnstile>' \<langle>l, u\<^sub>0\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, v\<rangle>"
      by auto
    from \<open>u\<^sub>0 \<in> Z\<close> \<open>\<alpha> l Z \<subseteq> _\<close> obtain v\<^sub>0 where "v\<^sub>0 \<in> Z'" "(l, u\<^sub>0) \<preceq> (l, v\<^sub>0)"
      unfolding abs_def using refl[of "(l, u\<^sub>0)"] by auto
    from simE[OF \<open>(l, u\<^sub>0) \<preceq> (l, v\<^sub>0)\<close> step] obtain v' where
      "A \<turnstile>' \<langle>l, v\<^sub>0\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, v'\<rangle>" "(l\<^sub>1, v) \<preceq> (l\<^sub>1, v')" .
    with \<open>v\<^sub>0 \<in> Z'\<close> \<open>Z\<^sub>1' = _\<close> have "v' \<in> Z\<^sub>1'"
      by auto
    moreover from \<open>_ \<preceq> (l\<^sub>1, v)\<close> \<open>(l\<^sub>1, v) \<preceq> _\<close> have "(l\<^sub>1, u) \<preceq> (l\<^sub>1, v')"
      by (rule trans)
    ultimately show "\<exists>x\<in>Z\<^sub>1'. (l\<^sub>1, u) \<preceq> (l\<^sub>1, x)"
      by fast
  qed
qed

lemma simulation:
  assumes "\<alpha> l Z = \<alpha> l Z'" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z\<^sub>1\<rangle>" "A \<turnstile>' \<langle>l, Z'\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z\<^sub>1'\<rangle>"
  shows "\<alpha> l' Z\<^sub>1 = \<alpha> l' Z\<^sub>1'"
  using simulation_mono assms by blast

lemma simulation':
  assumes "\<alpha> l Z = \<alpha> l Z'" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z\<^sub>1\<rangle>"
  shows "\<exists>Z\<^sub>1'. A \<turnstile>' \<langle>l, Z'\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z\<^sub>1'\<rangle> \<and> \<alpha> l' Z\<^sub>1 = \<alpha> l' Z\<^sub>1'"
proof -
  from \<open>A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z\<^sub>1\<rangle>\<close> obtain Z\<^sub>1' where "A \<turnstile>' \<langle>l, Z'\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z\<^sub>1'\<rangle>"
    by (auto elim!: step_trans_z'.cases step_trans_z.cases)
  with simulation assms show ?thesis
    by blast
qed

lemma abs_involutive:
  "\<alpha> l (\<alpha> l Z) = \<alpha> l Z"
  unfolding abs_def by (auto intro: refl trans)

lemma abs_widens:
  "Z \<subseteq> \<alpha> l Z"
  unfolding abs_def by (auto intro: refl)

text \<open>
  This is Lemma 4 from the paper
  ``Better Abstractions for Timed Automata'' (\<^url>\<open>https://arxiv.org/abs/1110.3705\<close>)
\<close>
corollary transition_compatibility:
  assumes "A \<turnstile>' \<langle>l, \<alpha> l Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', W\<rangle>" "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>"
  shows "\<alpha> l' W = \<alpha> l' Z'"
  by (rule simulation[OF _ assms(1,2)], rule abs_involutive)

inductive step_abs ::
  "('a, 'c, 't, 'l) ta \<Rightarrow> 'l \<Rightarrow> ('c, 't) zone \<Rightarrow> 'a \<Rightarrow> 'l \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<alpha>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_alpha:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, \<alpha> l Z\<rangle> \<leadsto>\<^bsub>\<alpha>(a)\<^esub> \<langle>l'', \<alpha> l'' Z''\<rangle>"

interpretation sim1: Simulation where
  A = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" and
  B = "\<lambda>(l, Z) (l', Z'). \<exists>a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<alpha>(a)\<^esub> \<langle>l', Z'\<rangle>" and
  sim = "\<lambda>(l, u) (l', Z). l' = l \<and> u \<in> Z \<and> \<alpha> l Z = Z"
  apply standard
  unfolding step'.simps step_abs.simps
  apply clarsimp
  subgoal premises prems for l v l'' v'' Z d l' v' a
  proof -
    from \<open>v \<in> Z\<close> \<open>A \<turnstile> \<langle>l, v\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', v'\<rangle>\<close> obtain Z' where
      "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>" "v' \<in> Z'"
      by (auto dest: step_t_z_complete)
    moreover obtain Z'' where
      "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>" "v'' \<in> Z''"
      using prems \<open>v' \<in> Z'\<close> by (auto dest: step_a_z_complete)
    ultimately show ?thesis
      using \<open>\<alpha> l Z = Z\<close> abs_involutive abs_widens by blast
  qed
  done

interpretation sim2: Simulation where
  A = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" and
  B = "\<lambda>(l, Z) (l', Z'). \<exists>a. A \<turnstile> \<langle>l, \<alpha> l Z\<rangle> \<leadsto>\<^bsub>\<alpha>(a)\<^esub> \<langle>l', \<alpha> l' Z'\<rangle>" and
  sim = "\<lambda>(l, u) (l', Z). l' = l \<and> u \<in> Z"
  apply standard
  unfolding step'.simps step_abs.simps
  apply clarsimp
  subgoal premises prems for l v l'' v'' Z d l' v' a
  proof -
    from \<open>v \<in> Z\<close> \<open>A \<turnstile> \<langle>l, v\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', v'\<rangle>\<close> obtain Z' where
      "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>" "v' \<in> Z'"
      by (auto dest: step_t_z_complete)
    moreover obtain Z'' where
      "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>" "v'' \<in> Z''"
      using prems \<open>v' \<in> Z'\<close> by (auto dest: step_a_z_complete)
    ultimately show ?thesis
      by fastforce
  qed
  done

sublocale self_simulation: Self_Simulation where
  E = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" and P = "\<lambda>_. True"
  apply standard
  apply (force dest: sim simp: step_trans'_step_trans_iff[symmetric])
  using refl trans unfolding reflp_def transp_def by blast+

end


context Regions_TA
begin

definition sim_regions (infix "\<equiv>\<^sub>M" 60) where
  "sim_regions \<equiv> \<lambda>(l, u) (l', u').
    (l' = l \<and> l \<in> state_set A \<and> (\<exists>R \<in> \<R> l. u \<in> R \<and> u' \<in> R))
  \<or> (l \<notin> state_set A \<or> u \<notin> V) \<and> (l' \<notin> state_set A \<or> u' \<notin> V)"

abbreviation
  "valid \<equiv> \<lambda>(l, u). l \<in> state_set A \<and> u \<in> V"

lemma \<R>_I:
  assumes "l \<in> state_set A" "u \<in> V"
  shows "\<exists>R \<in> \<R> l. u \<in> R"
  using assms regions_partition[where \<R> = \<open>\<R> l\<close> and X = X and k = "k l" and u = u] \<R>_def[of l]
  unfolding V_def by blast

lemma regions_finite:
  "finite (\<R> l)"
  using finite_\<R>[OF finite] unfolding \<R>_def .

lemma valid_iff:
  "valid (l, u) \<longleftrightarrow> valid (l', u')" if "(l, u) \<equiv>\<^sub>M (l', u')"
  using that unfolding sim_regions_def by (auto dest: \<R>_V)

lemma \<R>_distinct:
  "R' = R" if "R \<in> \<R> l" "R' \<in> \<R> l" "u \<in> R" "u \<in> R'"
  using that \<R>_regions_distinct[where \<R> = \<open>\<R> l\<close> and X = X and k = "k l"] \<R>_def[of l] by metis

lemma refl:
  "(l, u) \<equiv>\<^sub>M (l, u)"
  unfolding sim_regions_def by (cases "valid (l, u)"; simp add: \<R>_I)

lemma sym:
  "(l, u) \<equiv>\<^sub>M (l', u') \<longleftrightarrow> (l', u') \<equiv>\<^sub>M (l, u)"
  unfolding sim_regions_def by auto

lemma trans:
  "(l, u) \<equiv>\<^sub>M (l'', u'')" if "(l, u) \<equiv>\<^sub>M (l', u')" "(l', u') \<equiv>\<^sub>M (l'', u'')"
proof (cases "valid (l, u)")
  case True
  with that have "valid (l, u)" "valid (l', u')" "valid (l'', u'')"
    using valid_iff by metis+
  then show ?thesis
    using that unfolding sim_regions_def by (auto dest: \<R>_distinct)
next
  case False
  with that have "\<not> valid (l, u)" "\<not> valid (l', u')" "\<not> valid (l'', u'')"
    using valid_iff by metis+
  then show ?thesis
    unfolding sim_regions_def by simp
qed

lemma equiv:
  "equivp (\<equiv>\<^sub>M)"
  using refl sym trans by - (rule equivpI; unfold equivp_def reflp_def symp_def transp_def; fast)

lemma same_loc:
  "l' = l" if "(l, u) \<equiv>\<^sub>M (l', u')" "valid (l, u)"
  using that unfolding sim_regions_def by auto

lemma regions_simI:
  "(l, u) \<equiv>\<^sub>M (l, u')" if "l \<in> state_set A" "R \<in> \<R> l" "u \<in> R" "u' \<in> R"
  using that unfolding sim_regions_def by auto

lemma regions_simD:
  "u' \<in> R" if "l \<in> state_set A" "R \<in> \<R> l" "u \<in> R" "(l, u) \<equiv>\<^sub>M (l', u')"
  using that unfolding sim_regions_def by (auto dest: \<R>_V \<R>_distinct)

lemma finite_quotient:
  "finite (UNIV // {(x, y). x \<equiv>\<^sub>M y})"
proof -
  let ?S = "state_set A \<times> (\<Union>l \<in> state_set A. \<R> l)" and ?f = "\<lambda>(l, R). from_R l R"
  let ?invalid = "{(l, u). \<not>valid (l, u)}"
  have "Collect ((\<equiv>\<^sub>M) (l, u)) \<in> ?f ` ?S"
    if "valid (l, u)" for l u
  proof -
    from that refl[of l u] obtain R where *: "l \<in> state_set A" "R \<in> \<R> l" "u \<in> R"
      unfolding sim_regions_def by auto
    with \<open>valid _\<close> have "Collect ((\<equiv>\<^sub>M) (l, u)) = from_R l R"
      unfolding from_R_def by (auto simp: same_loc intro: regions_simI regions_simD)
    with * show ?thesis
      by auto
  qed
  moreover have "Collect ((\<equiv>\<^sub>M) (l, u)) = ?invalid" if "\<not> valid (l, u)" for l u
    using that unfolding sim_regions_def by (auto simp: \<R>_V)
  ultimately have "UNIV // {(x, y). x \<equiv>\<^sub>M y} \<subseteq> (?f ` ?S) \<union> {?invalid}"
    apply -
    apply rule
    apply (erule quotientE)
    apply clarsimp
    by blast
  also have "finite \<dots>"
     by (blast intro: finite_state_set regions_finite)+
   finally show ?thesis .
 qed

sublocale region_self_simulation: Self_Simulation where
  E = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" and sim = "(\<equiv>\<^sub>M)" and P = valid
  apply (standard; clarsimp?)
  subgoal simulation premises prems for l u l1 u1 l' u'
  proof -
    from \<open>u \<in> V\<close> \<open>A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l1, u1\<rangle>\<close>[THEN step_r'_complete_spec] obtain a R1 where
      "u1 \<in> R1" "A,\<R> \<turnstile> \<langle>l, [u]\<^sub>l\<rangle> \<leadsto>\<^sub>a \<langle>l1, R1\<rangle>"
      by blast
    moreover from prems have "u' \<in> [u]\<^sub>l"
      unfolding V_def by (auto elim: regions_simD dest: region_cover')
    ultimately obtain u1' where "u1' \<in> R1" "A \<turnstile>' \<langle>l, u'\<rangle> \<rightarrow> \<langle>l1, u1'\<rangle>"
      by (auto 4 3 dest: step_r'_sound)
    moreover from \<open>u1 \<in> R1\<close> \<open>u1' \<in> R1\<close> \<open>A,\<R> \<turnstile> \<langle>l, [u]\<^sub>l\<rangle> \<leadsto>\<^sub>a \<langle>l1, R1\<rangle>\<close> have "(l1, u1) \<equiv>\<^sub>M (l1, u1')"
      by (meson regions_simI step_r'_\<R> step_r'_state_set)
    moreover from prems have "valid (l', u')"
      using valid_iff by auto
    moreover from prems have "l' = l"
      by - (erule same_loc, simp)
    ultimately show ?thesis
      using \<open>(l, u) \<equiv>\<^sub>M (l', u')\<close> by blast
  qed
  subgoal invariant
    by (meson \<R>_V step_r'_\<R> step_r'_complete_spec step_r'_state_set)
  using refl trans unfolding reflp_def transp_def by fast+

end


definition
  "constraints_of A l = \<Union> (set ` insert (inv_of A l) {g. \<exists>a r l'. (l, g, a, r, l') \<in> trans_of A})"

definition
  "is_lower A L \<equiv>
  \<forall>l. \<forall>ac \<in> constraints_of A l. case ac of
    GT c x \<Rightarrow> L l c \<ge> x |
    GE c x \<Rightarrow> L l c \<ge> x |
    EQ c x \<Rightarrow> L l c \<ge> x |
    _ \<Rightarrow> True"

definition
  "is_upper A U \<equiv>
  \<forall>l. \<forall>ac \<in> constraints_of A l. case ac of
    LT c x \<Rightarrow> U l c \<ge> x |
    LE c x \<Rightarrow> U l c \<ge> x |
    EQ c x \<Rightarrow> U l c \<ge> x |
    _ \<Rightarrow> True"

definition
  "is_locally_consistent A k \<equiv>
  \<forall>(l, g, a, r, l') \<in> trans_of A. \<forall>x \<in> clk_set A - set r. k l x \<ge> k l' x"

lemma is_locally_consistentD:
  assumes "is_locally_consistent A k" "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l\<^sub>1"
  shows "\<forall>x \<in> clk_set A - set r. k l x \<ge> k l\<^sub>1 x"
  using assms unfolding is_locally_consistent_def by fast

context
  fixes A :: "('a, 'c, 't :: time, 'l) ta"
  fixes L :: "'l \<Rightarrow> 'c \<Rightarrow> 't" and U :: "'l \<Rightarrow> 'c \<Rightarrow> 't"
  assumes is_lower: "is_lower A L" and is_upper: "is_upper A U"
      and locally_consistent: "is_locally_consistent A L" "is_locally_consistent A U"
begin

definition sim :: "'l \<times> ('c \<Rightarrow> 't :: time) \<Rightarrow> 'l \<times> ('c \<Rightarrow> 't) \<Rightarrow> bool" (infix "\<preceq>" 60) where
  "sim \<equiv> \<lambda>(l, v) (l', v').
    l' = l \<and> (\<forall>x \<in> clk_set A. (v' x < v x \<longrightarrow> v' x > L l x) \<and> (v' x > v x \<longrightarrow> v x > U l x))"

lemma simE:
  assumes "(l, v) \<preceq> (l', v')" "x \<in> clk_set A"
  obtains "l' = l" "v x = v' x"
  | "l' = l" "v x > v' x" "v' x > L l x"
  | "l' = l" "v x < v' x" "v x > U l x"
  using assms unfolding sim_def by force

lemma sim_locD:
  "l' = l" if "(l, v) \<preceq> (l', v')"
  using that unfolding sim_def by auto

lemma sim_nonneg:
  "u x \<ge> 0" if "(l, u) \<preceq> (l', u')" "u' x \<ge> 0" "x \<in> clk_set A" "U l x \<ge> 0"
  using that by (auto elim: simE)

lemma sim_time_shift:
  "(l, v \<oplus> d) \<preceq> (l', v' \<oplus> d)" if "(l, v) \<preceq> (l', v')" "d \<ge> 0"
  using that unfolding cval_add_def sim_def by simp (metis add.commute add_strict_increasing2)

lemma constraints_of_clk_set:
  assumes "g \<in> constraints_of A l"
  shows
    "g = LT c x \<Longrightarrow> c \<in> clk_set A"
    "g = LE c x \<Longrightarrow> c \<in> clk_set A"
    "g = EQ c x \<Longrightarrow> c \<in> clk_set A"
    "g = GE c x \<Longrightarrow> c \<in> clk_set A"
    "g = GT c x \<Longrightarrow> c \<in> clk_set A"
  using assms
  unfolding constraints_of_def
  unfolding collect_clkvt_def clkp_set_def
  unfolding
    Timed_Automata.clkp_set_def Timed_Automata.collect_clki_def Timed_Automata.collect_clkt_def
  unfolding collect_clock_pairs_def
  by auto (smt UnCI Union_iff constraint_pair.simps fst_conv image_eqI mem_Collect_eq)+

lemma constraint_simulation:
  assumes "g \<in> constraints_of A l" "(l, v) \<preceq> (l', v')" "v \<turnstile>\<^sub>a g"
  shows "v' \<turnstile>\<^sub>a g"
  using assms(3,1,2) is_lower is_upper unfolding is_lower_def is_upper_def
  by cases(all \<open>frule (1) constraints_of_clk_set; erule (1) simE; fastforce simp: clock_val_a.simps\<close>)

lemma inv_simulation:
  assumes "v \<turnstile> inv_of A l" "(l, v) \<preceq> (l', v')"
  shows "v' \<turnstile> inv_of A l"
proof -
  from assms(1) have "\<forall>ac \<in> set (inv_of A l). v \<turnstile>\<^sub>a ac"
    unfolding clock_val_def list_all_iff by auto
  moreover have "\<forall>ac \<in> set (inv_of A l). ac \<in> constraints_of A l"
    unfolding constraints_of_def by auto
  ultimately show ?thesis
    using \<open>_ \<preceq> _\<close> unfolding clock_val_def list_all_iff by (auto intro: constraint_simulation)
qed

lemma guard_simulation:
  assumes "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l\<^sub>1" "v \<turnstile> g" "(l, v) \<preceq> (l', v')"
  shows "v' \<turnstile> g"
proof -
  from assms(2) have "\<forall>ac \<in> set g. v \<turnstile>\<^sub>a ac"
    unfolding clock_val_def list_all_iff by auto
  moreover from assms(1) have "\<forall>ac \<in> set g. ac \<in> constraints_of A l"
    unfolding constraints_of_def by auto
  ultimately show ?thesis
    using \<open>_ \<preceq> _\<close> unfolding clock_val_def list_all_iff by (auto intro: constraint_simulation)
qed

lemma sim_delay:
  assumes "(l, v) \<preceq> (l', v')" "d \<ge> 0"
  shows "(l, v \<oplus> d) \<preceq> (l', v' \<oplus> d)"
  using assms unfolding cval_add_def sim_def by (auto simp: add_strict_increasing2 gt_swap)

lemma clock_set_iff:
  "([r\<rightarrow>0]v) c = (if c \<in> set r then 0 else v c)"
  by auto

lemma sim_reset:
  assumes "A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l\<^sub>1" "v \<turnstile> g" "(l, v) \<preceq> (l', v')"
  shows "(l\<^sub>1, [r\<rightarrow>0]v) \<preceq> (l\<^sub>1, [r\<rightarrow>0]v')"
proof -
  from assms(1) have
    "\<forall>x \<in> clk_set A - set r. L l x \<ge> L l\<^sub>1 x" "\<forall>x \<in> clk_set A - set r. U l x \<ge> U l\<^sub>1 x"
    using locally_consistent by - (intro is_locally_consistentD; assumption)+
  then show ?thesis
    using assms(2,3) unfolding sim_def by (auto simp: clock_set_iff) force+
qed

lemma step_t_simulation:
  "(l, u) \<preceq> (l', u') \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l\<^sub>1, u\<^sub>1\<rangle>
  \<Longrightarrow> \<exists>u\<^sub>1'. A \<turnstile> \<langle>l\<^sub>1, u'\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l\<^sub>1, u\<^sub>1'\<rangle> \<and> (l\<^sub>1, u\<^sub>1) \<preceq> (l, u\<^sub>1')"
  unfolding step_t.simps by (auto dest: sim_delay inv_simulation sim_locD)

lemma step_a_simulation:
  "(l, u) \<preceq> (l', u') \<Longrightarrow> A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l\<^sub>1, u\<^sub>1\<rangle>
  \<Longrightarrow> \<exists>u\<^sub>1'. A \<turnstile> \<langle>l, u'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l\<^sub>1, u\<^sub>1'\<rangle> \<and> (l\<^sub>1, u\<^sub>1) \<preceq> (l\<^sub>1, u\<^sub>1')"
  unfolding step_a.simps
  apply clarsimp
  apply (frule (2) guard_simulation)
  apply (drule (2) sim_reset[rotated -1])
  apply (frule (1) inv_simulation)
  apply auto
  done

lemma step_trans_simulation:
  "(l, u) \<preceq> (l', u') \<Longrightarrow> A \<turnstile>\<^sub>t \<langle>l, u\<rangle> \<rightarrow>\<^bsub>t\<^esub> \<langle>l\<^sub>1, u\<^sub>1\<rangle>
  \<Longrightarrow> \<exists>u\<^sub>1'. A \<turnstile>\<^sub>t \<langle>l, u'\<rangle> \<rightarrow>\<^bsub>t\<^esub> \<langle>l\<^sub>1, u\<^sub>1'\<rangle> \<and> (l\<^sub>1, u\<^sub>1) \<preceq> (l\<^sub>1, u\<^sub>1')"
  unfolding step_trans.simps
  apply clarsimp
  apply (frule (2) guard_simulation)
  apply (drule (2) sim_reset[rotated -1])
  apply (frule (1) inv_simulation)
  apply auto
  done

interpretation Time_Abstract_Simulation A sim
  apply standard
  subgoal
    unfolding step_trans'.simps using step_t_simulation step_trans_simulation
    by simp (metis sim_locD)
  subgoal
    unfolding sim_def by auto
  subgoal premises prems for u v w
  proof -
    define clks where "clks = clk_set A"
    from prems show ?thesis
      unfolding sim_def clks_def[symmetric] by fastforce+
  qed
  done

end





locale Invariant_Simulation =
  fixes L :: "'l set" and M :: "'l \<Rightarrow> 's set"
    and SE E SE' E' sim :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool"
  assumes SE_SE':
    "\<And>l l' x y x'. sim (l, x) (l, x') \<Longrightarrow> SE (l, x) (l', y)
    \<Longrightarrow> \<exists>y'. SE' (l, x') (l', y') \<and> sim (l', y) (l', y')"
  assumes SE'_SE:
    "\<And>l l' x y x' y'. sim (l, x) (l, x') \<Longrightarrow> sim (l', y) (l', y') \<Longrightarrow> SE' (l, x') (l', y')
    \<Longrightarrow> SE (l, x) (l', y)"
  and E'_E:
    "\<And>l l' a a' b'. sim (l, a) (l, a') \<Longrightarrow> E' (l, a') (l', b')
    \<Longrightarrow> (\<exists>b. E (l, a) (l', b) \<and> sim (l', b) (l', b'))"
begin

definition
  "M' \<equiv> \<lambda>l. {x'. \<exists>x \<in> M l. sim (l, x) (l, x')}"

lemma invariant_simulation:
  assumes
    "\<forall>l \<in> L. \<forall>s \<in> M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s'' \<in> M l'. SE (l', s') (l', s''))"
  shows
    "\<forall>l \<in> L. \<forall>s \<in> M' l. \<forall>l' s'. E' (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s'' \<in> M' l'. SE' (l', s') (l', s''))"
  apply safe
  subgoal
    using assms
    unfolding M'_def by (auto dest: E'_E)
  unfolding M'_def
proof (clarsimp)
  fix l :: 'l
      and s :: 's
      and l' :: 'l
      and s' :: 's
      and x :: 's
  assume "l \<in> L"
      and "E' (l, s) (l', s')"
      and "sim (l, x) (l, s)"
      and "x \<in> M l"
  with E'_E obtain x' where "sim (l', x') (l', s')" "E (l, x) (l', x')"
    by force
  with \<open>l \<in> L\<close> \<open>x \<in> M l\<close> assms obtain x'' where "x'' \<in> M l'" "SE (l', x') (l', x'')"
    by force
  from this(2) \<open>sim (l', x') _\<close> obtain s'' where
    "SE' (l', s') (l', s'')" "sim (l', x'') (l', s'')"
    by atomize_elim (rule SE_SE')
  with \<open>x'' \<in> _\<close> show "\<exists>s''. (\<exists>x\<in>M l'. sim (l', x) (l', s'')) \<and> SE' (l', s') (l', s'')"
    by auto
qed

interpretation Simulation where
  A = E' and
  B = E and
  sim = "\<lambda>(l, s) (l', s'). l' = l \<and> sim (l, s') (l', s)"
  by standard (auto dest: E'_E)

context
  fixes f :: "'l \<times> 's \<Rightarrow> nat"
begin

definition
  "f' \<equiv> \<lambda>(l, s). Max ({f (l, s') | s'. sim (l, s') (l, s) \<and> s' \<in> M l})"

context
  assumes finite: "finite L" "\<forall> l \<in> L. finite (M l)"
  assumes f_topo: "\<And>l s l1 s1 l2 s2.
    l \<in> L \<Longrightarrow> s \<in> M l \<Longrightarrow> l2 \<in> L \<Longrightarrow> s2 \<in> M l2 \<Longrightarrow> E (l, s) (l1, s1) \<Longrightarrow> SE (l1, s1) (l2, s2) \<Longrightarrow>
    f (l, s) \<le> f (l2, s2)"
begin

lemma topo_simulation: "\<And>l s l1 s1 l2 s2.
  l \<in> L \<Longrightarrow> s \<in> M' l \<Longrightarrow> l2 \<in> L \<Longrightarrow> s2 \<in> M' l2 \<Longrightarrow> E' (l, s) (l1, s1) \<Longrightarrow> SE' (l1, s1) (l2, s2) \<Longrightarrow>
  f' (l, s) \<le> f' (l2, s2)"
  unfolding M'_def
  apply (auto elim!: )
  subgoal for l s l' s' l'' s'' x x''
    proof -
  show "f' (l, s) \<le> f' (l'', s'')"
    if "l \<in> L"
      and "l'' \<in> L"
      and "E' (l, s) (l', s')"
      and "SE' (l', s') (l'', s'')"
      and "x \<in> M l"
      and "sim (l, x) (l, s)"
      and "x'' \<in> M l''"
      and "sim (l'', x'') (l'', s'')"
    proof -
      let ?S = "\<lambda> l'' s''. {f (l'', s') |s'. sim (l'', s') (l'', s'') \<and> s' \<in> M l''}"
      have finiteI: "finite (?S l s)" if "l \<in> L" for l s
        using finite that using [[simproc add: finite_Collect]] by simp
      have "Max (?S l s) \<in> ?S l s"
        using \<open>l \<in> L\<close> \<open>sim (l, x) _\<close> \<open>x \<in> _\<close> by (intro Max_in) (auto intro: finiteI)
      then obtain y where "f' (l, s) = f (l, y)" "sim (l, y) (l, s)" "y \<in> M l"
        unfolding f'_def by auto
      with E'_E \<open>E' _ _\<close> \<open>sim (l, x) _\<close> obtain x' where "E (l, y) (l', x')" "sim (l', x') (l', s')"
        by metis
      moreover from \<open>SE' _ _\<close> \<open>sim (l', x') _\<close> \<open>sim (l'', x'') _\<close> have "SE (l', x') (l'', x'')"
        using SE'_SE by metis
      ultimately have "f (l, y) \<le> f (l'', x'')"
        using that f_topo[of l y l'' x'' l' x'] \<open>y \<in> M l\<close> by auto
      with \<open>_ = f (l, y)\<close> have "f' (l, s) \<le> f (l'', x'')"
        by simp
      also from \<open>x'' \<in> _\<close> \<open>l'' \<in> _\<close> \<open>sim (l'', x'') _\<close> have "\<dots> \<le> f' (l'', s'')"
        unfolding f'_def by (auto intro: finiteI Max_ge)
      finally show ?thesis .
    qed
  qed
  done

end

end

end



locale Abstraction_Simulation =
  fixes L :: "'l set" and M :: "'l \<Rightarrow> 's set"
    and SE E SE' :: "('l \<times> 's) \<Rightarrow> ('l \<times> 's) \<Rightarrow> bool"
    and \<alpha> :: "'l \<Rightarrow> 's \<Rightarrow> 's"
  assumes SE_SE': "\<And>l l' x y. SE (l, x) (l', \<alpha> l' y) \<Longrightarrow> SE' (l, \<alpha> l x) (l', \<alpha> l' y)"
  assumes SE'_SE: "\<And>l l' x y. SE' (l, \<alpha> l x) (l', \<alpha> l' y) \<Longrightarrow> SE (l, x) (l', \<alpha> l' y)"
    and simulation:
      "\<And>l l' a a' b.
        \<alpha> l a = \<alpha> l a' \<Longrightarrow> E (l, a) (l', b) \<Longrightarrow> (\<exists>b'. E (l, a') (l', b') \<and> \<alpha> l' b = \<alpha> l' b')"
begin

definition
  "M' \<equiv> \<lambda>l. \<alpha> l ` M l"

inductive E' where
  "E (l, s) (l', s') \<Longrightarrow> E' (l, \<alpha> l s) (l', \<alpha> l' s')"

sublocale sim: Invariant_Simulation where
  sim = "\<lambda>(l, x) (l', y). l' = l \<and> y = \<alpha> l x" and
  SE = "\<lambda>(l, x) (l', y). SE (l, x) (l', \<alpha> l' y)" and
  SE' = "\<lambda>(l, x) (l', y). SE' (l, x) (l', y)" and
  E = E and
  E' = E'
  apply standard
  subgoal for l l' x y x'
    apply auto
    by (rule SE_SE')
  subgoal for l l' x y x' y'
    apply auto
    by (rule SE'_SE)
  subgoal for l l' a a' b'
    using simulation by (auto elim!: E'.cases)
  done

interpretation sim2: Simulation where
  sim = "\<lambda>(l, x) (l', y). l' = l \<and> y = \<alpha> l x" and
  A = E and
  B = E'
  by standard (force simp: E'.simps)

interpretation bisim: Bisimulation where
  sim = "\<lambda>(l, x) (l', y). l' = l \<and> y = \<alpha> l x" and
  A = E and
  B = E'
  apply standard
  subgoal
    using sim2.A_B_step .
  subgoal for a a' b'
    by (cases b') (auto dest: sim.E'_E[rotated])
  done

lemma simulationE:
  assumes "\<alpha> l a = \<alpha> l a'" "E (l, a) (l', b)"
  obtains b' where "E (l, a') (l', b')" "\<alpha> l' b = \<alpha> l' b'"
  using assms simulation by blast

lemma M'_eq:
  "sim.M' = M'"
  unfolding sim.M'_def M'_def by auto


lemma invariant_simulation:
  assumes
    "\<forall>l\<in>L. \<forall>s\<in>M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. SE (l', s') (l', \<alpha> l' s''))"
  shows
    "\<forall>l\<in>L. \<forall>s\<in>M' l. \<forall>l' s'. E' (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M' l'. SE' (l', s') (l', s''))"
  using sim.invariant_simulation assms unfolding M'_eq by fast

lemma \<comment> \<open>Alternative proof of: @{thm invariant_simulation}\<close>
  assumes
    "\<forall>l\<in>L. \<forall>s\<in>M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. SE (l', s') (l', \<alpha> l' s''))"
  shows
    "\<forall>l\<in>L. \<forall>s\<in>M' l. \<forall>l' s'. E' (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M' l'. SE' (l', s') (l', s''))"
unfolding M'_def
proof (safe; (erule E'.cases, clarsimp))
  fix x  l s l' s'
  assume "l \<in> L" "x \<in> M l" "(l, s) \<rightarrow> (l', s')" "\<alpha> l x = \<alpha> l s"
  then show "l' \<in> L"
    using assms simulation by metis
next
  fix l l' :: 'l and s s' x :: 's
  assume "l \<in> L" "E (l, s) (l', s')" "\<alpha> l x = \<alpha> l s" "x \<in> M l"
  with simulation obtain x' where "\<alpha> l' s' = \<alpha> l' x'" "E (l, x) (l', x')"
    by metis
  with \<open>l \<in> L\<close> \<open>x \<in> M l\<close> assms obtain x'' where "x'' \<in> M l'" "SE (l', x') (l', \<alpha> l' x'')"
    by force
  from this(2) have "SE' (l', \<alpha> l' x') (l', \<alpha> l' x'')"
    by (rule SE_SE')
  with \<open>x'' \<in> _\<close> \<open>\<alpha> l' s' = _\<close> show "\<exists>s''\<in>M l'. SE' (l', \<alpha> l' s') (l', \<alpha> l' s'')"
    by auto
qed


context
  fixes f :: "'l \<times> 's \<Rightarrow> nat"
  assumes finite: "finite L" "\<forall> l \<in> L. finite (M l)"
  assumes f_topo: "\<And>l s l1 s1 l2 s2.
    l \<in> L \<Longrightarrow> s \<in> M l \<Longrightarrow> l2 \<in> L \<Longrightarrow> s2 \<in> M l2 \<Longrightarrow> E (l, s) (l1, s1) \<Longrightarrow> SE (l1, s1) (l2, \<alpha> l2 s2)
    \<Longrightarrow> f (l, s) \<le> f (l2, s2)"
begin

definition
  "f' \<equiv> \<lambda>(l, s). Max ({f (l, s') | s'. \<alpha> l s' = s \<and> s' \<in> M l})"

lemma f'_eq:
  "sim.f' f = f'"
  unfolding sim.f'_def f'_def by (rule ext; clarsimp; metis)

lemma topo_simulation: "\<And>l s l1 s1 l2 s2.
  l \<in> L \<Longrightarrow> s \<in> M' l \<Longrightarrow> l2 \<in> L \<Longrightarrow> s2 \<in> M' l2 \<Longrightarrow> E' (l, s) (l1, s1) \<Longrightarrow> SE' (l1, s1) (l2, s2) \<Longrightarrow>
  f' (l, s) \<le> f' (l2, s2)"
  by (rule sim.topo_simulation[where f = f, OF finite, unfolded M'_eq f'_eq])
     ((rule f_topo; simp; fail), simp+)

lemma \<comment> \<open>Alternative proof of: @{thm topo_simulation}\<close>
  "\<And>l s l1 s1 l2 s2.
  l \<in> L \<Longrightarrow> s \<in> M' l \<Longrightarrow> l2 \<in> L \<Longrightarrow> s2 \<in> M' l2 \<Longrightarrow> E' (l, s) (l1, s1) \<Longrightarrow> SE' (l1, s1) (l2, s2) \<Longrightarrow>
  f' (l, s) \<le> f' (l2, s2)"
  unfolding M'_def
  apply (auto elim!: E'.cases)
  subgoal for l'' l s l' s' x s''
  proof -
    show "f' (l, \<alpha> l s) \<le> f' (l'', \<alpha> l'' s'')"
      if "l \<in> L" "l'' \<in> L" "SE' (l', \<alpha> l' s') (l'', \<alpha> l'' s'')" "E (l, s) (l', s')"
         "x \<in> M l" "s'' \<in> M l''" "\<alpha> l x = \<alpha> l s"
    proof -
      let ?S = "\<lambda> l'' s''. {f (l'', s') |s'. \<alpha> l'' s' = \<alpha> l'' s'' \<and> s' \<in> M l''}"
      have finiteI: "finite (?S l s)" if "l \<in> L" for l s
        using finite that using [[simproc add: finite_Collect]] by simp
      have "Max (?S l s) \<in> ?S l s"
        using \<open>l \<in> L\<close> \<open>\<alpha> l x = _\<close> \<open>x \<in> _\<close> by (intro Max_in) (auto intro: finiteI)
      then obtain y where "f' (l, \<alpha> l s) = f (l, y)" "\<alpha> l y = \<alpha> l s" "y \<in> M l"
        unfolding f'_def by auto
      with simulation[OF _ \<open>E _ _\<close>] \<open>\<alpha> l x = _\<close> obtain x' where
        "E (l, y) (l', x')" "\<alpha> l' x' = \<alpha> l' s'"
        by metis
      moreover from \<open>SE' _ _\<close> \<open>\<alpha> l' x' = \<alpha> l' s'\<close> have "SE (l', x') (l'', \<alpha> l'' s'')"
        using SE'_SE by metis
      ultimately have "f (l, y) \<le> f (l'', s'')"
        using that f_topo[of l y l'' s'' l' x'] \<open>y \<in> M l\<close> by auto
      with \<open>_ = f (l, y)\<close> have "f' (l, \<alpha> l s) \<le> f (l'', s'')"
        by simp
      also from \<open>s'' \<in> _\<close> \<open>l'' \<in> _\<close> have "\<dots> \<le> f' (l'', \<alpha> l'' s'')"
        unfolding f'_def by (auto intro: finiteI Max_ge)
      finally show ?thesis .
    qed
  qed
  done

end

end


context Time_Abstract_Simulation
begin

context
  fixes SE :: "('l \<times> ('c, 't) zone) \<Rightarrow> ('l \<times> ('c, 't) zone) \<Rightarrow> bool"
  assumes SE_subsumption: "\<And>l l' Z Z'. SE (l, Z) (l', Z') \<Longrightarrow> l' = l \<and> Z \<subseteq> \<alpha> l' Z'"
      and SE_determ:
      "\<And>l l' Z Z' W. SE (l, Z) (l', Z') \<Longrightarrow> \<alpha> l Z = \<alpha> l W \<Longrightarrow> SE (l, W) (l', Z')"
begin

lemma step_z'_step_trans_z'_iff:
  "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z''\<rangle> \<longleftrightarrow> (\<exists>t. A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z''\<rangle>)"
  using step_trans_z'_step_z' step_z'_step_trans_z' by metis

interpretation Abstraction_Simulation where
  SE = "\<lambda>(l, Z) (l', Z'). \<exists>W. Z' = \<alpha> l W \<and> SE (l, Z) (l', W)" and
  E = "\<lambda>(l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" and
  SE' = "\<lambda>(l, Z) (l', Z'). \<exists>W W'. Z = \<alpha> l W \<and> Z' = \<alpha> l' W' \<and> SE (l, W) (l', W')" and
  \<alpha> = abs
  apply (standard; clarsimp)
  subgoal
    using SE_subsumption by metis
  subgoal for l l' x y W W'
    using SE_subsumption SE_determ by metis
  subgoal
    unfolding step_z'_step_trans_z'_iff using simulation' by metis
  done

interpretation inv: Invariant_Simulation where
  SE = "\<lambda>(l, Z) (l', Z'). \<exists>W. l' = l \<and> \<alpha> l Z' = \<alpha> l W \<and> SE (l, Z) (l', W)" and
  E = "\<lambda>(l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" and E' = E' and
  SE' = "\<lambda>(l, Z) (l', Z'). \<exists>W W'. l' = l \<and> Z = \<alpha> l W \<and> Z' = \<alpha> l' W' \<and> SE (l, W) (l', W')" and
  sim = "\<lambda>(l, Z) (l', Z'). l' = l \<and> Z' = \<alpha> l Z"
  apply (standard; clarsimp simp: abs_involutive)
  subgoal for l Z' W
    by blast
  subgoal for l Z W Z' W'
    using SE_determ by auto
  subgoal for l l' Z Z'
    using sim.E'_E by auto
  done

end

end


locale Time_Abstract_Simulation_Sandwich =
  Regions_TA where A = A +
  Time_Abstract_Simulation where A = A for A :: "('a, 'c, real, 'l) ta" +
  assumes sim_V: "(l, u) \<preceq> (l', u') \<Longrightarrow> u' \<in> V \<Longrightarrow> u \<in> V"

  fixes I \<beta>
  assumes I_invariant: "I Z \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<Longrightarrow> I Z'"
  assumes \<beta>_\<alpha>:      "I Z \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> l \<in> state_set A \<Longrightarrow> \<beta> l Z \<subseteq> \<alpha> l Z"
      and \<beta>_widens: "I Z \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> l \<in> state_set A \<Longrightarrow> Z \<subseteq> \<beta> l Z"
      and \<beta>_I:      "I Z \<Longrightarrow> Z \<subseteq> V \<Longrightarrow> l \<in> state_set A \<Longrightarrow> I (\<beta> l Z)"
  and finite_abstraction: "finite {\<beta> l Z | l Z. I Z \<and> Z \<subseteq> V \<and> l \<in> state_set A}"

  fixes l\<^sub>0 :: 'l and Z\<^sub>0 :: "('c, real) zone"
  assumes l\<^sub>0_state_set: "l\<^sub>0 \<in> state_set A" and Z\<^sub>0_V: "\<forall>u \<in> Z\<^sub>0. u \<in> V" and Z\<^sub>0_I: "I Z\<^sub>0"
begin

inductive step_beta ::
  "('a, 'c, real, 'l) ta \<Rightarrow> 'l \<Rightarrow> ('c, real) zone \<Rightarrow> 'a \<Rightarrow> 'l \<Rightarrow> ('c, real) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<beta>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_beta:
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l'', \<beta> l'' Z''\<rangle>"

no_notation step_z_beta  ("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<beta>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61,61] 61)

no_notation step_z_alpha ("_ \<turnstile> \<langle>_, _\<rangle> \<leadsto>\<^bsub>\<alpha>(_)\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)

lemma step_beta_alt_def:
  "(\<exists>a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', W\<rangle>) \<longleftrightarrow> (\<exists>Z'. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle> \<and> W = \<beta> l' Z')"
  unfolding step_beta.simps step_z'_def by auto

lemma step_betaE:
  assumes "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', W\<rangle>"
  obtains Z' where "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" "W = \<beta> l' Z'"
  using step_beta_alt_def assms by metis

definition
  "loc_is l s \<equiv> \<forall>(l', _) \<in> s. l' = l"

lemma \<alpha>_V:
  "\<alpha> l Z \<subseteq> V" if "Z \<subseteq> V"
  using that sim_V unfolding V_def abs_def by auto

lemma \<beta>_V:
  "\<beta> l Z \<subseteq> V" if "Z \<subseteq> V" "I Z" "l \<in> state_set A"
  using \<beta>_\<alpha> \<alpha>_V that by blast

(* XXX Move *)
lemma step_z'_V:
  "Z' \<subseteq> V" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" "Z \<subseteq> V"
  by (meson step_z_V step_z'_def that)

text \<open>Corresponds to lemma 6 of @{cite "Li:FORMATS:2009"}.\<close>
lemma backward_simulation:
  assumes
    "b \<in> S'" "loc_is l S" "loc_is l' S'" "A \<turnstile> \<langle>l, R_of S\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', R_of S'\<rangle>"
    "I (R_of S)" "R_of S \<subseteq> V"
  shows "\<exists>a\<in>S. \<exists>b'. (case a of (l, u) \<Rightarrow> \<lambda>(l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>) b' \<and> b \<preceq> b'"
proof -
  let ?Z = "R_of S" and ?Z' = "R_of S'"
  obtain u1 where "b = (l', u1)"
    using assms(1,3) unfolding loc_is_def by (cases b) auto
  then have "u1 \<in> ?Z'"
    using assms(1) by blast
  from assms(4) obtain Z' where "A \<turnstile> \<langle>l, ?Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" "?Z' = \<beta> l' Z'"
    by (erule step_betaE)
  then have "\<beta> l' Z' \<subseteq> \<alpha> l' Z'"
    using assms(5,6) by (intro \<beta>_\<alpha>) (auto dest: I_invariant step_z'_V step_z_state_setI2)
  with \<open>u1 \<in> ?Z'\<close> \<open>?Z' = _\<close> obtain u1' where "u1' \<in> Z'" "(l', u1) \<preceq> (l', u1')"
    unfolding abs_def by auto
  with \<open>A \<turnstile> \<langle>l, ?Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>\<close> obtain u where "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u1'\<rangle>" "u \<in> ?Z"
    by (meson step_z_sound')
  with \<open>_ \<preceq> _\<close> show ?thesis
    using assms(2) unfolding R_of_def loc_is_def \<open>b = _\<close> by fastforce
qed

lemma step'_step_beta:
  assumes
    "(l, u) \<in> a'" "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" "loc_is l1 a'" "R_of a' \<subseteq> V" "I (R_of a')"
  shows
    "\<exists>b'. (\<exists>a l l'. loc_is l a' \<and> loc_is l' b' \<and> a' \<noteq> {} \<and> b' \<noteq> {} \<and>
            A \<turnstile> \<langle>l, R_of a'\<rangle> \<leadsto>\<^bsub>\<beta>a\<^esub> \<langle>l', R_of b'\<rangle>) \<and> (l', u') \<in> b'"
proof -
  let ?Z = "R_of a'"
  from \<open>(l, u) \<in> _\<close> \<open>loc_is _ _\<close> have [simp]: "l1 = l"
    unfolding loc_is_def by auto
  from assms(1) have "u \<in> ?Z"
    unfolding R_of_def by force
  with assms(2) obtain Z' where step: "A \<turnstile> \<langle>l, ?Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" "u' \<in> Z'"
    by (metis step_z_complete')
  then obtain a where "A \<turnstile> \<langle>l, R_of a'\<rangle> \<leadsto>\<^bsub>\<beta>a\<^esub> \<langle>l', \<beta> l' Z'\<rangle>"
    by atomize_elim (unfold step_beta_alt_def, fast)
  moreover from \<beta>_widens have "u' \<in> \<beta> l' Z'"
    using step \<open>_ \<subseteq> V\<close> \<open>I ?Z\<close> by (blast dest: step_z'_V I_invariant step_z_state_setI2)
  ultimately show ?thesis
    using \<open>loc_is _ _\<close> \<open>(l, u) \<in> _\<close>
    by (inst_existentials "from_R l' (\<beta> l' Z')" a l l')
       (auto simp: from_R_def loc_is_def R_of_def image_def)
qed

definition beta_step where
  "beta_step \<equiv> \<lambda>s s'. \<exists>a l l'. loc_is l s \<and> loc_is l' s' \<and> s \<noteq> {} \<and> s' \<noteq> {} \<and>
     A \<turnstile> \<langle>l, R_of s\<rangle> \<leadsto>\<^bsub>\<beta>(a)\<^esub> \<langle>l', R_of s'\<rangle>"

lemma beta_step_inv:
  assumes "beta_step a b" "\<exists>l\<in>state_set A. loc_is l a \<and> R_of a \<subseteq> V \<and> I (R_of a)"
  shows "\<exists>l\<in>state_set A. loc_is l b \<and> R_of b \<subseteq> V \<and> I (R_of b)"
  using assms unfolding beta_step_def
  using \<beta>_V step_z'_V step_z_state_setI2 \<beta>_I I_invariant step_betaE by metis

lemma from_R_R_of:
  assumes "loc_is l S"
  shows "from_R l (R_of S) = S"
  using assms from_R_R_of unfolding loc_is_def by force

interpretation backward_simulation: Backward_Double_Simulation_Complete where
  E = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" and
  G = beta_step and
  sim' = "(\<equiv>\<^sub>M)" and
  P = valid and
  Q = "\<lambda>s. \<exists>l \<in> state_set A. loc_is l s \<and> R_of s \<subseteq> V \<and> I (R_of s)" and
  a\<^sub>0 = "from_R l\<^sub>0 Z\<^sub>0"
proof (standard, goal_cases)
  case (1 a b a')
  then show ?case
    by (intro self_simulation.A_B_step TrueI)
next
  case (2 b B A)
  then show ?case
    unfolding beta_step_def apply clarify
    thm backward_simulation
    apply (rule backward_simulation, assumption+)
    sorry
next
  case (3 a)
  then show ?case
    by (rule refl)
next
  case 4
  then show ?case
    by (rule self_simulation.trans)
next
  case 5
  then show ?case
    by (rule equiv)
next
  case 6
  then show ?case
    by (rule finite_quotient)
next
  case (7 a b a')
  then show ?case
    unfolding beta_step_def by clarify (rule step'_step_beta)
next
  case (8 a b)
  then show ?case
    by (rule region_self_simulation.PA_invariant.invariant)
next
  case (9 a b)
  then show ?case
    by (rule beta_step_inv[rotated])
next
  case 10
  let ?S = "{from_R l (\<beta> l Z) | l Z. l \<in> state_set A \<and> Z \<subseteq> V \<and> I Z}"
  have "{x. beta_step\<^sup>*\<^sup>* (from_R l\<^sub>0 Z\<^sub>0) x} \<subseteq> ?S \<union> {from_R l\<^sub>0 Z\<^sub>0}"
    apply rule
    apply simp
    subgoal
    proof (induction "from_R l\<^sub>0 Z\<^sub>0" _ rule: rtranclp.induct)
      case rtrancl_refl
      then show ?case
        by simp
    next
      case (rtrancl_into_rtrancl b c)
      let ?Z = "R_of b" and ?Z' = "R_of c"
      from \<open>beta_step b c\<close> guess a l l'
        unfolding beta_step_def by clarify
      note step = this
      with rtrancl_into_rtrancl(2) \<open>loc_is l b\<close> have "l \<in> state_set A" "?Z \<subseteq> V" "I ?Z"
        using Z\<^sub>0_V Z\<^sub>0_I l\<^sub>0_state_set \<beta>_V \<beta>_I
         apply auto
          apply (auto simp: loc_is_def from_R_def)
        apply blast
        done
      with step(1,2,5) show ?case
        using from_R_R_of step_z_state_setI2 step_z'_V step_betaE I_invariant by metis
    qed
    done
  moreover have "finite (?S \<union> {from_R l\<^sub>0 Z\<^sub>0})"
  proof -
    let ?T = "(\<lambda>(l, Z). from_R l Z) ` (state_set A \<times> {\<beta> l Z |l Z. I Z \<and> Z \<subseteq> V \<and> l \<in> state_set A})"
    have "?S \<subseteq> ?T"
      by auto
    also from finite_state_set finite_abstraction have "finite ?T"
      by auto
    finally show ?thesis
      by fast
  qed
  ultimately show ?case
    by (rule finite_subset)
next
  case (11 a)
  then show ?case
    unfolding loc_is_def by auto
next
  case 12
  then show ?case
    using l\<^sub>0_state_set Z\<^sub>0_V Z\<^sub>0_I by (auto simp: V_def loc_is_def from_R_def R_of_def image_def)
qed

end



context Regions
begin

inductive step_z_dbm' ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> 't :: {linordered_cancel_ab_monoid_add,uminus} DBM
    \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 't DBM \<Rightarrow> bool"
("_ \<turnstile>' \<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61) for A l D a l'' D''
where
  "A \<turnstile>' \<langle>l,D\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'',D''\<rangle>" if "A \<turnstile> \<langle>l,D\<rangle> \<leadsto>\<^bsub>v,n,\<tau>\<^esub> \<langle>l',D'\<rangle>" "A \<turnstile> \<langle>l',D'\<rangle> \<leadsto>\<^bsub>v,n,\<upharpoonleft>a\<^esub> \<langle>l'',D''\<rangle>"

lemmas step_z_dbm'_def = step_z_dbm'.simps

inductive step_impl' ::
  "('a, nat, 't :: linordered_ab_group_add, 's) ta \<Rightarrow> 's \<Rightarrow> 't DBM'
    \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 't DBM' \<Rightarrow> bool"
("_ \<turnstile>\<^sub>I' \<langle>_, _\<rangle> \<leadsto>\<^bsub>_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61) for A l D a l'' D''
where
  "A \<turnstile>\<^sub>I' \<langle>l,D\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l'',D''\<rangle>" if "A \<turnstile>\<^sub>I \<langle>l, D\<rangle> \<leadsto>\<^bsub>n,\<tau>\<^esub> \<langle>l',D'\<rangle>" "A \<turnstile>\<^sub>I \<langle>l',D'\<rangle> \<leadsto>\<^bsub>n,\<upharpoonleft>a\<^esub> \<langle>l'',D''\<rangle>"

lemmas step_impl'_def = step_impl'.simps

end


definition
  "dbm_nonneg n M \<equiv> \<forall>i \<le> n. i > 0 \<longrightarrow> M 0 i \<le> 0"

named_theorems dbm_nonneg

lemma dbm_nonneg_And[dbm_nonneg]:
  assumes "dbm_nonneg n M" "dbm_nonneg n M'"
  shows "dbm_nonneg n (And M M')"
  using assms by (auto simp: dbm_nonneg_def min_def)

lemma dbm_nonneg_abstra[dbm_nonneg]:
  assumes "dbm_nonneg n M"
  shows "dbm_nonneg n (abstra ac M v)"
  using assms by (cases ac) (auto simp: dbm_nonneg_def min_def)

lemma dbm_nonneg_abstr[dbm_nonneg]:
  assumes "dbm_nonneg n M"
  shows "dbm_nonneg n (abstr g M v)"
  using assms(1) unfolding abstr.simps
  by (rule fold_acc_preserv'[where P = "dbm_nonneg n", rotated]) (rule dbm_nonneg_abstra)

lemma dbm_nonneg_up[dbm_nonneg]:
  "dbm_nonneg n (up M)" if "dbm_nonneg n M"
  using that unfolding dbm_nonneg_def up_def by auto

lemma dbm_nonneg_reset[dbm_nonneg]:
  fixes M :: "'t :: time DBM"
  assumes "dbm_nonneg n M" "x > 0"
  shows "dbm_nonneg n (reset M n x 0)"
  using assms unfolding reset_def dbm_nonneg_def by (auto simp: neutral min_def)

lemma dbm_nonneg_reset'[dbm_nonneg]:
  fixes M :: "'t :: time DBM"
  assumes "dbm_nonneg n M" "\<forall>c \<in> set r. v c > 0"
  shows "dbm_nonneg n (reset' M n r v 0)"
  using assms by (induction r) (auto intro: dbm_nonneg_reset)

lemma dbm_nonneg_fw_upd[dbm_nonneg]:
  "dbm_nonneg n (fw_upd M k' i j)" if "dbm_nonneg n M"
  using that unfolding dbm_nonneg_def fw_upd_def upd_def min_def by auto

lemma dbm_nonneg_fwi[dbm_nonneg]:
  "dbm_nonneg n (fwi M n k' i j)" if "dbm_nonneg n M"
  using that by (induction M _ _ _ _ rule: fwi.induct) (auto intro!: dbm_nonneg_fw_upd)

lemma dbm_nonneg_fw[dbm_nonneg]:
  "dbm_nonneg n (fw M n k)" if "dbm_nonneg n M"
  using that by (induction k) (auto intro!: dbm_nonneg_fwi)

lemma dbm_nonneg_FW[dbm_nonneg]:
  "dbm_nonneg n (FW M n)" if "dbm_nonneg n M"
  using that by (rule dbm_nonneg_fw)

definition
  "empty_dbm \<equiv> \<lambda>_ _. Lt 0"

lemma neg_diag_zero_empty_dbmI:
  assumes "M 0 0 < 0"
  shows "[M]\<^bsub>v,n\<^esub> = {}"
  using assms
  unfolding DBM_zone_repr_def DBM_val_bounded_def DBM.neutral DBM.less_eq[symmetric] by auto

lemma empty_dbm_empty_zone:
  "[empty_dbm]\<^bsub>v,n\<^esub> = {}"
  unfolding empty_dbm_def by (rule neg_diag_zero_empty_dbmI) (simp add: DBM.neutral)

lemma canonical_empty_dbm:
  "canonical empty_dbm n"
  unfolding empty_dbm_def by (auto simp: DBM.add)

lemma dbm_int_empty_dbm:
  "dbm_int empty_dbm n"
  unfolding empty_dbm_def by auto

lemma dbm_nonneg_empty_dbm:
  "dbm_nonneg n empty_dbm"
  unfolding dbm_nonneg_def empty_dbm_def DBM.neutral by simp

lemmas [simp] = any_le_inf

lemma DBM_val_boundedD1:
  assumes "u \<turnstile>\<^bsub>v,n\<^esub> M" "v c \<le> n"
  shows "Le (- u c) \<le> M 0 (v c)"
  using assms unfolding dbm_entry_val.simps DBM_val_bounded_def by auto

lemma DBM_val_boundedD2:
  assumes "u \<turnstile>\<^bsub>v,n\<^esub> M" "v c \<le> n"
  shows "Le (u c) \<le> M (v c) 0"
  using assms unfolding dbm_entry_val.simps DBM_val_bounded_def by auto

lemma DBM_val_boundedD3:
  assumes "u \<turnstile>\<^bsub>v,n\<^esub> M" "v c1 \<le> n" "v c2 \<le> n"
  shows "Le (u c1 - u c2) \<le> M (v c1) (v c2)"
  using assms unfolding dbm_entry_val.simps DBM_val_bounded_def by force

lemma dbm_default_And:
  assumes "dbm_default M n" "dbm_default M' n"
  shows "dbm_default (And M M') n"
  using assms by auto

lemma dbm_default_abstra:
  assumes "dbm_default M n" "constraint_pair ac = (x, m)" "v x \<le> n"
  shows "dbm_default (abstra ac M v) n"
  using assms by (cases ac) auto

lemma dbm_default_abstr:
  assumes "dbm_default M n" "\<forall>(x, m)\<in>collect_clock_pairs g. v x \<le> n"
  shows "dbm_default (abstr g M v) n"
  using assms(1) unfolding abstr.simps
proof (rule fold_acc_preserv'[where P = "\<lambda>M. dbm_default M n", rotated], goal_cases)
  case (1 ac acc)
  then obtain x m where "constraint_pair ac = (x, m)"
    by force
  with assms(2) 1 show ?case
    by (intro dbm_default_abstra) (auto simp: collect_clock_pairs_def)
qed

lemma dbm_entry_dense:
  fixes a b :: "'t :: time DBMEntry"
  assumes "a + b \<ge> 0" "b > 0"
  obtains x where "x > 0" "b \<ge> Le x" "Le (-x) \<le> a"
proof -
  consider "a = \<infinity>" | "a \<noteq> \<infinity>" "a + b = 0" | "a \<noteq> \<infinity>" "a + b > 0"
    using assms(1) by force
  then show ?thesis
  proof cases
    case 1
    with assms show ?thesis
    proof (cases b)
      case (Le x)
      with assms(2) 1 show ?thesis
        by (intro that[of x]) (auto simp: DBM.neutral DBM.add)
    next
      case (Lt x2)
      with assms(2) 1 show ?thesis
        using that time_class.dense by (auto simp: DBM.neutral DBM.add)
    next
      case INF
      with 1 assms(2) that show ?thesis
        by (metis add_inf(2) any_le_inf dbm_less_eq_simps(2) neg_less_iff_less sum_gt_neutral_dest)
    qed
  next
    case 2
    then obtain x where "a = Le (-x)" "b = Le x"
      unfolding neutral by (cases a; cases b; simp add: DBM.add eq_neg_iff_add_eq_0)
    with \<open>b > 0\<close> show ?thesis
      by (intro that[of x]; simp add: neutral)
  next
    case 3
    note intro = that
    have 1: "0 < x + y \<Longrightarrow> - y \<le> x" for x y :: 't
      by (metis ab_semigroup_add_class.add.commute add.right_inverse add_le_cancel_left less_imp_le)
    have 2: thesis if "0 < x + y" "0 < y" "a = Le x" "b = Lt y" for x y :: 't
    proof (cases "x > 0")
      case True
      then have "- x \<le> 0"
        by auto
      from \<open>y > 0\<close> dense obtain z where "0 < z" "z < y"
        by auto
      with that \<open>- x \<le> 0\<close> show ?thesis
        using dual_order.trans by (intro intro[of z]; fastforce)
    next
      case False
      from that have "-x < y"
        using 1 minus_less_iff by fastforce
      with dense obtain z where "- x < z" "z < y"
        by auto
      with False that show ?thesis
        by (intro intro[of z]; simp add: less_imp_le minus_less_iff)
          (meson leI less_le_trans neg_less_0_iff_less)
    qed
    have 3: thesis if "a = Le x" "b = \<infinity>" for x :: 't
      by (metis that Le_le_LeI add_inf(2) any_le_inf assms(2) dbm_less_eq_simps(2) diff_0_right
          diff_left_mono diff_less_eq minus_diff_eq sum_gt_neutral_dest' intro uminus_add_conv_diff)
    have 4: thesis if "a = Lt x" "b = \<infinity>" for x :: 't
      by (metis that \<open>0 < a + b\<close> add.inverse_inverse dbm_less_eq_simps(2) dbm_less_simps(2) intro leI
          less_imp_le less_le_trans neg_0_less_iff_less sum_gt_neutral_dest)
    have 5: thesis if "0 < x + y" "0 < y" "a = Lt x" "b = Le y" for x y
      by (metis that Le_le_LtI antisym_conv1 diff_0_right diff_less_eq intro less_irrefl minus_diff_eq)
    have 6: thesis if "0 < y" "a = Lt x" "b = Lt y" for x y
      by (metis that \<open>0 < a + b\<close> add.inverse_inverse dbm_less_eq_simps(2) intro
          leI less_imp_le less_le_trans neg_less_iff_less sum_gt_neutral_dest dense)
    have 7: thesis if "0 < x + y" "0 < y" "a = Le x" "b = Le y" for x y
      using that by (intro intro[of y]) (auto simp: DBM.add intro: 1)
    from \<open>a + b > 0\<close> \<open>b > 0\<close> \<open>a \<noteq> \<infinity>\<close> show thesis
      by (cases a; cases b) (auto simp: DBM.add neutral intro: 2 3 4 5 6 7)
  qed
qed

lemma canonical_diag:
  fixes M :: "'t :: time DBM"
  assumes "canonical M n" "i \<le> n"
  shows "M i i \<ge> Lt 0"
proof (rule ccontr)
  assume "\<not> M i i \<ge> Lt 0"
  then have "M i i < Lt 0"
    by auto
  then have "M i i + M i i < M i i"
    by (cases "M i i") (auto simp: DBM.add)
  with assms show False
    by force
qed

lemma canonical_diag_nonnegI:
  fixes M :: "'t :: time DBM"
  assumes "canonical M n" "\<forall>i \<le> n. M i i \<noteq> Lt 0"
  shows "\<forall>i \<le> n. M i i \<ge> 0"
proof clarify
  fix i assume "i \<le> n"
  then show "M i i \<ge> 0"
    using canonical_diag[OF assms(1) \<open>i \<le> n\<close>] assms(2) by (cases "M i i"; auto simp: DBM.neutral)
qed

context Regions_common
begin

lemma canonical_non_emptyI:
  assumes "[M]\<^bsub>v,n\<^esub> \<noteq> {}"
  shows "canonical (FW M n) n"
  by (simp add: assms fw_shortest non_empty_cyc_free)

definition
  "canonical_dbm M \<equiv> canonical M n \<and> dbm_nonneg n M \<and> dbm_int M n"

abbreviation
  "vabstr' (Z :: ('c, t) zone) M \<equiv> Z = [M]\<^bsub>v,n\<^esub> \<and> canonical_dbm M"

lemma V_structuralI:
  assumes "dbm_nonneg n M"
  shows "[M]\<^bsub>v,n\<^esub> \<subseteq> V"
  using clock_numbering(3) assms unfolding V_def DBM_zone_repr_def
  by (clarsimp simp: neutral) (meson assms clock_numbering(1) dbm_positive dbm_nonneg_def)

lemma canonical_dbm_valid:
  "valid_dbm M" if "canonical_dbm M"
  using that unfolding canonical_dbm_def by (auto dest: V_structuralI)

lemma dbm_nonnegI:
  assumes "canonical M n" "[M]\<^bsub>v,n\<^esub> \<subseteq> V" "\<forall>i \<le> n. M i i \<noteq> Lt 0"
  shows "dbm_nonneg n M"
proof (rule ccontr)
  assume A: "\<not> dbm_nonneg n M"
  from assms(1,3) have diag_nonneg: "\<forall>i \<le> n. M i i \<ge> 0"
    by (rule canonical_diag_nonnegI)
  from A obtain i where "i > 0" "i \<le> n" "M 0 i > 0"
    unfolding dbm_nonneg_def by auto
  moreover have "M i 0 + M 0 i \<ge> 0"
  proof -
    from assms(1) \<open>i \<le> n\<close> have "M i i \<ge> Lt 0"
      by (rule canonical_diag)
    with \<open>i \<le> n\<close> assms(3) have "M i i \<ge> 0"
      by (cases "M i i"; auto simp: neutral)
    also from \<open>canonical M n\<close> \<open>i \<le> n\<close> have "M i 0 + M 0 i \<ge> M i i"
      by auto
    finally show ?thesis .
  qed
  ultimately obtain x where "x > 0" "M 0 i \<ge> Le x" "Le (-x) \<le> M i 0"
    by - (rule dbm_entry_dense)
  moreover from \<open>i > 0\<close> \<open>i \<le> n\<close> obtain c where "c \<in> X" "v c \<le> n" "i = v c"
    using clock_numbering by auto
  moreover from clock_numbering(1) cn_weak assms(1) have "cycle_free M n"
    by (intro non_empty_cycle_free canonical_nonneg_diag_non_empty diag_nonneg) auto
  ultimately obtain u where "u \<in> [M]\<^bsub>v,n\<^esub>" "u c < 0"
    using assms(1)
    by (auto simp: clock_numbering(1) intro: canonical_saturated_1[where M = M and v = v])
  with assms(2) \<open>c \<in> X\<close> show False
    unfolding V_def DBM_zone_repr_def by force
qed

lemma vabstr'_V:
  obtains M where "vabstr' V M"
proof -
  interpret beta_regions: Beta_Regions'
  where k = "k l"
    apply -
    apply unfold_locales
         apply (rule finite)
        apply (simp add: non_empty)
     apply (rule clock_numbering cn_weak not_in_X)+
  done
  have V_eq: "beta_regions.V = V"
    unfolding beta_regions.V_def V_def ..
  let ?M = "beta_regions.V_dbm"
  from beta_regions.V_dbm_eq_V beta_regions.V_dbm_int beta_regions.normalized_V_dbm have *:
    "[?M]\<^bsub>v,n\<^esub> = V" "dbm_int ?M n" "beta_regions.normalized ?M"
    unfolding V_eq by auto
  moreover have "dbm_nonneg n ?M"
    unfolding beta_regions.V_dbm_def dbm_nonneg_def DBM.neutral by simp
  ultimately show ?thesis
    apply -
    apply (rule that[of "FW ?M n"])
    apply (rule conjI)
    subgoal
      using FW_zone_equiv_spec by blast
    unfolding canonical_dbm_def
    apply (intro conjI dbm_nonneg_FW FW_int_preservation canonical_non_emptyI)
      apply (auto simp: V_def)
    done
qed

lemma canonical_dbm_empty_dbm:
  "canonical_dbm empty_dbm"
  unfolding canonical_dbm_def
  by (intro conjI canonical_empty_dbm dbm_int_empty_dbm dbm_nonneg_empty_dbm)

lemma vabstr'_empty_dbm:
  "vabstr' {} empty_dbm"
  by (intro conjI empty_dbm_empty_zone[symmetric] canonical_dbm_empty_dbm)

lemma vabstr'I:
  assumes "dbm_int M' n" "Z' \<subseteq> V" "Z' = [M']\<^bsub>v,n\<^esub>"
  obtains M' where "vabstr' Z' M'"
proof (cases "Z' = {}")
  case True
  then show ?thesis
    by (intro that[of empty_dbm], simp only: vabstr'_empty_dbm)
next
  case False
  with assms obtain M' where *: "Z' = [M']\<^bsub>v,n\<^esub>" "dbm_int M' n" "canonical M' n"
    by (metis FW_canonical' FW_valid_preservation FW_zone_equiv_spec
        dbm_non_empty_diag valid_dbm.simps)
  with assms(2) have "dbm_nonneg n M'"
    by - (rule dbm_nonnegI; smt \<open>Z' \<noteq> {}\<close> dbm_less_eq_simps(2) dbm_non_empty_diag neutral)
  let ?M = "FW M' n"
  from * \<open>dbm_nonneg n M'\<close> show ?thesis
    apply (intro that[of ?M] conjI)
     apply (simp add: FW_zone_equiv_spec[symmetric])
    unfolding canonical_dbm_def
    unfolding dbm_nonneg_def[symmetric]
    apply (intro conjI FW_canonical' dbm_nonneg_FW FW_int_preservation; assumption?)
    subgoal diag_nonneg
      using FW_zone_equiv_spec False dbm_non_empty_diag by blast
    done
qed

end

context Regions_TA
begin

text \<open>The following does not hold:\<close>
lemma
  fixes M :: "real DBM"
  assumes "canonical M n"
      and "\<forall>i \<le> n. M 0 i \<le> 0"
    shows "\<forall>i \<le> n. 0 \<le> M i i"
  oops

lemma global_clock_numbering:
  "global_clock_numbering A v n"
  using clock_numbering(1) clock_numbering_le cn_weak valid_abstraction by blast

sublocale step_z'_bisim_step_z_dbm': Bisimulation
  "\<lambda>(l, Z) (l', Z'). A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>"
  "\<lambda>(l, M) (l', M'). \<exists>a. A \<turnstile>' \<langle>l,M\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',M'\<rangle>"
  "\<lambda>(l, Z) (l', M). l' = l \<and> Z = [M]\<^bsub>v,n\<^esub>"
  apply (standard; clarsimp simp: step_z_dbm'_def step_z'_def)
  subgoal
    using global_clock_numbering by (auto elim!: step_z_dbm_DBM)
  subgoal
    by (blast dest: step_z_dbm_sound[OF _ global_clock_numbering])
  done

lemma step_z_dbm_preserves_int:
  "dbm_int M' n" if "A \<turnstile> \<langle>l,M\<rangle> \<leadsto>\<^bsub>v,n,a\<^esub> \<langle>l',M'\<rangle>" "dbm_int M n"
  apply (rule step_z_dbm_preserves_int; (rule that global_clock_numbering)?)
  using valid_abstraction valid_abstraction_pairsD by fastforce

lemma step_z_dbm'_preserves_int:
  "dbm_int M' n" if "A \<turnstile>' \<langle>l,M\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l',M'\<rangle>" "dbm_int M n"
  using that by cases (erule step_z_dbm_preserves_int)+

lemma step_z'_vabstr':
  "\<exists>M. vabstr' Z' M" if "\<exists>M. vabstr' Z M" "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>"
proof -
  from that obtain M where "vabstr' Z M"
    by auto
  with step_z'_bisim_step_z_dbm'.A_B_step[of "(l, Z)" _ "(l, M)"] that(2) obtain a M' where *:
    "A \<turnstile>' \<langle>l, M\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', M'\<rangle>" "Z' = [M']\<^bsub>v,n\<^esub>"
    by force
  with \<open>vabstr' Z M\<close> have "dbm_int M' n"
    by - (rule step_z_dbm'_preserves_int, auto simp: canonical_dbm_def)
  moreover from *(1) \<open>vabstr' Z M\<close> have "Z' \<subseteq> V"
    by (metis canonical_dbm_valid step_z'_def step_z_V that(2) valid_dbm.simps)
  ultimately obtain M' where "vabstr' Z' M'"
    using \<open>Z' = _\<close> by - (rule vabstr'I)
  then show ?thesis
    by (intro exI)
qed

end


locale TA_Extrapolation =
  Regions_TA where A = A +
  Time_Abstract_Simulation where A = A for A :: "('a, 'c, real, 'l) ta" +
  assumes simulation_nonneg: "u' \<in> V \<Longrightarrow> (l, u) \<preceq> (l', u') \<Longrightarrow> u \<in> V"
  fixes extra :: "'l \<Rightarrow> real DBM \<Rightarrow> real DBM"
  assumes extra_widens: "vabstr' Z M \<Longrightarrow> Z \<subseteq> [extra l M]\<^bsub>v,n\<^esub>"
      and extra_\<alpha>: "vabstr' Z M \<Longrightarrow> [extra l M]\<^bsub>v,n\<^esub> \<subseteq> \<alpha> l Z"
      and extra_finite: "finite {extra l M | M. canonical_dbm M}"
      and extra_int: "dbm_int M n \<Longrightarrow> dbm_int (extra l M) n"
begin

definition apx where
  "apx l Z \<equiv> let M = (SOME M. canonical_dbm M \<and> Z = [M]\<^bsub>v,n\<^esub>) in [extra l M]\<^bsub>v,n\<^esub>"

lemma apx_widens:
  "[M]\<^bsub>v,n\<^esub> \<subseteq> apx l ([M]\<^bsub>v,n\<^esub>)" if "canonical_dbm M"
  by (smt apx_def extra_widens someI_ex that)

lemma apx_abs:
  "apx l ([M]\<^bsub>v,n\<^esub>) \<subseteq> \<alpha> l ([M]\<^bsub>v,n\<^esub>)" if "canonical_dbm M"
  by (smt apx_def extra_\<alpha> someI_ex that)

lemma \<alpha>_V:
  "\<alpha> l Z \<subseteq> V" if "Z \<subseteq> V"
  using that simulation_nonneg unfolding V_def abs_def by auto

lemma apx_V:
  "apx l ([M]\<^bsub>v,n\<^esub>) \<subseteq> V" if "canonical_dbm M"
proof -
  from that have "apx l ([M]\<^bsub>v,n\<^esub>) \<subseteq> \<alpha> l ([M]\<^bsub>v,n\<^esub>)"
    by (rule apx_abs)
  moreover from that have "\<dots> \<subseteq> V"
    unfolding canonical_dbm_def by (intro \<alpha>_V V_structuralI, elim conjE)
  finally show ?thesis .
qed

lemma apx_empty:
  "apx l {} = {}"
proof -
  have "vabstr' {} empty_dbm"
    by (rule vabstr'_empty_dbm)
  from canonical_dbm_empty_dbm have "apx l {} \<subseteq> \<alpha> l {}"
    by (subst empty_dbm_empty_zone[symmetric])+ (rule apx_abs)
  also have "\<dots> = {}"
    unfolding abs_def by auto
  finally show ?thesis
    by simp
qed

lemma apx_ex:
  assumes "canonical_dbm M"
  shows "\<exists>M'. apx l ([M]\<^bsub>v,n\<^esub>) = [extra l M']\<^bsub>v,n\<^esub> \<and> canonical_dbm M'"
  using assms unfolding apx_def by (smt someI_ex)

lemma vabstr'_apx:
  assumes "vabstr' Z M" "Z \<subseteq> V"
  obtains M where "vabstr' (apx l Z) M"
proof (cases "Z = {}")
  case False
  from apx_ex assms obtain M' where *:
    "apx l Z = [extra l M']\<^bsub>v,n\<^esub>" "canonical_dbm M'"
    using apx_ex by blast
  with FW_zone_equiv_spec have "apx l Z = [FW (extra l M') n]\<^bsub>v,n\<^esub>"
    by auto
  moreover from \<open>canonical_dbm M'\<close> have "canonical_dbm (FW (extra l M') n)"
  proof -
    from assms have "Z \<subseteq> apx l Z"
      by (auto intro!: apx_widens)
    with \<open>Z \<noteq> {}\<close> have "apx l Z \<noteq> {}"
      by auto
    then have "canonical (FW (extra l M') n) n"
      unfolding * by (rule canonical_non_emptyI)
    moreover have "dbm_nonneg n (FW (extra l M') n)"
      using \<open>apx l Z = [FW (extra l M') n]\<^bsub>v,n\<^esub>\<close> \<open>apx l Z \<noteq> {}\<close> \<open>canonical (FW _ _) _\<close>
      apply (intro dbm_nonnegI)
      apply assumption
      subgoal
        using apx_V assms(1) by blast
      subgoal
        by (metis DBMEntry.distinct(1) Le_less_Lt  antisym_conv dbm_non_empty_diag leI neutral)
      done
    moreover have "dbm_int (FW (extra l M') n) n"
      using *(2) unfolding canonical_dbm_def by (intro FW_int_preservation extra_int, elim conjE)
    ultimately show ?thesis
      unfolding canonical_dbm_def by (intro conjI)
  qed
  ultimately show ?thesis
    by (auto intro: that)
next
  case True
  then show ?thesis
    by (intro that[of empty_dbm])(auto simp: empty_dbm_empty_zone apx_empty canonical_dbm_empty_dbm)
qed

lemma apx_finite:
  "finite {apx l Z |l Z. \<exists>M. vabstr' Z M \<and> l \<in> state_set A}" (is "finite ?S")
proof -
  { fix l assume "l \<in> state_set A"
    from extra_finite have "finite {[extra l M]\<^bsub>v,n\<^esub> | M. canonical_dbm M}"
    proof -
      have "{[extra l M]\<^bsub>v,n\<^esub> | M. canonical_dbm M}
        = (\<lambda>M. [M]\<^bsub>v,n\<^esub>) ` {extra l M | M. canonical_dbm M}"
        by auto
      with extra_finite show ?thesis
        by simp
    qed
    also from apx_ex have "{apx l Z |Z. \<exists>M. vabstr' Z M} \<subseteq> \<dots>"
      by auto
    finally (finite_subset[rotated]) have "finite {apx l Z |Z. \<exists>M. vabstr' Z M}" .
  } note * = this
  have "?S = (\<Union> l \<in> state_set A. {apx l Z |Z. \<exists>M. vabstr' Z M})"
    by auto
  also have "finite \<dots>"
    using * finite_state_set by auto
  finally show ?thesis .
qed

sublocale Time_Abstract_Simulation_Sandwich
  where \<beta> = apx and
  I = "\<lambda>Z. \<exists>M. vabstr' Z M"
  proof standard
  show "u \<in> V" if "(l, u) \<preceq> (l', u')" "u' \<in> V" for l l' :: 'l and u u' :: "'c \<Rightarrow> real"
    using that by (rule simulation_nonneg[rotated])
  show "\<exists>M. vabstr' Z' M"
    if "\<exists>M. vabstr' Z M" and "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto> \<langle>l', Z'\<rangle>" for Z Z' :: "('c \<Rightarrow> real) set" and l l' :: 'l
    using that by (rule step_z'_vabstr')
  show "apx l Z \<subseteq> \<alpha> l Z"
    if "\<exists>M. vabstr' Z M" "Z \<subseteq> V" for Z :: "('c \<Rightarrow> real) set" and l :: 'l
    using that apx_abs by auto
  show "Z \<subseteq> apx l Z" if "\<exists>M. vabstr' Z M" "Z \<subseteq> V" for Z :: "('c \<Rightarrow> real) set" and l :: 'l
    using that apx_widens by auto
  show "\<exists>M. vabstr' (apx l Z) M"
    if "\<exists>M. vabstr' Z M" "Z \<subseteq> V" for Z :: "('c \<Rightarrow> real) set" and l :: 'l
    using that by (elim exE) (rule vabstr'_apx, auto)
  show "finite {apx l Z |l Z. (\<exists>M. vabstr' Z M) \<and> Z \<subseteq> V \<and> l \<in> state_set A}"
    using apx_finite by (rule finite_subset[rotated]) auto
  show "l\<^sub>0 \<in> state_set A"
    sorry
  show "\<forall>u\<in>Z\<^sub>0. u \<in> V"
    sorry
  show "\<exists>M. vabstr' Z\<^sub>0 M"
    sorry
qed


end


end