theory TA_Simulation
  imports "TA.Timed_Automata" "TA.Simulation_Graphs_TA" "HOL-Eisbach.Eisbach"
begin

no_notation dbm_le ("_ \<preceq> _" [51, 51] 50)

lemma step_trans_z'_sound:
  "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle> \<Longrightarrow> \<forall>u' \<in> Z'. \<exists>u \<in> Z. \<exists>d.  A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l',u'\<rangle>"
  by (fastforce dest!: step_trans_a_z_sound step_trans_t_z_sound elim!: step_trans_z'.cases)

lemma step_trans_z'_exact_strong:
  assumes "A \<turnstile>' \<langle>l, Z\<rangle> \<leadsto>\<^bsup>t\<^esup> \<langle>l', Z'\<rangle>"
  shows "Z' = {u'. \<exists>u \<in> Z. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l', u'\<rangle>}"
  using step_trans_z'_sound assms by (auto dest: step_trans_z'_exact step_trans_z'_sound)

locale Time_Abstract_Simulation =
  fixes A :: "('a, 'c, 't :: time, 'l) ta"
  fixes sim :: "'l \<times> ('c \<Rightarrow> 't :: time) \<Rightarrow> 'l \<times> ('c \<Rightarrow> 't) \<Rightarrow> bool" (infix "\<preceq>" 60)
  assumes sim:
  "\<And>l l' l\<^sub>1 u u' u\<^sub>1 t. (l, u) \<preceq> (l', u') \<Longrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1\<rangle>
    \<Longrightarrow> \<exists>u\<^sub>1'. A \<turnstile>' \<langle>l, u'\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1'\<rangle> \<and> (l\<^sub>1, u\<^sub>1) \<preceq> (l\<^sub>1, u\<^sub>1')"
  assumes refl: "\<And>u. u \<preceq> u" and trans: "\<And>u v w. u \<preceq> v \<Longrightarrow> v \<preceq> w \<Longrightarrow> u \<preceq> w"
begin

lemma simE:
  assumes "(l, u) \<preceq> (l', u')" "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1\<rangle>"
  obtains u\<^sub>1' where "A \<turnstile>' \<langle>l, u'\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, u\<^sub>1'\<rangle>" "(l\<^sub>1, u\<^sub>1) \<preceq> (l\<^sub>1, u\<^sub>1')"
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
    with \<open>Z\<^sub>1 = _\<close> obtain v\<^sub>0 where "v\<^sub>0 \<in> Z" and step: "A \<turnstile>' \<langle>l, v\<^sub>0\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, v\<rangle>"
      by auto
    from \<open>v\<^sub>0 \<in> Z\<close> \<open>\<alpha> l Z \<subseteq> _\<close> obtain v\<^sub>1 where "v\<^sub>1 \<in> Z'" "(l, v\<^sub>0) \<preceq> (l, v\<^sub>1)"
      unfolding abs_def using refl[of "(l, v\<^sub>0)"] by auto
    from simE[OF \<open>(l, v\<^sub>0) \<preceq> (l, v\<^sub>1)\<close> step] obtain v' where
      "A \<turnstile>' \<langle>l, v\<^sub>1\<rangle> \<rightarrow>\<^bsup>t\<^esup> \<langle>l\<^sub>1, v'\<rangle>" "(l\<^sub>1, v) \<preceq> (l\<^sub>1, v')" .
    with \<open>v\<^sub>1 \<in> Z'\<close> \<open>Z\<^sub>1' = _\<close> have "v' \<in> Z\<^sub>1'"
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

\<^cancel>\<open>interpretation bisim: Bisimulation where
  A = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" and
  B = "\<lambda>(l, Z) (l', Z'). \<exists>a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<alpha>(a)\<^esub> \<langle>l', Z'\<rangle> \<and> Z' \<noteq> {}" and
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
  apply clarsimp
  subgoal premises prems for l u l'' a Z l' Z' Z''
  proof -
    thm prems
    from \<open>u \<in> _\<close> obtain v where "(l, u) \<preceq> (l, v)" "v \<in> Z"
      unfolding abs_def by auto
    from \<open>_ \<noteq> {}\<close> obtain v'' where "v'' \<in> Z''"
      sorry
    with prems obtain v' where "A \<turnstile> \<langle>l', v'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l'', v''\<rangle>" "v' \<in> Z'"
      by (force dest!: step_a_z_sound)
    moreover from \<open>v' \<in> Z'\<close> prems obtain d v1 where "A \<turnstile> \<langle>l, v1\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l', v'\<rangle>" "v1 \<in> Z"
      by (force dest: step_t_z_sound)
    ultimately have "A \<turnstile>' \<langle>l, v1\<rangle> \<rightarrow> \<langle>l'', v''\<rangle>"
      by auto
    moreover from \<open>(l, u) \<preceq> (l, v)\<close> \<open>v \<in> Z\<close> \<open>v1 \<in> Z\<close> have "(l, v1) \<preceq> (l, u)"
      sorry
    ultimately obtain u'' where" A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l'', u''\<rangle>" "(l'', v'') \<preceq> (l'', u'')"
      using sim[of l v1 l u] sorry
    moreover have "u'' \<in> \<alpha> l'' Z''"
      using \<open>(l'', v'') \<preceq> (l'', u'')\<close> \<open>v'' \<in> _\<close> unfolding abs_def apply auto
      sorry
    ultimately show ?thesis
      sorry
  qed
  done\<close>

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

interpretation sim: Invariant_Simulation where
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

lemma
  assumes
    "\<forall>l\<in>L. \<forall>s\<in>M l. \<forall>l' s'. E (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M l'. SE (l', s') (l', \<alpha> l' s''))"
  shows
    "\<forall>l\<in>L. \<forall>s\<in>M' l. \<forall>l' s'. E' (l, s) (l', s') \<longrightarrow> l' \<in> L \<and> (\<exists>s''\<in>M' l'. SE' (l', s') (l', s''))"
  apply safe
  subgoal
    using assms
    unfolding M'_def
    apply (auto elim!: E'.cases)
    using simulation by metis
  unfolding M'_def
proof (erule E'.cases , clarsimp)
  fix l :: 'l
      and s :: 's
      and l' :: 'l
      and s' :: 's
      and x :: 's
  assume "l \<in> L"
      and "E (l, s) (l', s')"
      and "\<alpha> l s = \<alpha> l x"
      and "x \<in> M l"
  with simulation obtain x' where "\<alpha> l' s' = \<alpha> l' x'" "E (l, x) (l', x')"
    by force
  with \<open>l \<in> L\<close> \<open>x \<in> M l\<close> assms obtain x'' where "x'' \<in> M l'" "SE (l', x') (l', \<alpha> l' x'')"
    by force
  from this(2) have "SE' (l', \<alpha> l' x') (l', \<alpha> l' x'')"
    by (rule SE_SE')
  with \<open>x'' \<in> _\<close> \<open>\<alpha> l' s' = _\<close> show "\<exists>s''\<in>M l'. SE' (l', \<alpha> l' s') (l', \<alpha> l' s'')"
    by auto
qed
\<^cancel>\<open>
  apply clarsimp
  apply (erule (1) simulationE)
  using assms(1)
  by (fastforce intro: SE_\<alpha>)\<close>


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

lemma "\<And>l s l1 s1 l2 s2.
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

end

end