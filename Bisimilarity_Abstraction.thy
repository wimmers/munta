theory Bisimilarity_Abstraction
  imports Timed_Automata Closure
begin

inductive ta_bisim where
  "ta_bisim A R" if
    "\<And> l u l' u'. R (l, u) (l', u') \<Longrightarrow> l = l'"
    "\<And> l1 u1 l2 u2 d l1' u1'. R (l1, u1) (l2, u2) \<Longrightarrow> A \<turnstile> \<langle>l1, u1\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l1', u1'\<rangle>
    \<Longrightarrow> \<exists> d' l2' u2'. A \<turnstile> \<langle>l2, u2\<rangle> \<rightarrow>\<^bsup>d'\<^esup> \<langle>l2', u2'\<rangle> \<and> R (l1', u1') (l2', u2')"
    "\<And> l1 u1 l2 u2 a l1' u1'. R (l1, u1) (l2, u2) \<Longrightarrow> A \<turnstile> \<langle>l1, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l1', u1'\<rangle>
    \<Longrightarrow> \<exists> l2' u2'. A \<turnstile> \<langle>l2, u2\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l2', u2'\<rangle> \<and> R (l1', u1') (l2', u2')"
    "\<And> l u. R (l, u) (l, u)"
    "\<And> l1 u1 l2 u2. R (l1, u1) (l2, u2) \<Longrightarrow> R (l2, u2) (l1, u1)"
    "\<And> l1 u1 l2 u2 l3 u3. R (l1, u1) (l2, u2) \<Longrightarrow> R (l2, u2) (l3, u3) \<Longrightarrow> R (l1, u1) (l3, u3)"

context
  fixes A :: "('a, 'c, 't :: time, 's) ta"
  fixes R :: "('s * ('c, ('t::time)) cval) \<Rightarrow> ('s * ('c, 't) cval) \<Rightarrow> bool"
  assumes bisim: "ta_bisim A R"
begin

lemma
    locs:
    "R (l, u) (l', u') \<Longrightarrow> l = l'"
    and delay:
    "R (l1, u1) (l2, u2) \<Longrightarrow> A \<turnstile> \<langle>l1, u1\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l1', u1'\<rangle>
    \<Longrightarrow> \<exists> d' l2' u2'. A \<turnstile> \<langle>l2, u2\<rangle> \<rightarrow>\<^bsup>d'\<^esup> \<langle>l2', u2'\<rangle> \<and> R (l1', u1') (l2', u2')"
    and action:
    "R (l1, u1) (l2, u2) \<Longrightarrow> A \<turnstile> \<langle>l1, u1\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l1', u1'\<rangle>
    \<Longrightarrow> \<exists> l2' u2'. A \<turnstile> \<langle>l2, u2\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l2', u2'\<rangle> \<and> R (l1', u1') (l2', u2')"
    and refl:
    "R (l, u) (l, u)"
    and sym:
    "R (l1, u1) (l2, u2) \<Longrightarrow> R (l2, u2) (l1, u1)"
    and trans:
    "R (l1, u1) (l2, u2) \<Longrightarrow> R (l2, u2) (l3, u3) \<Longrightarrow> R (l1, u1) (l3, u3)"
  using bisim by (cases; metis)+

definition "Cl l Z = {u. \<exists> u' \<in> Z. R (l, u) (l, u')}"

(*
inductive step_z_cl ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> 'a action \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^bsub>\<equiv>,_\<^esub> \<langle>_, _\<rangle>" [61,61,61] 61)
where
  step_alpha: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^bsub>\<equiv>,a\<^esub> \<langle>l', Cl l' Z\<rangle>"
*)

inductive cl_steps ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  cl_refl: "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l, Z\<rangle>" (* if "Cl l Z = Z" *) |
  cl_step: "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Z'\<rangle> \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l'', Z''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l''', Z'''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l''', Cl l''' Z'''\<rangle>"

lemmas [intro] = cl_steps.intros

  (*
inductive cl_steps ::
  "('a, 'c, 't, 's) ta \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> 's \<Rightarrow> ('c, 't) zone \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>_, _\<rangle>" [61,61,61] 61)
where
  cl_refl: "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l, Z\<rangle>" if "Cl l Z = Z" |
  cl_step: "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l'', Z''\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l''', Z'''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l''', Cl l''' Z'''\<rangle>" if "Cl l Z = Z"
*)

lemma Cl_idempotent:
  "Cl l (Cl l Z) = Cl l Z"
  unfolding Cl_def using sym trans refl by blast

(*
lemma cl_steps_cl:
  assumes "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Z'\<rangle>"
  obtains Z'' where "Z' = Cl l' Z''"
    apply atomize_elim
  using assms by (cases; blast)
*)

(* XXX Move *)
lemma step_z_sound':
  assumes "A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l'', Z''\<rangle>" "A \<turnstile> \<langle>l'', Z''\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l''', Z'''\<rangle>" "u' \<in> Z'''"
  shows "\<exists> u. A \<turnstile>' \<langle>l', u\<rangle> \<rightarrow> \<langle>l''', u'\<rangle> \<and> u \<in> Z'"
  using assms by (auto 4 6 simp: zone_delay_def zone_set_def intro: step_a.intros)

lemma steps'_altI:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow> \<langle>l'', u''\<rangle> \<Longrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>"
  by (induction rule: steps'.induct; blast)

    (*
lemma
  assumes "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Z'\<rangle>" "u' \<in> Z'"
    shows "\<exists> u. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> u \<in> Z"
  using assms
proof (induction arbitrary: u')
  case (cl_refl l Z)
  then show ?case by auto
next
  case (cl_step l Z l' Z' a l'' Z'' l''' Z''')
  from \<open>u' \<in> Cl l''' Z'''\<close> obtain u'' where "u'' \<in> Z'''" "R (l''', u') (l''', u'')"
    unfolding Cl_def by auto
  with cl_step[] thm steps_z_sound

      oops
  with cl_step obtain u''' where u''':
    "A \<turnstile>' \<langle>l', u'''\<rangle> \<rightarrow> \<langle>l''', u''\<rangle>" "u''' \<in> Z'"
    by atomize_elim (drule step_z_sound'; assumption)
  from cl_step(4)[OF this(2)] obtain u where
    "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'''\<rangle>" "u \<in> Z"
    by blast
  with u'''(1) show ?case
    apply -
    apply (drule steps'_altI, assumption)

    using steps'_altI
  with step_z_sound cl_step obtain u''' where
    "u''' \<in> Z'" "A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow> \<langle>l''', u''\<rangle>"

  then show ?case sorry
qed
  *)

lemma step:
  "\<exists> l2' u2'. A \<turnstile>' \<langle>l2, u2\<rangle> \<rightarrow> \<langle>l2', u2'\<rangle> \<and> R (l1', u1') (l2', u2')"
  if "A \<turnstile>' \<langle>l1, u1\<rangle> \<rightarrow> \<langle>l1', u1'\<rangle>" "R (l1, u1) (l2, u2)"
  using that(1) by (force dest!: delay[OF that(2)] dest: action)

lemma cl_steps_sound:
  assumes "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Z'\<rangle>" "u' \<in> Z'"
    shows "\<exists> u u''. A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u''\<rangle> \<and> u \<in> Z \<and> u'' \<in> Z' \<and> R (l', u') (l', u'')"
  using assms
proof (induction arbitrary: u')
  case prems: (cl_refl l Z)
  with refl show ?case by auto
next
  case (cl_step l Z l' Z' l'' Z'' a l''' Z''')
  from \<open>u' \<in> Cl l''' Z'''\<close> obtain u'' where u'': "u'' \<in> Z'''" "R (l''', u') (l''', u'')"
    unfolding Cl_def by auto
  with cl_step obtain u3 where u3:
    "A \<turnstile>' \<langle>l', u3\<rangle> \<rightarrow> \<langle>l''', u''\<rangle>" "u3 \<in> Z'"
    by atomize_elim (drule step_z_sound'; assumption)
  from cl_step(4)[OF this(2)] obtain u u4 where u4:
    "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u4\<rangle>" "u \<in> Z" "u4 \<in> Z'" "R (l', u3) (l', u4)"
    by blast
  from step[OF u3(1) u4(4)] obtain l2 u2 where l2:
    "A \<turnstile>' \<langle>l', u4\<rangle> \<rightarrow> \<langle>l2, u2\<rangle>" "R (l''', u'') (l2, u2)"
    by blast
  with locs[OF l2(2)] \<open>u'' \<in> Z'''\<close> have "u2 \<in> local.Cl l2 Z'''"
    unfolding Cl_def by (auto intro: sym)
  from l2(2) u''(2) locs[OF l2(2)] have "R (l2, u') (l2, u2)"
    by (auto intro: trans)
  with l2 u4(1) \<open>u \<in> Z\<close> locs[OF l2(2)] \<open>u'' \<in> Z'''\<close> \<open>u2 \<in> _\<close> show ?case
    by - (drule steps'_altI; auto)
qed

lemma step_z_complete':
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l'', u'\<rangle> \<Longrightarrow> u \<in> Z
  \<Longrightarrow> \<exists> l' Z' Z'' a. A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle> \<and> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle> \<and> u' \<in> Z''"
  by (auto 4 7 simp: zone_delay_def zone_set_def elim!: step_a.cases step'.cases)

lemma
  "A \<turnstile> \<langle>l, Cl l Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Cl l' Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>a\<^esub> \<langle>l', Z'\<rangle>"
  oops

lemma
  "\<exists> W'. A \<turnstile> \<langle>l, W\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', W'\<rangle> \<and> Z' \<subseteq> W'" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle>" "Z \<subseteq> W"
  using that
  apply (induction A \<equiv> A _ _ _ _ arbitrary: W)
    oops

lemma
  "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Cl l' Z'\<rangle>" if "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>* \<langle>l', Z'\<rangle>"
  using that
  apply (induction A \<equiv> A _ _ _ _)
    oops

lemma Cl_subset:
  "Z \<subseteq> Cl l Z"
  unfolding Cl_def using refl by auto

lemma Cl_mono:
  "Cl l Z \<subseteq> Cl l W" if "Z \<subseteq> W"
  using that unfolding Cl_def by blast

lemma cl_steps_cl:
  "\<exists> W'. A \<turnstile> \<langle>l, Cl l Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', W'\<rangle> \<and> Z' \<subseteq> W'" if "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Z'\<rangle>"
  using that
  proof (induction A \<equiv> A _ _ _ _)
    case (cl_refl l Z)
    with Cl_subset show ?case by blast
  next
    case (cl_step l Z l' Z' l'' Z'' a l''' Z''')
    then obtain W' where
      "A \<turnstile> \<langle>l, Cl l Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', W'\<rangle>" "Z' \<subseteq> W'"
      by auto
    moreover from step_z_mono[OF cl_step(3) this(2)] obtain W'' where
      "A \<turnstile> \<langle>l', W'\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l'', W''\<rangle>" "Z'' \<subseteq> W''"
      by auto
    moreover from step_z_mono[OF cl_step(4) this(2)] obtain W''' where
      "A \<turnstile> \<langle>l'', W''\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l''', W'''\<rangle>" "Z''' \<subseteq> W'''"
      by auto
    ultimately show ?case by (blast dest: Cl_mono)
  qed

lemma cl_step_altI:
  "A \<turnstile> \<langle>l'', Cl l'' Z''\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l''', Z'''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l', Z'\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l', Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l'', Z''\<rangle>
  \<Longrightarrow> A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l''', Z'''\<rangle>"
  by (induction "Cl l'' Z''" _ _ rule: cl_steps.induct; blast)

lemma cl_steps_complete:
  assumes "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" "u \<in> Z"
  shows "\<exists> Z'. A \<turnstile> \<langle>l, Cl l Z\<rangle> \<rightarrow>\<^sub>\<equiv>\<^sup>* \<langle>l', Z'\<rangle> \<and> u' \<in> Z'"
  using assms
proof (induction A \<equiv> A _ _ _ _ arbitrary: Z)
  case (refl' l u)
  with Cl_subset show ?case by blast
next
  case prems: (step' l u l' u' l'' u'')
  from step_z_complete'[OF prems(1,4)] obtain l1 Z' Z'' a where
    "A \<turnstile> \<langle>l, Z\<rangle> \<leadsto>\<^bsub>\<tau>\<^esub> \<langle>l1, Z'\<rangle>" "A \<turnstile> \<langle>l1, Z'\<rangle> \<leadsto>\<^bsub>\<upharpoonleft>a\<^esub> \<langle>l', Z''\<rangle>" "u' \<in> Z''"
    by blast
  with prems(3)[OF this(3)] show ?case by (blast dest: cl_steps_cl cl_step_altI)
qed

end

context
  fixes A :: "('a, 'c, 't :: time, 's) ta"
  fixes k :: "'s \<Rightarrow> 'c \<Rightarrow> 't"
  assumes inv_ceiling:
    "\<And> l c m. (c, m) \<in> collect_clock_pairs (inv_of A l) \<Longrightarrow> k l c \<ge> m"
  and guard_ceiling:
    "\<And> l c m g a r l'. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> (c, m) \<in> collect_clock_pairs g \<Longrightarrow> k l c \<ge> m"
  and active:
    "\<And> l c g a r l'. A \<turnstile> l \<longrightarrow>\<^bsup>g,a,r\<^esup> l' \<Longrightarrow> c \<notin> set r \<Longrightarrow> k l c \<ge> k l' c"
begin

definition
  "Cl_loc \<equiv> \<lambda> (l, u) (l', u'). l = l' \<and> (\<forall> c. u c = u' c \<or> (u c > k l c \<and> u' c > k l c))"

lemma Cl_loc_delay:
  "Cl_loc (l, u \<oplus> d) (l', u' \<oplus> d)" if "Cl_loc (l, u) (l', u')" "d \<ge> 0"
  using that unfolding Cl_loc_def
  by (auto simp: cval_add_def) (metis add.commute add_strict_increasing2)+

lemma ac_cong:
  "u' \<turnstile>\<^sub>a ac" if
  "u \<turnstile>\<^sub>a ac" "ac \<in> set g" "Cl_loc (l, u) (l', u')" "\<forall> (c, m) \<in> collect_clock_pairs g. k l c \<ge> m"
proof -
  let ?c = "fst (constraint_pair ac)"
  let ?d = "snd (constraint_pair ac)"
  from that(2,4) have "k l ?c \<ge> ?d" unfolding collect_clock_pairs_def by auto
  show ?thesis
  proof (cases "u ?c = u' ?c")
    case True
    with that(1) show ?thesis by cases auto
  next
    case False
    with that(1,3) \<open>k l ?c \<ge> ?d\<close> show ?thesis unfolding Cl_loc_def by cases (auto 4 3)
  qed
qed

lemma Cl_loc_reset:
  "Cl_loc (l1', [r\<rightarrow>0]u) (l1', [r\<rightarrow>0]u')" if
  "Cl_loc (l1, u) (l2, u')" "\<forall> c. c \<notin> set r \<longrightarrow> k l1 c \<ge> k l1' c"
  using that unfolding Cl_loc_def
  apply safe
  subgoal for c
    by (cases "c \<in> set r"; force)
  subgoal for c
    by (cases "c \<in> set r"; force)
  done

lemma cc_cong:
  "u' \<turnstile> g" if "u \<turnstile> g" "Cl_loc (l, u) (l', u')" "\<forall> (c, m) \<in> collect_clock_pairs g. k l c \<ge> m"
  using that by (auto 4 4 intro: ac_cong simp: list_all_iff)

(* XXX How to make this simp rule work? *)
lemma Cl_loc_id[simp]:
  "l' = l" if "Cl_loc (l, u) (l', u')"
  using that unfolding Cl_loc_def by auto

lemma Cl_loc_ta_bisim:
  "ta_bisim A Cl_loc"
  apply rule
  subgoal
    unfolding Cl_loc_def by auto
  subgoal
    apply (erule step_t.cases)
    apply simp
    apply (drule Cl_loc_delay, assumption)
    apply (drule cc_cong, assumption)
    using inv_ceiling Cl_loc_id by blast+
  subgoal
    apply (erule step_a.cases)
    subgoal for A l g a' r l' u u'
      apply simp
      apply (drule cc_cong, assumption)
      using guard_ceiling apply force
      apply (subst Cl_loc_id, assumption)
      apply (drule Cl_loc_reset[where r = r and l1' = l'])
      using active apply force
      apply (drule cc_cong, assumption)
      using inv_ceiling apply force
      by (assumption | rule)+
    done
  subgoal
    unfolding Cl_loc_def by auto
  subgoal
    unfolding Cl_loc_def by force
  subgoal
    unfolding Cl_loc_def by (auto; metis)
  done

end

end
