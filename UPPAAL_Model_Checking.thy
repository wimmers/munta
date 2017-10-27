theory UPPAAL_Model_Checking
  imports
    UPPAAL_State_Networks_Impl_Refine
    "~~/src/HOL/Library/BNF_Corec"
    TA_More
begin

hide_const models

(* XXX To be moved to UPPAAL_State_Networks.thy *)
inductive step_u' ::
  "('a, 't :: time, 's) unta \<Rightarrow> nat \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval
  \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sup>_ \<langle>_, _, _\<rangle> \<rightarrow> \<langle>_, _, _\<rangle>" [61,61,61,61,61,61] 61) where
  "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>" if
  "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>" "a \<noteq> Del" "A \<turnstile>\<^sub>n \<langle>L', s', u'\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L'', s'', u''\<rangle>"

inductive steps_un' ::
  "('a, 't :: time, 's) unta \<Rightarrow> nat \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval
  \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sup>_ \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61,61,61,61,61,61] 61)
where
  refl: "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L, s, u\<rangle>" |
  step: "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<Longrightarrow> A \<turnstile>\<^sup>n \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>
        \<Longrightarrow> A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"

declare steps_un'.intros[intro]

lemma stepI2:
  "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>" if
  "A \<turnstile>\<^sup>n \<langle>L', s', u'\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>" "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  using that by induction auto

context Equiv_TA
begin

lemma prod_correct'_action:
  "(\<exists> a. defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>) =
   (\<exists> a. state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle> \<and> a \<noteq> Del)"
  apply standard    
  subgoal
    by (blast elim: prod.prod_sound'_action)
   apply clarify
   subgoal for a
     apply (cases a; simp; erule prod.prod_complete_silent prod.prod_complete_sync, fast)
     done
  done

lemma prod_correct'_delay:
  "(\<exists> d. defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>(L', s'), u'\<rangle>) =
   state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  by (blast dest: prod.prod_sound'_delay elim: prod.prod_complete_delay)

lemma equiv_correct:
  "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle> = A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
  by (blast intro!: equiv_sound equiv_complete)

lemma prod_correct_action:
  "(\<exists> a. defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>) =
   (\<exists> a. A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle> \<and> a \<noteq> State_Networks.label.Del)"
  unfolding prod_correct'_action equiv_correct ..

lemma prod_correct_delay:
  "(\<exists> d. defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>(L', s'), u'\<rangle>) =
  A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  unfolding prod_correct'_delay equiv_correct ..

lemma prod_correct:
  "defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle> =
  (\<exists> a. A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>)"
  apply standard
  subgoal
    using prod_correct_action[of u L' s' u'] prod_correct_delay[of u L' s' u']
      Timed_Automata.step.cases by metis
  subgoal
    apply clarify
    subgoal for a
      apply (cases a)
      using prod_correct_action[of u L' s' u'] prod_correct_delay[of u L' s' u']
        Timed_Automata.step.intros apply metis+
      done
    done
  done

context
  assumes "0 < p"
begin

lemmas equiv_complete'' = equiv_complete''[OF _ \<open>0 < p\<close>]

definition
  "all_prop L' s' \<equiv>
    (\<forall>q<p. \<exists>pc st s'' rs pcs.
      exec PF n ((I ! q) (L' ! q), [], s', True, []) [] =
      Some ((pc, st, s'', True, rs), pcs)
    ) \<and> bounded B s' \<and> L' \<in> defs.states' s' (* \<and> (\<forall>q<p. (defs.P ! q) (L' ! q) s') *)
  "

lemma step_u_inv:
  "all_prop L' s'" if "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
  using equiv_complete''[OF that] equiv_complete'[OF that] unfolding all_prop_def by auto

lemma step_inv:
  "all_prop L' s'" if "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
  using step_u_inv[OF equiv_sound[OF that]] .

lemma Equiv_TA_I:
  "Equiv_TA A n L' s'" if *[unfolded all_prop_def]: "all_prop L' s'"
  using * by - (standard, auto intro!: pred_time_indep upd_time_indep clock_conj Len)

lemma step_u'_inv:
  "all_prop L'' s'' \<and> defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L'', s''), u''\<rangle>"
  if "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>"
using that proof cases
  case prems: (1 L' s' u')
  from step_u_inv[OF prems(1)] have *[unfolded all_prop_def]: "all_prop L' s'" .
  interpret equiv: Equiv_TA A n L' s'
    using Equiv_TA_I[OF step_u_inv[OF prems(1)]] .
  from equiv.step_u_inv[OF \<open>0 < p\<close> prems(3)] show ?thesis
    using prems prod_correct_delay[of u L' s' u'] equiv.prod_correct_action[of u' L'' s'' u'']
      Timed_Automata.step'.intros
    by metis
qed

lemma step'_inv:
  "all_prop L'' s'' \<and> A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>"
  if "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L'', s''), u''\<rangle>"
using that proof cases
  case prems: (step' d l' u' a)
  obtain L' s' where "l' = (L', s')"
    by force
  from step_inv prod_correct'_delay prems(1) have *:
    "all_prop L' s'"
    unfolding \<open>l' = _\<close> by fast
  interpret equiv: Equiv_TA A n L' s'
    by (rule Equiv_TA_I[OF *])
  from equiv.step_inv[OF \<open>0 < p\<close>] equiv.prod_correct'_action prems(2)[unfolded \<open>l' = _\<close>] have
    "all_prop L'' s''"
    by metis
  then show ?thesis
    using prems prod_correct_delay[of u L' s' u'] equiv.prod_correct_action[of u' L'' s'' u'']
      step_u'.intros
    unfolding \<open>l' = _\<close> by metis
qed

lemma prod_correct_step':
  "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle> =
  A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  using step'_inv step_u'_inv by blast

lemma all_prop_start:
  "all_prop L s"
  using Equiv_TA_axioms unfolding Equiv_TA_def all_prop_def by auto

lemma steps_u'_inv:
  "all_prop L'' s'' \<and> defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L'', s''), u''\<rangle>"
  if "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"
  using that
    thm steps_un'.induct
proof (induction A \<equiv> A n \<equiv> n L \<equiv> L s \<equiv> s u L'' s'' u'')
  case (refl u)
  show ?case using all_prop_start by auto
next
  case (step u L' s' u' L'' s'' u'')
  then interpret equiv: Equiv_TA A n L' s'
    by (blast intro: Equiv_TA_I)
  from equiv.step_u'_inv[OF \<open>0 < p\<close> step.hyps(3)] step.hyps(1-2) show ?case
    by (blast intro: steps'_altI)
qed

lemma steps'_inv:
  "all_prop L'' s'' \<and> A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"
  if "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L'', s''), u''\<rangle>"
  using that all_prop_start
proof (induction defs.prod_ta "(L, s)" u "(L'', s'')" u'' arbitrary: L s)
  case (refl' u)
  then show ?case using all_prop_start by auto
next
  case (step' u l' u' u'' L s)
  obtain L' s' where "l' = (L', s')" by force
  from step' interpret equiv: Equiv_TA A n L s
    by (blast intro: Equiv_TA_I)
  from equiv.step'_inv[OF \<open>0 < p\<close> step'(1)[unfolded \<open>l' = _\<close>]] step'(3)[OF \<open>l' = _\<close>] show ?case
    by (auto intro: stepI2)
qed

lemma steps_un'_complete:
  "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L'', s''), u''\<rangle>"
  if "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"
  using steps_u'_inv[OF that] ..

lemma steps'_sound:
  "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"
  if "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L'', s''), u''\<rangle>"
  using steps'_inv[OF that] ..

lemma prod_reachable_correct:
  "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<longleftrightarrow> A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>"
  using steps'_sound steps_un'_complete by fast

lemma Bisimulation_Invariant_I:
  "Bisimulation_Invariant
  (\<lambda> (L, s, u) (L', s', u'). defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)
  (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
  (op =)
  (\<lambda> (L, s, u). all_prop L s)
  (\<lambda> (L, s, u). all_prop L s)"
  proof ((standard; clarsimp), goal_cases)
    case prems: (1 L' s' u' L s u)
    then interpret equiv: Equiv_TA A n L s
      by - (rule Equiv_TA_I)
    from prems(1) show ?case
      unfolding equiv.prod_correct_step'[OF \<open>0 < p\<close>] .
  next
    case prems: (2 L s u L' s' u')
    then interpret equiv: Equiv_TA A n L s
      by - (rule Equiv_TA_I)
    from prems(1) show ?case
      unfolding equiv.prod_correct_step'[OF \<open>0 < p\<close>] .
  next
    case prems: (3 L s u L' s' u')
    then interpret equiv: Equiv_TA A n L s
      by - (rule Equiv_TA_I)
    from prems show ?case
      by (blast dest: equiv.step'_inv[OF \<open>0 < p\<close>])
  next
    case prems: (4 L s u L' s' u')
    then interpret equiv: Equiv_TA A n L s
      by - (rule Equiv_TA_I)
    from prems show ?case
      by (blast dest: equiv.step_u'_inv[OF \<open>0 < p\<close>])
  qed

interpretation Bisimulation_Invariant
  "\<lambda> (L, s, u) (L', s', u'). defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  "\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  "op ="
  "\<lambda> (L, s, u). all_prop L s"
  "\<lambda> (L, s, u). all_prop L s"
  by (rule Bisimulation_Invariant_I)

end (* p > 0 *)

end (* Equiv TA *)

definition models ("_,_ \<Turnstile>\<^sub>_ _" [61,61] 61) where
  "A,a\<^sub>0 \<Turnstile>\<^sub>n \<Phi> \<equiv> (case \<Phi> of
    formula.EX \<phi> \<Rightarrow>
      Graph_Defs.Ex_ev
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_bexp \<phi> L s)
  | formula.EG \<phi> \<Rightarrow>
      Graph_Defs.Ex_alw
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_bexp \<phi> L s)
  | formula.AX \<phi> \<Rightarrow>
      Graph_Defs.Alw_ev
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_bexp \<phi> L s)
  | formula.AG \<phi> \<Rightarrow>
      Graph_Defs.Alw_alw
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_bexp \<phi> L s)
  | formula.Leadsto \<phi> \<psi> \<Rightarrow>
      Graph_Defs.leadsto
        (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
        (\<lambda> (L, s, _). check_bexp \<phi> L s)
        (\<lambda> (L, s, _). check_bexp \<psi> L s)
  ) a\<^sub>0
  "

lemmas models_iff = models_def[unfolded Graph_Defs.Ex_alw_iff Graph_Defs.Alw_alw_iff]

context Reachability_Problem
begin

lemma reaches_steps':
  "reaches (l, u) (l', u') \<longleftrightarrow> conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>"
  apply standard
  subgoal premises prems
    using prems by (induction "(l, u)" "(l', u')" arbitrary: l' u') (auto intro: steps'_altI)
  subgoal premises prems
    using prems by induction (auto intro: converse_rtranclp_into_rtranclp)
  done

lemma clocks_I:
  "(\<forall> c. c \<in> clk_set (conv_A A) \<longrightarrow> u c = u' c)" if "\<forall> c \<in> {1..n}. u c = u' c"
  unfolding clk_set_conv_A using clocks_n using that by auto

lemma init_dbm_reaches_iff:
  "(\<exists> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>. \<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)
  \<longleftrightarrow> ([curry (init_dbm :: real DBM')]\<^bsub>v,n\<^esub> \<noteq> {} \<and>
    (\<forall> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>. \<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>))
  "
proof -
  interpret ta_bisim: Bisimulation_Invariant
    "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u'). l' = l \<and> (\<forall> c. c \<in> clk_set (conv_A A) \<longrightarrow> u c = u' c))"
    "(\<lambda>_. True)" "(\<lambda>_. True)"
    by (rule ta_bisimulation[of "conv_A A"])
  show ?thesis
    apply safe
      apply force
    subgoal for u1 u' u2
      unfolding init_dbm_semantics reaches_steps'[symmetric]
      apply (drule ta_bisim.A_B.simulation_reaches[of _ _ "(l\<^sub>0, u2)"])
      subgoal
        using clocks_I[of u1 u2] by fastforce
      by auto
    subgoal for u
      by blast
    done
qed

theorem reachable_decides_emptiness_new:
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {})
  \<longleftrightarrow> [curry (init_dbm :: real DBM')]\<^bsub>v,n\<^esub> \<noteq> {} \<and>
    (\<forall> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>. \<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)"
  unfolding reachable_decides_emptiness init_dbm_reaches_iff ..

lemma reachable_decides_emptiness'_new:
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {})
  \<longleftrightarrow> (\<forall> u. (\<forall> c \<in> {1..n}. u c = 0) \<longrightarrow> (\<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>))"
  unfolding reachable_decides_emptiness_new
  using init_dbm_semantics' init_dbm_semantics'' init_dbm_non_empty by blast

lemma reachability_check_new_aux:
  "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> [curry (conv_M D')]\<^bsub>v,n\<^esub> \<noteq> {} \<and> F l')
  \<longleftrightarrow> (\<forall> u. (\<forall> c \<in> {1..n}. u c = 0) \<longrightarrow> (\<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'))"
  using reachable_decides_emptiness'_new[of l'] by fast

theorem reachability_check_new:
    "(\<exists> D'. E\<^sup>*\<^sup>* a\<^sub>0 (l', D') \<and> F_rel (l', D'))
    \<longleftrightarrow> (\<forall> u. (\<forall> c \<in> {1..n}. u c = 0) \<longrightarrow> (\<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle> \<and> F l'))"
  using reachability_check_new_aux[of l'] check_diag_empty_spec reachable_empty_check_diag
  unfolding F_rel_def by auto

lemma init_state_in_state_set:
  "l\<^sub>0 \<in> state_set (trans_of A)" if "\<not> deadlock (l\<^sub>0, u\<^sub>0)"
proof -
  obtain l u where "conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<^sub>0\<rangle> \<rightarrow> \<langle>l, u\<rangle>"
    using \<open>\<not> deadlock _\<close> unfolding deadlock_def deadlocked_def by force
  then have "l\<^sub>0 \<in> state_set (trans_of (conv_A A))"
    unfolding state_set_def
    by cases (auto elim!: step_a.cases step_t.cases)
  then show ?thesis
    unfolding state_set_def unfolding trans_of_def by (cases A) force
qed

lemma init_state_in_state_set':
  "l\<^sub>0 \<in> state_set (trans_of A)" if "(\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0))"
  using init_state_in_state_set that by auto

end (* Reachability Problem *)

context Reachability_Problem_Impl
begin

context
    fixes Q :: "'s \<Rightarrow> bool" and Q_fun
    assumes Q_fun: "(Q_fun, Q) \<in> inv_rel states"
begin

(* XXX Put in place of for leadsto_spec_refine *)
lemma leadsto_spec_refine:
  "leadsto_spec_alt Q
  \<le> SPEC (\<lambda> r. \<not> r \<longleftrightarrow>
    (\<nexists>x. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) x \<and>
       F (fst x) \<and> Q (fst x) \<and>
       (\<exists>a. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>*\<^sup>* x a \<and>
            (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>+\<^sup>+ a a)
    ))"
proof -
  have *:"
    (\<lambda>x y. (case y of (l', M') \<Rightarrow> E_op''.E_from_op x (l', M') \<and> \<not> check_diag n M') \<and>
    \<not> (case y of (l, M) \<Rightarrow> check_diag n M))
    = (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))"
    by (intro ext) auto
  have **:
    "(\<lambda>x y. (case y of (l', M') \<Rightarrow> E_op''.E_from_op x (l', M') \<and> \<not> check_diag n M') \<and>
     (case y of (l, M) \<Rightarrow> Q l) \<and> \<not> (case y of (l, M) \<Rightarrow> check_diag n M))
     = (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))"
    by (intro ext) auto
  have ***: "\<not> check_diag n b"
    if "(\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* a\<^sub>0 (a, b)" for a b
    using that by cases (auto simp: a\<^sub>0_def)
  show ?thesis
    unfolding leadsto_spec_alt_def[OF Q_fun]
    unfolding PR_CONST_def a\<^sub>0_def[symmetric] by (auto dest: *** simp: * **)
  qed

(* XXX *)
lemma leadsto_impl_hnr':
  "(uncurry0
    (leadsto_impl TYPE('bb) TYPE('cc) TYPE('dd) state_copy_impl
      (succs_P_impl' Q_fun) a\<^sub>0_impl subsumes_impl (return \<circ> fst)
      succs_impl' emptiness_check_impl F_impl (Q_impl Q_fun)),
   uncurry0
    (SPEC
      (\<lambda>r. (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0)) \<longrightarrow>
           (\<not> r) =
           (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow>
                  leadsto (\<lambda>(l, u). F l) (\<lambda>(l, u). \<not> Q l) (l\<^sub>0, u\<^sub>0)))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  define p1 where "p1 \<equiv>
    (\<nexists>x. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) x \<and>
         F (fst x) \<and> Q (fst x) \<and>
         (\<exists>a. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>*\<^sup>* x a \<and>
              (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>+\<^sup>+ a a))"
  define p2 where "p2 \<equiv> (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0))"
  define p3 where
    "p3 \<equiv> (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> leadsto (\<lambda>(l, u). F l) (\<lambda>(l, u). \<not> Q l) (l\<^sub>0, u\<^sub>0))"
  show ?thesis
  unfolding state_set_eq[symmetric]
  using Reachability_Problem_Impl_Op.leadsto_impl_hnr[OF Reachability_Problem_Impl_Op_axioms,
    OF Q_fun precond_a\<^sub>0,
    FCOMP leadsto_spec_refine[THEN Id_SPEC_refine, THEN nres_relI], to_hnr, unfolded hn_refine_def
  ]
  using init_state_in_state_set'
  using leadsto_mc[of F Q]
  unfolding p1_def[symmetric] p2_def[symmetric] p3_def[symmetric]
  apply (simp del: state_set_eq)
  apply sepref_to_hoare
  apply sep_auto
  apply (erule cons_post_rule)
  apply sep_auto
  done
qed

end (* Context for leadsto predicate *)

end (* Reachability Problem Impl *)

context UPPAAL_Reachability_Problem_precompiled'
begin

lemma F_reachable_correct'_new:
  "impl.op.F_reachable
  \<longleftrightarrow> (\<exists> L' s'. \<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow> (\<exists> u'.
      conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
      \<and>  check_bexp \<phi> L' s')
    )" if "formula = formula.EX \<phi>"
  using that E_op''.E_from_op_reachability_check reachability_check_new
  unfolding impl.E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
  unfolding F_def by auto

lemma F_reachable_correct'_new':
  "impl.op.F_reachable
  \<longleftrightarrow> (\<exists> L' s'. \<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow> (\<exists> u'.
      conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>
      \<and>  \<not> check_bexp \<phi> L' s')
    )" if "formula = formula.AG \<phi>"
  using that E_op''.E_from_op_reachability_check reachability_check_new
  unfolding impl.E_op_F_reachable E_op''.F_reachable_def E_op''.reachable_def
  unfolding F_def by auto

lemma F_reachable_correct_new:
  "impl.op.F_reachable
  \<longleftrightarrow> (\<exists> L' s'. \<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow> (\<exists> u'.
      conv N \<turnstile>\<^sup>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
       \<and> check_bexp \<phi> L' s')
    )" if "formula = formula.EX \<phi>"
    unfolding F_reachable_correct'_new[OF that]
    apply (subst product'.prod_reachable_correct[symmetric])
    using prod_conv p_p p_gt_0 by simp+

lemma F_reachable_correct_new':
  "impl.op.F_reachable
  \<longleftrightarrow> (\<exists> L' s'. \<forall> u. (\<forall> c \<in> {1..m}. u c = 0) \<longrightarrow> (\<exists> u'.
      conv N \<turnstile>\<^sup>max_steps \<langle>init, s\<^sub>0, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>
       \<and> \<not> check_bexp \<phi> L' s')
    )" if "formula = formula.AG \<phi>"
    unfolding F_reachable_correct'_new'[OF that]
    apply (subst product'.prod_reachable_correct[symmetric])
    using prod_conv p_p p_gt_0 by simp+

definition
  "Alw_ev_checker = dfs_map_impl' TYPE('bb) TYPE('cc) TYPE('dd)
     (impl.succs_P_impl' final_fun) impl.a\<^sub>0_impl impl.subsumes_impl (return \<circ> fst)
     impl.state_copy_impl"

definition
  "leadsto_checker \<psi> = do {
      r \<leftarrow> leadsto_impl TYPE('bb) TYPE('cc) TYPE('dd)
      impl.state_copy_impl (impl.succs_P_impl' (\<lambda> (L, s). \<not> check_bexp \<psi> L s))
      impl.a\<^sub>0_impl impl.subsumes_impl (return \<circ> fst)
      impl.succs_impl' impl.emptiness_check_impl impl.F_impl
      (impl.Q_impl (\<lambda> (L, s). \<not> check_bexp \<psi> L s));
      return (\<not> r)
    }"

definition
  "model_checker = (
  case formula of
    formula.EX _ \<Rightarrow> reachability_checker' |
    formula.AG _ \<Rightarrow> do {
      r \<leftarrow> reachability_checker';
      return (\<not> r)
    } |
    formula.AX _ \<Rightarrow> do {
      r \<leftarrow> if PR_CONST (\<lambda>(x, y). F x y) (init, s\<^sub>0)
      then Alw_ev_checker TYPE('bb) TYPE('cc) TYPE('dd)
      else return False;
      return (\<not> r)
    } |
    formula.EG _ \<Rightarrow>
      if PR_CONST (\<lambda>(x, y). F x y) (init, s\<^sub>0)
      then Alw_ev_checker TYPE('bb) TYPE('cc) TYPE('dd)
      else return False |
    formula.Leadsto _ \<psi> \<Rightarrow> leadsto_checker TYPE('bb) TYPE('cc) TYPE('dd) \<psi>
  )
  "

lemma p'_gt_0:
  "0 < defs'.p"
  unfolding p_p by (rule p_gt_0)

interpretation Bisim_A: Bisimulation_Invariant
   "(\<lambda>(L, s, u) (L', s', u').
       defs'.defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)"
   "(\<lambda>(L, s, u) (L', s', u').
       conv N \<turnstile>\<^sup>max_steps \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
   "op =" "(\<lambda>(L, s, u). product'.all_prop L s)"
   "(\<lambda>(L, s, u). product'.all_prop L s)"
  by (rule product'.Bisimulation_Invariant_I) (rule p'_gt_0)

interpretation Bisim_B: Bisimulation_Invariant
  "(\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
  "(\<lambda>(L, s, u) (L', s', u').
       defs'.defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>)"
   "(\<lambda> (l, u') (L, s, u). (l, u') = ((L, s), u))" "\<lambda> _. True"
   "(\<lambda>(L, s, u). product'.all_prop L s)"
  unfolding prod_conv[symmetric] by (standard; (rule Bisim_A.A_invariant; assumption | auto; fail))

interpretation Bisimulation_Invariant
   "(\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
   "(\<lambda>(L, s, u) (L', s', u').
       conv N \<turnstile>\<^sup>max_steps \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
   "(\<lambda> (l, u') (L, s, u). (l, u') = ((L, s), u))" "\<lambda> _. True"
   "(\<lambda>(L, s, u). product'.all_prop L s)"
proof -
  interpret bisim: Bisimulation_Invariant
    "(\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
   "(\<lambda>(L, s, u) (L', s', u').
       conv N \<turnstile>\<^sup>max_steps \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)"
   "(\<lambda>a c. \<exists>b. (case b of (L, s, u) \<Rightarrow> product'.all_prop L s) \<and>
              (case a of (l, u') \<Rightarrow> \<lambda>(L, s, u). (l, u') = ((L, s), u)) b \<and> b = c)"
   "\<lambda> _. True"
   "(\<lambda>(L, s, u). product'.all_prop L s)"
    using Bisimulation_Invariant_composition[OF
        Bisim_B.Bisimulation_Invariant_axioms Bisim_A.Bisimulation_Invariant_axioms
        ]
    .
  show "Bisimulation_Invariant
     (\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
     (\<lambda>(L, s, u) (L', s', u').
       conv N \<turnstile>\<^sup>max_steps \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
     (\<lambda>(l, u') (L, s, u). (l, u') = ((L, s), u)) (\<lambda>_. True) (\<lambda>(L, s, u). product'.all_prop L s)"
    apply standard
    subgoal for a b a'
      apply (drule bisim.A_B_step[of a b a'])
         apply auto
      done
    subgoal for a b a'
      apply (drule bisim.B_A_step[of b a' a])
         apply auto
      done
     apply simp
    apply (drule bisim.B_invariant)
     apply auto
    done
qed

lemma models_correct:
  "conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps \<Phi> = (case \<Phi> of
    formula.EX \<phi> \<Rightarrow>
        (\<lambda> ((L, s), u). \<exists> L' s' u'. conv_A A \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<and> check_bexp \<phi> L' s')
  | formula.EG \<phi> \<Rightarrow>
      Not o Graph_Defs.Alw_ev
        (\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). \<not> check_bexp \<phi> L s)
  | formula.AX \<phi> \<Rightarrow>
      Graph_Defs.Alw_ev
        (\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). check_bexp \<phi> L s)
  | formula.AG \<phi> \<Rightarrow>
      Not o (\<lambda> ((L, s), u).
        \<exists> L' s' u'. conv_A A \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<and> \<not> check_bexp \<phi> L' s'
      )
  | formula.Leadsto \<phi> \<psi> \<Rightarrow>
      Graph_Defs.leadsto
        (\<lambda> (l, u) (l', u'). conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
        (\<lambda> ((L, s), _). check_bexp \<phi> L s)
        (\<lambda> ((L, s), _). check_bexp \<psi> L s)
  ) ((init, s\<^sub>0), u\<^sub>0)" if "\<not> deadlock ((init, s\<^sub>0), u\<^sub>0)"
proof -
  have *: "((Not \<circ>\<circ> case_prod) (\<lambda>(L, s) _. check_bexp \<phi> L s)) =
    (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s)" for \<phi> by auto

  show ?thesis
    apply (subst models_def)
    apply (cases \<Phi>)
    subgoal for \<phi>
      apply simp

      apply (subst Ex_ev_iff[
            of "(\<lambda>((L, s), _). check_bexp \<phi> L s)" _ "((init, s\<^sub>0), u\<^sub>0)", symmetric, simplified
            ])
        apply (drule equiv'_D[simplified], force)
       using product'.all_prop_start[OF p'_gt_0] apply (simp add: A_B.equiv'_def[simplified]; fail)
      apply (subst Ex_ev[OF that])
      unfolding reaches_steps'[symmetric]
      apply auto
      done
    subgoal for \<phi>
      apply simp
      apply (subst Ex_alw_iff[
            of "(\<lambda>((L, s), _). check_bexp \<phi> L s)" _ "((init, s\<^sub>0), u\<^sub>0)", symmetric, simplified
            ])
        apply (drule equiv'_D[simplified]; force)
       using product'.all_prop_start[OF p'_gt_0] apply (simp add: A_B.equiv'_def[simplified]; fail)
      unfolding Graph_Defs.Ex_alw_iff * ..
    subgoal for \<phi>
      apply simp
      apply (subst Alw_ev_iff[
            of "(\<lambda>((L, s), _). check_bexp \<phi> L s)" _ "((init, s\<^sub>0), u\<^sub>0)", symmetric, simplified
            ])
        apply (drule equiv'_D[simplified]; force)
       using product'.all_prop_start[OF p'_gt_0] apply (simp add: A_B.equiv'_def[simplified]; fail)
      unfolding Graph_Defs.Ex_alw_iff * ..
    subgoal for \<phi>
      apply simp
      unfolding Graph_Defs.Alw_alw_iff
      apply (subst Ex_ev_iff[
            of "(\<lambda>((L, s), _). \<not>check_bexp \<phi> L s)" _ "((init, s\<^sub>0), u\<^sub>0)", symmetric, simplified
            ])
        apply (drule equiv'_D[simplified], subst *[symmetric], force)
       using product'.all_prop_start[OF p'_gt_0] apply (simp add: A_B.equiv'_def[simplified]; fail)
      apply (subst Ex_ev[OF that])
      unfolding reaches_steps'[symmetric]
      apply auto
      done
    subgoal for \<phi> \<psi>
      apply simp
      apply (subst Leadsto_iff[
            of "(\<lambda>((L, s), _). check_bexp \<phi> L s)" _
               "(\<lambda>((L, s), _). check_bexp \<psi> L s)" _ "((init, s\<^sub>0), u\<^sub>0)", symmetric, simplified
            ])
         apply (drule equiv'_D[simplified]; force)
        apply (drule equiv'_D[simplified]; force)
       using  product'.all_prop_start[OF p'_gt_0] apply (simp add: A_B.equiv'_def[simplified]; fail)
      ..
    done
qed

(* XXX Remove less general versions *)
lemma final_fun_final':
  "((\<lambda> (L, s). P L s), (\<lambda> (L, s). P L s)) \<in> inv_rel states'" for P
  unfolding F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
  by (force dest!: states'_states')

lemma final_fun_final[intro, simp]:
  "((\<lambda> (L, s). P L s), (\<lambda> (L, s). P L s)) \<in> inv_rel states" for P
  using final_fun_final' states_states' by (rule inv_rel_mono)

abbreviation "u\<^sub>0 \<equiv> (\<lambda> _. 0 :: real)"

lemma deadlock_start_iff:
  "Bisim_A.B.deadlock (init, s\<^sub>0, \<lambda>_. 0) \<longleftrightarrow> deadlock ((init, s\<^sub>0), u\<^sub>0)"
  using product'.all_prop_start[OF p'_gt_0]
  by - (rule deadlock_iff[of _ "(init, s\<^sub>0, u\<^sub>0)", symmetric]; simp)

theorem model_check':
  "(uncurry0 (model_checker TYPE('bb) TYPE('cc) TYPE('dd)),
    uncurry0 (
      SPEC (\<lambda> r.
        \<not> Graph_Defs.deadlock
          (\<lambda> (L, s, u) (L', s', u'). conv N \<turnstile>\<^sup>max_steps \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>) (init, s\<^sub>0, u\<^sub>0) \<longrightarrow>
        r = (conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula)
      )
    )
   )
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  have *: "(\<lambda>(l, u). \<not> (case l of (L, s) \<Rightarrow> (Not \<circ>\<circ>\<circ> check_bexp) \<phi> L s))
    = (\<lambda>((L, s), _). check_bexp \<phi> L s)" for \<phi>
    by auto
  have **:
    "(\<lambda>(l, u). \<not> (case l of (L, s) \<Rightarrow> check_bexp \<phi> L s)) = (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s)"
    for \<phi> by auto
  have ***:
    "(\<lambda>(l, u). case l of (L, s) \<Rightarrow> \<phi> L s) = (\<lambda>((L, s), _). \<phi> L s)" for \<phi>
    by auto
  have ****: "(\<lambda>(L, y). (Not \<circ>\<circ>\<circ> check_bexp) \<psi> L y) = (\<lambda>(L, y). \<not>check_bexp \<psi> L y)" for \<psi>
    by auto
  have *****:
    "return True = (return False \<bind> return o Not)"
    by auto

  interpret ta_bisim: Bisimulation_Invariant
    "(\<lambda>(l, u) (l', u').
       conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u').
       conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)"
    "(\<lambda>(l, u) (l', u').
       l' = l \<and>
       (\<forall> c. c \<in> clk_set (conv_A A) \<longrightarrow>
            u c = u' c))"
    "(\<lambda>_. True)" "(\<lambda>_. True)"
    by (rule ta_bisimulation[of "conv_A A"])

  have bisim2:
    "(\<exists>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<and>
                  \<not> Alw_ev (\<lambda>(l, u). \<phi> l) ((init, s\<^sub>0), u\<^sub>0))
    \<longleftrightarrow> (\<not> Alw_ev (\<lambda>(l, u). \<phi> l) ((init, s\<^sub>0), u\<^sub>0))
    " for \<phi>
    apply safe
    subgoal for u
      apply (subst (asm) ta_bisim.Alw_ev_iff[of _ "(\<lambda>(l, u). \<phi> l)" _ "((init, s\<^sub>0), \<lambda>_. 0)"])
      using clocks_I[of u "\<lambda>_. 0"] unfolding ta_bisim.A_B.equiv'_def
        apply auto
      done
    by force

  have bisim1:
    "(\<exists>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<and> \<not> Alw_ev (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s) ((init, s\<^sub>0), u\<^sub>0)) =
     (\<not> Alw_ev (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s) ((init, s\<^sub>0), u\<^sub>0))" for \<phi>
    using bisim2[of "\<lambda> (L, s). \<not> check_bexp \<phi> L s"] unfolding *** .

  have bisim3:
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow>
      leadsto (\<lambda>((L, s), _). check_bexp \<phi> L s) (\<lambda>((L, s), _). check_bexp \<psi> L s) ((init, s\<^sub>0), u\<^sub>0)) =
      leadsto (\<lambda>((L, s), _). check_bexp \<phi> L s) (\<lambda>((L, s), _). check_bexp \<psi> L s) ((init, s\<^sub>0), u\<^sub>0)
    " for \<phi> \<psi>
    apply safe
     apply force
    subgoal for u
      apply (subst (asm) ta_bisim.Leadsto_iff[of
            _ "(\<lambda>((L, s), _). check_bexp \<phi> L s)" _ "(\<lambda>((L, s), _). check_bexp \<psi> L s)"
            _ "((init, s\<^sub>0), u)"
            ])
      using clocks_I[of u "\<lambda>_. 0"] unfolding ta_bisim.A_B.equiv'_def by auto
    done

  have bisim4:
    "(\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock ((init, s\<^sub>0), u\<^sub>0))
    \<longleftrightarrow> \<not> deadlock ((init, s\<^sub>0), u\<^sub>0)
    "
    apply safe
     apply fast
    subgoal for u
      apply (subst (asm) ta_bisim.deadlock_iff[of _ "((init, s\<^sub>0), u)"])
      using clocks_I[of u "\<lambda>_. 0"] unfolding ta_bisim.A_B.equiv'_def by auto
    done

  have bisim5:
    "(\<forall>u. (\<forall>c\<in>{1..m}. u c = 0) \<longrightarrow> (\<exists>u'. conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<and> \<phi> L' s'))
  \<longleftrightarrow> (\<exists>u'. conv_A A \<turnstile>' \<langle>(init, s\<^sub>0), u\<^sub>0\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<and> \<phi> L' s')
  " for \<phi> L' s'
    unfolding reaches_steps'[symmetric]
    apply safe
     apply fast
    subgoal for u' u
      apply (drule ta_bisim.bisim.A_B_reaches[of _ _ "((init, s\<^sub>0), u)"])
      subgoal
        using clocks_I[of u "\<lambda>_. 0"] unfolding ta_bisim.equiv'_def by auto
      unfolding ta_bisim.equiv'_def by auto
    done

  define protect where
    "protect = ((\<lambda>(l, u) (l', u').
                              conv_A A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>))"

  show ?thesis
    unfolding deadlock_start_iff
    using models_correct
    apply simp
    unfolding protect_def[symmetric]
    apply sepref_to_hoare
    apply sep_auto
    unfolding model_checker_def reachability_checker'_def Alw_ev_checker_def leadsto_checker_def
    apply (cases formula; simp)

      -- \<open>\<open>EX\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.pw_impl_hnr_F_reachable[to_hnr, unfolded hn_refine_def]
      apply (subst (asm) (2) F_reachable_correct'_new)
       apply (rule prems; fail)
      apply (subst (asm) bisim5)
      apply sep_auto
      unfolding final_fun_def F_def prems
      apply (erule cons_post_rule)
      apply (sep_auto simp: pure_def)
      done

        -- \<open>\<open>EG\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.Alw_ev_impl_hnr[where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd,
          to_hnr, unfolded hn_refine_def
          ]
      unfolding final_fun_def F_def prems(2)
        UPPAAL_Reachability_Problem_precompiled'.final_fun_def[
          OF UPPAAL_Reachability_Problem_precompiled'_axioms
          ]
        UPPAAL_Reachability_Problem_precompiled_defs.F_def
      apply sep_auto
      unfolding **
      subgoal
        apply (subst (asm) bisim1)
        apply (erule cons_post_rule)
        using init_state_in_state_set[of u\<^sub>0]
        apply (sep_auto simp: pure_def protect_def ***)
        done
      subgoal
        apply (subst (asm) bisim1)
        apply simp
        apply (erule cons_post_rule)
        using init_state_in_state_set[of u\<^sub>0]
        apply (sep_auto simp: pure_def protect_def ***)
        done
      done

        -- \<open>\<open>AX\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.Alw_ev_impl_hnr[where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd,
          to_hnr, unfolded hn_refine_def
          ]
      unfolding final_fun_def F_def
      unfolding UPPAAL_Reachability_Problem_precompiled_defs.F_def
      apply (subst
          UPPAAL_Reachability_Problem_precompiled'.final_fun_def[
            OF UPPAAL_Reachability_Problem_precompiled'_axioms
            ])
      apply (safe; clarsimp simp: prems(2))
      unfolding bisim2
      unfolding * ***
      subgoal
        using init_state_in_state_set[of u\<^sub>0]
        by (sep_auto simp: pure_def protect_def)
      subgoal
        unfolding protect_def *****
        apply (erule bind_rule)
        using init_state_in_state_set[of u\<^sub>0]
        apply (sep_auto simp: pure_def)
        done
      done

        -- \<open>\<open>AG\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.pw_impl_hnr_F_reachable[to_hnr, unfolded hn_refine_def]
      apply (subst (asm) (2) F_reachable_correct'_new')
       apply (rule prems; fail)
      apply (subst (asm) bisim5)
      unfolding final_fun_def F_def prems
      apply (sep_auto simp: pure_def)
      done

        -- \<open>\<open>Leadsto\<close>\<close>
    subgoal premises prems for \<phi> \<psi>
      using impl.leadsto_impl_hnr'[
          OF final_fun_final, of "Not oo check_bexp \<psi>",
          to_hnr, unfolded hn_refine_def
          ]
      unfolding * F_def
      apply (simp add: prems(2))
      unfolding *** **** bisim3 bisim4
      apply (erule bind_rule)
      apply (sep_auto simp: pure_def protect_def)
      done
    done
qed

theorem model_check'_hoare:
  "<emp>
    model_checker TYPE('bb) TYPE('cc) TYPE('dd)
  <\<lambda>r. \<up> ((\<not> Bisim_A.B.deadlock (init, s\<^sub>0, \<lambda>_. 0)) \<longrightarrow> r = (
    conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula
  ))>\<^sub>t"
  using model_check'[to_hnr, unfolded hn_refine_def, where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd]
  by (sep_auto simp: pure_def elim!: cons_post_rule)

lemma Alw_ev_checker_alt_def':
  "Alw_ev_checker TYPE('bb) TYPE('cc) TYPE('dd) \<equiv>
    do {
      x \<leftarrow> let
        key = return \<circ> fst;
        sub = impl.subsumes_impl;
        copy = impl.state_copy_impl;
        start = impl.a\<^sub>0_impl;
        succs =  impl.succs_P_impl' final_fun
      in dfs_map_impl' TYPE('bb) TYPE('cc) TYPE('dd) succs start sub key copy;
      _ \<leftarrow> return ();
      return x
    }"
  unfolding Alw_ev_checker_def by simp

lemma leadsto_checker_alt_def':
  "leadsto_checker TYPE('bb) TYPE('cc) TYPE('dd) \<psi> \<equiv>
    do {
      r \<leftarrow> let
        key = return \<circ> fst;
        sub = impl.subsumes_impl;
        copy = impl.state_copy_impl;
        start = impl.a\<^sub>0_impl;
        final = impl.F_impl;
        final' = (impl.Q_impl (\<lambda>(L, s). \<not> check_bexp \<psi> L s));
        succs =  impl.succs_P_impl' (\<lambda>(L, s). \<not> check_bexp \<psi> L s);
        succs' =  impl.succs_impl';
        empty = impl.emptiness_check_impl
      in
        leadsto_impl TYPE('bb) TYPE('cc) TYPE('dd)
          copy succs start sub key succs' empty final final';
      return (\<not> r)
    }"
  unfolding leadsto_checker_def by simp

schematic_goal succs_P_impl_alt_def:
  "impl.succs_P_impl (\<lambda>(L, s). P L s) \<equiv> ?impl" for P
  unfolding impl.succs_P_impl_def[OF final_fun_final]
  unfolding k_impl_alt_def
  apply (tactic
      \<open>pull_tac
      @{term
        "\<lambda> (l, _). IArray (map (\<lambda> c. Max {k_i !! i !! (l ! i) !! c | i. i \<in> {0..<p}}) [0..<m+1])"
      }
      @{context}
     \<close>
      )
  apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
  unfolding inv_fun_def[abs_def] trans_fun_def[abs_def] trans_s_fun_def trans_i_fun_def trans_i_from_def
  apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
  by (rule Pure.reflexive)

(* XXX These implementations contain unnecessary list reversals *)
lemmas succs_P'_impl_alt_def =
  impl.succs_P_impl'_def[OF final_fun_final, unfolded succs_P_impl_alt_def]

lemmas succs_impl'_alt_def =
  impl.succs_impl'_def[unfolded succs_impl_alt_def]

lemma reachability_checker'_alt_def':
  "reachability_checker' \<equiv>
    do {
      x \<leftarrow> do {
        let key = return \<circ> fst;
        let sub = impl.subsumes_impl;
        let copy = impl.state_copy_impl;
        let start = impl.a\<^sub>0_impl;
        let final = impl.F_impl;
        let succs =  impl.succs_impl;
        let empty = impl.emptiness_check_impl;
        pw_impl key copy sub start final succs empty
      };
      _ \<leftarrow> return ();
      return x
    }"
  unfolding reachability_checker'_def by simp

schematic_goal reachability_checker'_alt_def:
  "reachability_checker' \<equiv> ?impl"
  unfolding reachability_checker'_alt_def' impl.succs_impl_def
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def unbounded_dbm_def
  unfolding k_impl_alt_def
  apply (tactic \<open>pull_tac @{term k_i} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>) (* XXX This is not pulling anything *)
  apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding final_fun_def[abs_def]
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

schematic_goal Alw_ev_checker_alt_def:
  "Alw_ev_checker TYPE('bb) TYPE('cc) TYPE('dd) \<equiv> ?impl"
  unfolding Alw_ev_checker_alt_def' final_fun_def
    impl.succs_P_impl_def[OF final_fun_final] impl.succs_P_impl'_def[OF final_fun_final]
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def unbounded_dbm_def
  unfolding k_impl_alt_def
  apply (tactic \<open>pull_tac @{term k_i} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>) (* XXX This is not pulling anything *)
  apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding impl.F_impl_def
  unfolding final_fun_def[abs_def]
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

schematic_goal leadsto_checker_alt_def:
  "leadsto_checker TYPE('bb) TYPE('cc) TYPE('dd) \<equiv> ?impl"
  unfolding leadsto_checker_alt_def'
  unfolding impl.F_impl_def impl.Q_impl_def[OF final_fun_final]
  unfolding impl.succs_P_impl'_def[OF final_fun_final]
  unfolding impl.succs_impl'_def impl.succs_impl_def impl.succs_P_impl_def[OF final_fun_final]
  unfolding impl.E_op''_impl_def impl.abstr_repair_impl_def impl.abstra_repair_impl_def
  unfolding
    impl.start_inv_check_impl_def impl.unbounded_dbm_impl_def
    impl.unbounded_dbm'_def unbounded_dbm_def
  unfolding k_impl_alt_def
  apply (tactic \<open>pull_tac @{term k_i} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "inv_fun"} @{context}\<close>) (* XXX This is not pulling anything *)
  apply (tactic \<open>pull_tac @{term "trans_fun"} @{context}\<close>)
  unfolding impl.init_dbm_impl_def impl.a\<^sub>0_impl_def
  unfolding final_fun_def
  unfolding impl.subsumes_impl_def
  unfolding impl.emptiness_check_impl_def
  unfolding impl.state_copy_impl_def
  by (rule Pure.reflexive)

schematic_goal reachability_checker'_alt_def_refined:
  "reachability_checker' \<equiv> ?impl"
  unfolding reachability_checker'_alt_def
  unfolding fw_impl'_int
  unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def
  unfolding trans_i_from_impl
  unfolding runf_impl runt_impl check_g_impl pairs_by_action_impl check_pred_impl
  apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray bounds"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PF} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PT} @{context}\<close>)
  unfolding PF_alt_def PT_alt_def
  apply (tactic \<open>pull_tac @{term PROG'} @{context}\<close>)
  unfolding PROG'_def
  apply (tactic \<open>pull_tac @{term "length prog"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stripf) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stript) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray prog"} @{context}\<close>)
  unfolding all_actions_by_state_impl
  apply (tactic \<open>pull_tac @{term "[0..<p]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<na]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "{0..<p}"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<m+1]"} @{context}\<close>)
  by (rule Pure.reflexive)

schematic_goal Alw_ev_checker_alt_def_refined:
  "Alw_ev_checker TYPE('bb) TYPE('cc) TYPE('dd) \<equiv> ?impl"
  unfolding Alw_ev_checker_alt_def
  unfolding fw_impl'_int
  unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def
  unfolding trans_i_from_impl
  unfolding runf_impl runt_impl check_g_impl pairs_by_action_impl check_pred_impl
  apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray bounds"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PF} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PT} @{context}\<close>)
  unfolding PF_alt_def PT_alt_def
  apply (tactic \<open>pull_tac @{term PROG'} @{context}\<close>)
  unfolding PROG'_def
  apply (tactic \<open>pull_tac @{term "length prog"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stripf) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stript) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray prog"} @{context}\<close>)
  unfolding all_actions_by_state_impl
  apply (tactic \<open>pull_tac @{term "[0..<p]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<na]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "{0..<p}"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<m+1]"} @{context}\<close>)
  by (rule Pure.reflexive)

schematic_goal leadsto_checker_alt_def_refined:
  "leadsto_checker TYPE('bb) TYPE('cc) TYPE('dd) \<equiv> ?impl"
  unfolding leadsto_checker_alt_def
  unfolding fw_impl'_int
  unfolding inv_fun_def trans_fun_def trans_s_fun_def trans_i_fun_def
  unfolding trans_i_from_impl
  unfolding runf_impl runt_impl check_g_impl pairs_by_action_impl check_pred_impl
  apply (tactic \<open>pull_tac @{term "IArray (map IArray inv)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_out_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_in_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map IArray trans_i_map)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray bounds"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PF} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term PT} @{context}\<close>)
  unfolding PF_alt_def PT_alt_def
  apply (tactic \<open>pull_tac @{term PROG'} @{context}\<close>)
  unfolding PROG'_def
  apply (tactic \<open>pull_tac @{term "length prog"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stripf) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray (map (map_option stript) prog)"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "IArray prog"} @{context}\<close>)
  unfolding all_actions_by_state_impl
  apply (tactic \<open>pull_tac @{term "[0..<p]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<na]"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "{0..<p}"} @{context}\<close>)
  apply (tactic \<open>pull_tac @{term "[0..<m+1]"} @{context}\<close>)
  by (rule Pure.reflexive)

end

concrete_definition reachability_checker'
  uses UPPAAL_Reachability_Problem_precompiled'.reachability_checker'_alt_def_refined

concrete_definition Alw_ev_checker
  uses UPPAAL_Reachability_Problem_precompiled'.Alw_ev_checker_alt_def_refined

concrete_definition leadsto_checker
  uses UPPAAL_Reachability_Problem_precompiled'.leadsto_checker_alt_def_refined

context UPPAAL_Reachability_Problem_precompiled'
begin

lemmas model_checker_def_refined = model_checker_def[unfolded
    reachability_checker'.refine[OF UPPAAL_Reachability_Problem_precompiled'_axioms]
    Alw_ev_checker.refine[OF UPPAAL_Reachability_Problem_precompiled'_axioms]
    leadsto_checker.refine[OF UPPAAL_Reachability_Problem_precompiled'_axioms]
  ]

end

concrete_definition model_checker uses
  UPPAAL_Reachability_Problem_precompiled'.model_checker_def_refined

definition [code]:
  "precond_mc p m k max_steps I T prog final bounds P s\<^sub>0 na \<equiv>
    if UPPAAL_Reachability_Problem_precompiled' p m max_steps I T prog bounds P s\<^sub>0 na k
    then
      model_checker TYPE('bb) TYPE('cc) TYPE('dd) p m max_steps I T prog bounds P s\<^sub>0 na k final
      \<bind> (\<lambda> x. return (Some x))
    else return None"

theorem model_check:
  "<emp> precond_mc TYPE('bb) TYPE('cc) TYPE('dd) p m k max_steps I T prog formula bounds P s\<^sub>0 na
    <\<lambda> r. \<up> (
    if UPPAAL_Reachability_Problem_precompiled' p m max_steps I T prog bounds P s\<^sub>0 na k
    then r \<noteq> None \<and>
      (\<not> Graph_Defs.deadlock
          (\<lambda> (L, s, u) (L', s', u').
            conv (N p I P T prog bounds) \<turnstile>\<^sup>max_steps \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>
          )
          (repeat 0 p, s\<^sub>0, \<lambda>_ . 0) \<longrightarrow>
      r = Some (
        conv (N p I P T prog bounds),(repeat 0 p, s\<^sub>0, \<lambda>_ . 0) \<Turnstile>\<^sub>max_steps formula
      ))
    else r = None
    )>\<^sub>t"
proof -
  define A where "A \<equiv> conv (N p I P T prog bounds)"
  define no_deadlock where
    "no_deadlock \<equiv> (\<forall>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> Graph_Defs.deadlock
          (\<lambda>(l, u) (l', u').
              (case Prod_TA_Defs.prod_ta
                     (Equiv_TA_Defs.state_ta
                       (N p I P T prog bounds) max_steps) of
               (T, I) \<Rightarrow>
                 ((\<lambda>(l, g, a, r, l').
                      (l, map conv_ac g, a, r, l')) `
                  T,
                  map conv_ac \<circ> I)) \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
          ((repeat 0 p,
            s\<^sub>0),
           u\<^sub>0))"
  define check where
    "check \<equiv>
        A,(repeat 0 p, s\<^sub>0, \<lambda>_ . 0) \<Turnstile>\<^sub>max_steps formula"
  note [sep_heap_rules] =
    UPPAAL_Reachability_Problem_precompiled'.model_check'_hoare[
      of p m max_steps I T prog bounds P s\<^sub>0 na k formula,
      unfolded UPPAAL_Reachability_Problem_precompiled_defs.init_def,
      folded A_def check_def no_deadlock_def,
      where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd
      ]
  have *: "(no_deadlock \<longrightarrow> r = Some check) \<longleftrightarrow> (if no_deadlock then r = Some check else True)" for r
    by auto
  show ?thesis
    unfolding UPPAAL_Reachability_Problem_precompiled_defs.init_def
    unfolding A_def[symmetric] check_def[symmetric] no_deadlock_def[symmetric]
    unfolding precond_mc_def * by (sep_auto simp: model_checker.refine[symmetric])
qed

prepare_code_thms dfs_map_impl'_def leadsto_impl_def

(* XXX Debug code generator performance problems in conjunction with Let-expressions *)
lemmas [code] =
  reachability_checker'_def
  Alw_ev_checker_def
  leadsto_checker_def
  model_checker_def[unfolded UPPAAL_Reachability_Problem_precompiled_defs.F_def PR_CONST_def]

export_code
  precond_mc Pure.type init_pred_check time_indep_check1 time_indep_check1 conjunction_check2
  checking SML_imp

end (* Theory *)