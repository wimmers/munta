theory UPPAAL_Model_Checking
  imports
    UPPAAL_State_Networks_Impl_Refine
    "~~/src/HOL/Library/BNF_Corec"
begin

hide_const models

context Simulation
begin

lemma simulation_run:
  "\<exists> ys. B.run (y ## ys) \<and> stream_all2 op \<sim> xs ys" if "A.run (x ## xs)" "x \<sim> y"
proof -
  let ?ys = "sscan (\<lambda> a' b. SOME b'. B b b' \<and> a' \<sim> b') xs y"
  have "B.run (y ## ?ys)"
    using that
    apply (coinduction arbitrary: x y xs)
    apply simp
    apply (rule conjI)
    subgoal for x y xs
      by (auto dest!: someI_ex A_B_step elim: A.run.cases)
    subgoal for x y xs
      apply (rule disjI1)
      apply (inst_existentials "shd xs" "stl xs")
      apply (auto dest!: someI_ex A_B_step elim: A.run.cases)
      done
    done
  moreover have "stream_all2 op \<sim> xs ?ys"
    using that
    apply (coinduction arbitrary: x y xs)
    apply simp
    apply (rule conjI)
    subgoal for x y xs
      by (auto dest!: someI_ex A_B_step elim: A.run.cases)
    subgoal for a u b v x y xs
      by (inst_existentials "shd xs" "(SOME b'. B y b' \<and> a \<sim> b')")
         (auto dest!: someI_ex A_B_step elim: A.run.cases)
    done
  ultimately show ?thesis by blast
qed

end

(*
Summarize the two action steps first. Then do delay \<rightarrow> action.
*)
inductive step_u' ::
  "('a, 't :: time, 's) unta \<Rightarrow> nat \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval
  \<Rightarrow> 's list \<Rightarrow> int list \<Rightarrow> (nat, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sup>_ \<langle>_, _, _\<rangle> \<rightarrow> \<langle>_, _, _\<rangle>" [61,61,61,61,61,61] 61) where
  "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>" if
  "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" "A \<turnstile>\<^sub>n \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>"

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

lemma prod_correct':
  "defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle> =
     state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  apply rule
   apply (rule prod.prod_sound prod.prod_complete, assumption)+
  done

lemma equiv_correct:
  "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle> =
  A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  apply rule
   apply (rule equiv_sound equiv_complete, assumption)+
  done

lemma prod_correct:
  "defs.prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle> =
  A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  unfolding prod_correct' equiv_correct ..

(* XXX Move *)
lemma (in -) steps'_altI:
  "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l'', u''\<rangle>" if "A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>" "A \<turnstile>' \<langle>l', u'\<rangle> \<rightarrow> \<langle>l'', u''\<rangle>"
  using that by induction auto

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
  "all_prop L' s'" if "A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  using equiv_complete''[OF that] equiv_complete'[OF that]
  unfolding all_prop_def by auto

lemma step_inv:
  "all_prop L' s'" if "state_ta \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  using step_u_inv[OF equiv_sound[OF that]] .

lemma Equiv_TA_I:
  "Equiv_TA A n L' s'" if *[unfolded all_prop_def]: "all_prop L' s'"
  apply standard
    subgoal
      using * by auto
    subgoal
      by (rule pred_time_indep)
    subgoal
      by (rule upd_time_indep)
    subgoal
      by (rule clock_conj)
    subgoal
      by (rule Len)
    subgoal
      using * by auto
    subgoal
      using * by auto
    done

lemma step_u'_inv:
  "all_prop L'' s'' \<and> defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L'', s''), u''\<rangle>"
  if "A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>"
using that proof cases
  case prems: (1 L' s' u')
  from step_u_inv[OF prems(1)] have *[unfolded all_prop_def]: "all_prop L' s'" .
  interpret equiv: Equiv_TA A n L' s'
    using Equiv_TA_I[OF step_u_inv[OF prems(1)]] .
  thm prems(1)[unfolded prod_correct[symmetric]]
  from equiv.step_u_inv[OF \<open>0 < p\<close> prems(2)] show ?thesis
    apply -
    apply rule
     apply assumption
    apply rule
    using prems[unfolded prod_correct[symmetric] equiv.prod_correct[symmetric]] sorry
    (* We just need to split up the prod_correct theorem here. Pure refactoring *)
qed

lemma step'_inv:
  "all_prop L'' s'' \<and> A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>"
  if "defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L'', s''), u''\<rangle>"
using that proof cases
  case (step' d l' u' a)
  then show ?thesis
    sorry
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

interpretation Bisimulation_Invariant
  "\<lambda> (L, s, u) (L', s', u'). defs.prod_ta \<turnstile>' \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  "\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
  "op ="
  "\<lambda> (L, s, u). all_prop L s"
  "\<lambda> (L, s, u). all_prop L s"
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

end (* p > 0 *)

end (* Equiv TA *)

thm Equiv_TA.prod_correct


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

term "A,a\<^sub>0 \<Turnstile>\<^sub>n \<Phi>"

lemmas models_iff = models_def[unfolded Graph_Defs.Ex_alw_iff Graph_Defs.Alw_alw_iff]

(*
term sscan term "\<lambda> xs. sscan (\<lambda> a (_, i). (a, Suc i)) xs (undefined, 0)"

definition substream :: "'a stream => nat set => 'a stream" where
"substream xs I =
  smap fst (sfilter (\<lambda> (a, i). i \<in> I) (sscan (\<lambda> a (_, i). (a, Suc i)) xs (undefined, 0)))"

lemma substream_eq_ConsD:
  assumes "substream xs I = x ## as"
  shows
    "\<exists> ys zs.
      xs = ys @- x ## zs \<and> length ys \<in> I \<and> (\<forall> i \<in> I. i \<ge> length ys)
      \<and> substream zs ({i - length ys - 1 | i. i \<in> I \<and> i > length ys}) = as"
    sorry

lemma
  "ev (holds P) xs" if "ev (holds P) (substream xs I)"
  using that thm ev.induct
  apply (induction "substream xs I" arbitrary: xs I)
   apply simp
  subgoal for xs I
    apply (cases "substream xs I")
    apply simp
    apply (frule substream_eq_ConsD)
    apply auto
      oops

context
  fixes A :: "('a, 'c, 't :: time, 's) ta"
begin

interpretation G: Graph_Defs "\<lambda> (l, u) (l', u'). A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" .
interpretation G': Graph_Defs "\<lambda> (l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" .

corec expand_run :: "('s \<times> ('c, 't) cval) stream \<Rightarrow> ('s \<times> ('c, 't) cval) stream" where
  "expand_run xs =
    (case xs of (l, u) ## (l', u') ## ys \<Rightarrow>
      (l, u) ## (l, SOME u''. \<exists> a d. A \<turnstile> \<langle>l, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>l, u''\<rangle> \<and> A \<turnstile> \<langle>l, u''\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>l', u'\<rangle>)
      ## expand_run ((l', u') ## ys)
    )"

lemma
  "\<exists> xs. G.run (x ## xs) \<and> alw (holds (\<lambda> (l, u). P l)) (x ## xs)"
  if "G'.run (x ## xs)" "alw (holds (\<lambda> (l, u). P l)) (x ## xs)"
proof -
  from that(1) have "G.run (expand_run (x ## xs))"
  proof (coinduction arbitrary: x xs)
    case run
    then show ?case sorry -- "Need to proof specialized coinduction rule for G.rule"
  qed
oops

end

*)

(* XXX Move *)
lemma cval_add_0:
  "u \<oplus> 0 = u" for u :: "(_, _ :: time) cval"
  unfolding cval_add_def by simp

lemma Ex_ev_eq_reachability:
  assumes
    "\<forall>p<length (fst (snd A)). \<exists>pc st s' rs.
       stepst (fst A) n u
          ((fst (snd (snd A)) ! p) (L ! p), [], s, True, [])
          (pc, st, s', True, rs)"
    "\<forall>p<length (fst (snd A)). u \<turnstile> snd (fst (snd A) ! p) (L ! p)"
    "bounded (snd (snd (snd A))) s"
  shows
  "Graph_Defs.Ex_ev
    (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
    (\<lambda> (L, s, _). P L s) (L, s, u)
   \<longleftrightarrow> (\<exists> L' s' u'. A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<and> P L' s')
  "
  unfolding Graph_Defs.Ex_ev_def
  apply safe
  subgoal for xs
    apply (drule ev_imp_shift)
    apply safe
    subgoal for ys zs
      apply (cases zs)
      apply clarsimp
      subgoal premises prems for L' s' u' ws
        proof (cases ys)
          case Nil
          with prems show ?thesis
            by fastforce
        next
          case (Cons a us)
          with prems have
            "Graph_Defs.run (\<lambda>(L, s, u) (L', x, y). A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', x, y\<rangle>)
              ((L, s, u) ## us @- (L', s', u') ## ws)"
            by simp
          with \<open>P _ _\<close> show ?thesis
          proof (induction us arbitrary: L s u)
            case Nil
            then show ?case
              apply (inst_existentials L' s')
              apply clarsimp
              apply (erule Graph_Defs.run.cases)
              apply clarify
              apply (inst_existentials u')
              apply rule
              by auto
          next
            case (Cons a us)
            obtain L'' s'' u'' where [simp]: "a = (L'', s'', u'')"
              by (cases a) auto
            from Cons.prems(2) Cons.IH[OF \<open>P _ _\<close>] obtain L' s' a where
              "A \<turnstile>\<^sub>n \<langle>L'', s'', u''\<rangle> \<rightarrow>* \<langle>L', s', a\<rangle>" "P L' s'"
              by atomize_elim (fastforce elim: Graph_Defs.run.cases)
            with Cons.prems(2) show ?case
              by - (erule Graph_Defs.run.cases, clarsimp, metis UPPAAL_State_Networks.stepI2)
          qed
        qed
        done
      done
    subgoal premises prems for L' s' u'
    proof -
      interpret Graph_Defs "\<lambda>(L, s, u) (L', x, y). A \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', x, y\<rangle>" .
      from prems(1) have "reaches (L, s, u) (L', s', u')"
        by (induction; blast intro!: rtranclp.rtrancl_into_rtrancl)
      from reaches_steps[OF this] guess xs by clarify
      note xs = this
      from prems(1) have "A \<turnstile>\<^sub>n \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L', s', u' \<oplus> 0\<rangle>"
        apply cases
        subgoal
          using assms by (cases A)  (simp add: , rule step_u_t, auto simp: cval_add_0)
        subgoal
          by (cases A, simp, rule step_u_t, auto simp: cval_add_0 elim!: step_u.cases)
        done
      then have "run (sconst (L', s', u'))"
        by coinduction (simp add: cval_add_0)
      with xs have "run (xs @- sconst (L', s', u'))"
        by - (subst siterate.ctr, erule run.cases, clarsimp, rule extend_run, auto)
      with xs \<open>P _ _\<close> show ?thesis
        apply (inst_existentials "tl xs @- sconst (L', s', u')")
        subgoal
          by (erule steps.cases; simp)
        subgoal
          apply (erule steps.cases)
           apply (simp, rule ev.base, simp; fail)
          apply (subst append_butlast_last_id[of xs, symmetric])
           apply (simp; fail)
          apply (fastforce intro: ev_shift)
          done
        done
    qed
    done

lemma Ex_ev_eq_reachability':
  assumes
    "\<forall>p<length (fst (snd A)). \<exists>pc st s' rs.
       stepst (fst A) n u
          ((fst (snd (snd A)) ! p) (L ! p), [], s, True, [])
          (pc, st, s', True, rs)"
    "\<forall>p<length (fst (snd A)). u \<turnstile> snd (fst (snd A) ! p) (L ! p)"
    "bounded (snd (snd (snd A))) s"
  shows
  "Graph_Defs.Ex_ev
    (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
    (\<lambda> (L, s, _). P L s) (L, s, u)
   \<longleftrightarrow> (\<exists> L' s' u'. A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<and> P L' s')
  "
  sorry

lemma models_alt_def:
  assumes
    "\<forall>p<length (fst (snd A)). \<exists>pc st s' rs.
       stepst (fst A) n u
          ((fst (snd (snd A)) ! p) (L ! p), [], s, True, [])
          (pc, st, s', True, rs)"
    "\<forall>p<length (fst (snd A)). u \<turnstile> snd (fst (snd A) ! p) (L ! p)"
    "bounded (snd (snd (snd A))) s"
  shows
    "A,(L,s,u) \<Turnstile>\<^sub>n \<Phi> = (case \<Phi> of
      formula.EX \<phi> \<Rightarrow>
        (\<lambda> (L, s, u). \<exists> L' s' u'. A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<and> check_bexp \<phi> L' s')
    | formula.EG \<phi> \<Rightarrow>
        Not o Graph_Defs.Alw_ev
          (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
          (\<lambda> (L, s, _). \<not> check_bexp \<phi> L s)
    | formula.AX \<phi> \<Rightarrow>
        Graph_Defs.Alw_ev
          (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
          (\<lambda> (L, s, _). check_bexp \<phi> L s)
    | formula.AG \<phi> \<Rightarrow>
        Not o (\<lambda> (L, s, u). \<exists> L' s' u'. A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<and> \<not> check_bexp \<phi> L' s')
    | formula.Leadsto \<phi> \<psi> \<Rightarrow>
        Graph_Defs.leadsto
          (\<lambda> (L, s, u) (L', s', u'). A \<turnstile>\<^sup>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>)
          (\<lambda> (L, s, _). check_bexp \<phi> L s)
          (\<lambda> (L, s, _). check_bexp \<psi> L s)
    ) (L,s,u)
    "
proof -
  have *:
    "(Not \<circ>\<circ> case_prod) (\<lambda>L (s, _). check_bexp \<phi> L s) = (\<lambda> (L, s, _). \<not> check_bexp \<phi> L s)" for \<phi>
    by auto
  show ?thesis
    unfolding models_def Graph_Defs.Alw_alw_iff Graph_Defs.Ex_alw_iff
    by (cases "\<Phi>") (auto simp: * Ex_ev_eq_reachability'[OF assms])
qed

context Reachability_Problem
begin

lemma init_dbm_reaches_iff:
  "(\<exists> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>. \<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>)
  \<longleftrightarrow> ([curry (init_dbm :: real DBM')]\<^bsub>v,n\<^esub> \<noteq> {} \<and>
    (\<forall> u \<in> [curry init_dbm]\<^bsub>v,n\<^esub>. \<exists> u'. conv_A A \<turnstile>' \<langle>l\<^sub>0, u\<rangle> \<rightarrow>* \<langle>l', u'\<rangle>))
  "
  apply safe
    apply force
  subgoal for u1 u' u2
    sorry
  subgoal for u
    by blast
  done

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

end

context Reachability_Problem_Impl
begin

context
    fixes Q :: "'s \<Rightarrow> bool" and Q_fun
    assumes Q_fun: "(Q_fun, Q) \<in> inv_rel states"
    assumes l\<^sub>0_state_set: "l\<^sub>0 \<in> state_set (trans_of A)"
begin

lemma leadsto_spec_refine:
  "leadsto_spec_alt Q
  \<le> SPEC (\<lambda> r. \<not> r \<longleftrightarrow>
    (\<nexists>x. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) x \<and>
       F (fst x) \<and>
       Q (fst x) \<and>
       (\<exists>a. (\<lambda>a b. E_op''.E_from_op a b \<and>
                   \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>*\<^sup>*
             x a \<and>
            (\<lambda>a b. E_op''.E_from_op a b \<and>
                   \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>+\<^sup>+
             a a))
    )"
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

lemma leadsto_impl_hnr:
  "(uncurry0
    (leadsto_impl TYPE('bb) TYPE('cc) TYPE('dd)
      state_copy_impl (succs_P_impl' Q_fun) a\<^sub>0_impl
      subsumes_impl (return \<circ> fst) local.succs_impl'
      emptiness_check_impl F_impl (Q_impl Q_fun)),
   uncurry0
    (SPEC
      (\<lambda>r. (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0)) \<longrightarrow> (\<not> r) =
           (\<forall>u\<^sub>0.
               (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow>
               leadsto (\<lambda>(l, u). F l) (\<lambda>(l, u). \<not> Q l)
                (l\<^sub>0, u\<^sub>0)))))
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
proof -
  define P where "P = (\<forall>u\<^sub>0.
               (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow>
               leadsto (\<lambda>(l, u). F l) (\<lambda>(l, u). \<not> Q l)
                (l\<^sub>0, u\<^sub>0))"
  define q where "q = (\<forall>u\<^sub>0. (\<forall>c\<in>{1..n}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock (l\<^sub>0, u\<^sub>0))"
  define r where "r = (\<nexists>x. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b))\<^sup>*\<^sup>* (l\<^sub>0, init_dbm) x \<and>
       F (fst x) \<and>
       Q (fst x) \<and>
       (\<exists>a. (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>*\<^sup>* x a \<and>
            (\<lambda>a b. E_op''.E_from_op a b \<and> \<not> check_diag n (snd b) \<and> Q (fst b))\<^sup>+\<^sup>+ a a))"
  define prog where "prog = leadsto_impl TYPE('bb) TYPE('cc) TYPE('dd)
      state_copy_impl (succs_P_impl' Q_fun) a\<^sub>0_impl
      subsumes_impl (return \<circ> fst) local.succs_impl'
      emptiness_check_impl F_impl (Q_impl Q_fun)"
  show ?thesis
    unfolding prog_def[symmetric] P_def[symmetric] q_def[symmetric]


  using Reachability_Problem_Impl_Op.leadsto_impl_hnr[OF Reachability_Problem_Impl_Op_axioms,
    OF Q_fun precond_a\<^sub>0,
    FCOMP leadsto_spec_refine[THEN Id_SPEC_refine, THEN nres_relI],
    where 'b35 = 'bb and 'c35 = 'cc and 'd35 = 'dd,
    folded prog_def P_def q_def r_def,
    to_hnr, unfolded hn_refine_def
    ]
  apply sepref_to_hoare
  apply sep_auto
  apply (erule cons_post_rule)
  apply (sep_auto simp: leadsto_mc[OF l\<^sub>0_state_set[folded state_set_eq], of F Q, symmetric, folded q_def r_def P_def])
  done
qed

end

end (* Context for leadsto predicate *)

context UPPAAL_Reachability_Problem_precompiled'
begin

(* XXX Fix naming problem *)
(* XXX Unnecessary *)
lemmas reachability_check_old =
  Normalized_Zone_Semantics_Impl.Reachability_Problem.reachability_check
  [OF Reachability_Problem_axioms]

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

thm reachability_checker'_def impl.pw_impl_hnr_F_reachable

thm final_fun_def F_def

thm
  impl.leadsto_impl_hnr[OF _]
  impl.Alw_ev_impl_hnr[OF _]

term formula term pw_impl

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

term model_checker

thm model_checker_def

term TA.steps

sublocale sem: Graph_Defs "\<lambda> (l, u) (l', u'). conv_A A \<turnstile> \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" .

term "conv N"

sublocale network: Graph_Defs "\<lambda> (L, s, u) (L', s', u'). conv N \<turnstile>\<^sub>n \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" .

term a\<^sub>0

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
  ) ((init, s\<^sub>0), u\<^sub>0)" if "\<forall> c \<in> {1..m}. u\<^sub>0 c = 0"
proof -
  show ?thesis
    apply (subst models_alt_def)
    subgoal
      sorry
    subgoal
      sorry
    subgoal
      by blast
     apply (cases \<Phi>)
  using [[goals_limit=1]]
    subgoal for \<phi>
    using prod_conv p_p p_gt_0
    by (fastforce simp: product'.prod_reachable_correct[symmetric, simplified])
      apply simp
  sorry
qed

(* XXX *)
lemma init_state_in_state_set:
  "(init, s\<^sub>0) \<in> Normalized_Zone_Semantics_Impl_Refine.state_set (trans_of A)"
  sorry

(* XXX Remove less general versions *)
lemma final_fun_final':
  "((\<lambda> (L, s). P L s), (\<lambda> (L, s). P L s)) \<in> inv_rel states'" for P
  unfolding F_def final_fun_def inv_rel_def in_set_member[symmetric] list_ex_iff
  by (force dest!: states'_states')

lemma final_fun_final[intro, simp]:
  "((\<lambda> (L, s). P L s), (\<lambda> (L, s). P L s)) \<in> inv_rel states" for P
  using final_fun_final' states_states' by (rule inv_rel_mono)

term "conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula"

lemma hn_refine_emp_neg_RES:
  assumes "hn_refine emp (f) emp bool_assn (RES Y)"
  shows "hn_refine emp (do {r \<leftarrow> f; return (\<not> r)}) emp bool_assn (RES {\<not> x | x. x \<in> Y})"
  using assms[unfolded hn_refine_def]
  by sepref_to_hoare sep_auto

lemma hfref_emp_neg_RES:
  assumes "(uncurry0 f, uncurry0 (RES Y)) \<in> (unit_assn, unit_assn) \<rightarrow>\<^sub>a bool_assn"
  shows "(uncurry0 (do {r \<leftarrow> f; return (\<not> r)}), uncurry0 (RES {\<not> x | x. x \<in> Y}))
  \<in> (unit_assn, unit_assn) \<rightarrow>\<^sub>a bool_assn"
  using assms[to_hnr]
  by (auto intro!: hfrefI hn_refine_emp_neg_RES simp: pure_unit_rel_eq_empty)

lemma hfref_emp_neg_RES':
  assumes "(uncurry0 f, uncurry0 (SPEC R)) \<in> (unit_assn, unit_assn) \<rightarrow>\<^sub>a bool_assn"
  shows "(uncurry0 (do {r \<leftarrow> f; return (\<not> r)}), uncurry0 (SPEC (R o Not)))
  \<in> (unit_assn, unit_assn) \<rightarrow>\<^sub>a bool_assn"
proof -
  have "(\<lambda>y. \<exists>x. y = (\<not> x) \<and> R x) = R o Not"
    apply (rule ext)
    apply simp
      subgoal for y
        apply (cases y)
         apply simp
        apply simp
        done
      done
  then show ?thesis
    using hfref_emp_neg_RES[OF assms]
    by auto
qed

lemma hn_refine_emp_return_neg_RES:
  assumes "hn_refine emp (return False) emp bool_assn (RES Y)"
  shows "hn_refine emp (return True) emp bool_assn (RES {\<not> x | x. x \<in> Y})"
  using hn_refine_emp_neg_RES[OF assms] by simp

lemma Alw_ev_bisim:
  "(\<exists>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<and>
                  \<not> Alw_ev (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s) ((init, s\<^sub>0), u\<^sub>0))
  = (\<forall>u\<^sub>0. (\<forall>c\<in>{Suc 0..m}. u\<^sub>0 c = 0) \<longrightarrow>
               \<not> Alw_ev (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s) ((init, s\<^sub>0), u\<^sub>0))"
  sorry

lemma maxiscope_impl:
  "(\<forall> a. P a \<longrightarrow> (\<forall> b. Q a b)) = (\<forall> b a. P a \<longrightarrow> Q a b)" for P Q
  by auto

theorem model_check':
  "(uncurry0 (model_checker TYPE('bb) TYPE('cc) TYPE('dd)),
    uncurry0 (
      SPEC (\<lambda> r.
        (\<forall>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock ((init, s\<^sub>0), u\<^sub>0)) \<longrightarrow>
        r = (\<forall> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<longrightarrow> conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula)
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
    "(\<lambda>(l, u). case l of (L, s) \<Rightarrow> check_bexp \<phi> L s) = (\<lambda>((L, s), _). check_bexp \<phi> L s)" for \<phi>
    by auto
  have ****: "{\<not> xa |xa. (\<not> xa) = x} = {x}" for x
    by auto

  show ?thesis
    using models_correct
    apply simp
    unfolding model_checker_def reachability_checker'_def Alw_ev_checker_def leadsto_checker_def
    apply (cases formula; simp)

      -- \<open>\<open>EX\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.pw_impl_hnr_F_reachable
      apply (subst (asm) F_reachable_correct_new)
        apply (rule prems; fail)
      apply auto
      sorry

        -- \<open>\<open>EG\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.Alw_ev_impl_hnr[OF init_state_in_state_set, where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd]
      unfolding final_fun_def F_def
      unfolding
        UPPAAL_Reachability_Problem_precompiled'.final_fun_def[
          OF UPPAAL_Reachability_Problem_precompiled'_axioms
          ]
        UPPAAL_Reachability_Problem_precompiled_defs.F_def
      unfolding prems(2)
      apply simp
      unfolding Refine_Basic.RETURN_def **
      by (auto 4 2 simp add: pure_unit_rel_eq_empty Alw_ev_bisim intro: hn_refine_ref hfrefI)

        -- \<open>\<open>AX\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.Alw_ev_impl_hnr[OF init_state_in_state_set, where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd]
      unfolding final_fun_def F_def
      unfolding UPPAAL_Reachability_Problem_precompiled_defs.F_def
      apply (subst
          UPPAAL_Reachability_Problem_precompiled'.final_fun_def[
            OF UPPAAL_Reachability_Problem_precompiled'_axioms
            ])
      apply (safe; clarsimp simp: prems(2))
      subgoal premises prems
        using prems(1)[unfolded *, THEN hfref_emp_neg_RES]
        by (simp add: RETURN_def disj_not1[symmetric])
      subgoal premises prems
        using prems(1)[unfolded *, THEN hfref_emp_neg_RES]
        by (simp add: RETURN_def disj_not1[symmetric])
      done

        -- \<open>\<open>AG\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.pw_impl_hnr_F_reachable
      apply (subst (asm) F_reachable_correct_new')
        apply (rule prems; fail)
      apply auto
      subgoal premises prems
        using prems(1)[unfolded * RETURN_def, THEN hfref_emp_neg_RES]
        apply (simp add: RETURN_def)
        apply (simp only: maxiscope_impl)
          -- "We also need bisimilarity here."
        sorry
      done

        -- \<open>\<open>Leadsto\<close>\<close>
    subgoal premises prems for \<phi> \<psi>
      using impl.leadsto_impl_hnr[
          OF final_fun_final init_state_in_state_set, of "Not oo check_bexp \<psi>"
          ]
      unfolding * F_def
      by (auto simp: prems(2) *** dest: hfref_emp_neg_RES' simp: comp_def)
    done
qed

theorem model_check'_old:
  "(uncurry0 (model_checker TYPE('bb) TYPE('cc) TYPE('dd)),
    uncurry0 (
      Refine_Basic.RETURN (
        \<forall> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<longrightarrow> conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula
      )
    )
   )
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  if "\<forall>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock ((init, s\<^sub>0), u\<^sub>0)"
proof -
  have *: "(\<lambda>(l, u). \<not> (case l of (L, s) \<Rightarrow> (Not \<circ>\<circ>\<circ> check_bexp) \<phi> L s))
    = (\<lambda>((L, s), _). check_bexp \<phi> L s)" for \<phi>
    by auto
  have **:
    "(\<lambda>(l, u). \<not> (case l of (L, s) \<Rightarrow> check_bexp \<phi> L s)) = (\<lambda>((L, s), _). \<not> check_bexp \<phi> L s)"
    for \<phi> by auto
  have ***:
    "(\<lambda>(l, u). case l of (L, s) \<Rightarrow> check_bexp \<phi> L s) = (\<lambda>((L, s), _). check_bexp \<phi> L s)" for \<phi>
    by auto
  have ****: "{\<not> xa |xa. (\<not> xa) = x} = {x}" for x
    by auto

  show ?thesis
    using models_correct
    apply simp
    unfolding model_checker_def reachability_checker'_def Alw_ev_checker_def leadsto_checker_def
    apply (cases formula; simp)

      -- \<open>\<open>EX\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.pw_impl_hnr_F_reachable
      apply (subst (asm) F_reachable_correct_new)
        apply (rule prems; fail)
      apply auto
      sorry

        -- \<open>\<open>EG\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.Alw_ev_impl_hnr[OF init_state_in_state_set, where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd]
      unfolding final_fun_def F_def
      unfolding
        UPPAAL_Reachability_Problem_precompiled'.final_fun_def[
          OF UPPAAL_Reachability_Problem_precompiled'_axioms
          ]
        UPPAAL_Reachability_Problem_precompiled_defs.F_def
      unfolding prems(2)
      apply simp
      unfolding Refine_Basic.RETURN_def **
      by (auto simp add: pure_unit_rel_eq_empty Alw_ev_bisim intro: hn_refine_ref hfrefI)

        -- \<open>\<open>AX\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.Alw_ev_impl_hnr[OF init_state_in_state_set, where 'bb = 'bb and 'cc = 'cc and 'dd = 'dd]
      unfolding final_fun_def F_def
      unfolding UPPAAL_Reachability_Problem_precompiled_defs.F_def
      apply (subst
          UPPAAL_Reachability_Problem_precompiled'.final_fun_def[
            OF UPPAAL_Reachability_Problem_precompiled'_axioms
            ])
      apply (safe; clarsimp simp: prems(2))
      subgoal premises prems
        using prems(1)[unfolded *, THEN hfref_emp_neg_RES]
        by (simp add: RETURN_def disj_not1[symmetric])
      subgoal premises prems
        using prems(1)[unfolded *, THEN hfref_emp_neg_RES]
        by (simp add: RETURN_def disj_not1[symmetric])
      done

        -- \<open>\<open>AG\<close>\<close>
    subgoal premises prems for \<phi>
      using impl.pw_impl_hnr_F_reachable
      apply (subst (asm) F_reachable_correct_new')
        apply (rule prems; fail)
      apply auto
      subgoal premises prems
        using prems(1)[unfolded * RETURN_def, THEN hfref_emp_neg_RES]
        apply (simp add: RETURN_def)
        apply (simp only: maxiscope_impl)
          -- "We also need bisimilarity here."
        sorry
      done

        -- \<open>\<open>Leadsto\<close>\<close>
    subgoal premises prems for \<phi> \<psi>
      using impl.leadsto_impl_hnr[
          OF final_fun_final init_state_in_state_set that(1), of "Not oo check_bexp \<psi>"
          ]
      unfolding * F_def
      by (auto simp: prems(2) RETURN_def *** **** dest: hfref_emp_neg_RES)
    done
qed

theorem model_check'_hoare:
  "<emp>
    model_checker TYPE('bb) TYPE('cc) TYPE('dd)
  <\<lambda>r. \<up> ((\<forall>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> deadlock ((init, s\<^sub>0), u\<^sub>0)) \<longrightarrow> r = (
    (\<forall> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<longrightarrow> conv N,(init, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula)
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

thm model_checker_def[unfolded
  reachability_checker'_alt_def Alw_ev_checker_alt_def leadsto_checker_alt_def
]

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

thm reachability_checker'_def Alw_ev_checker_def leadsto_checker_def

context UPPAAL_Reachability_Problem_precompiled'
begin

lemmas model_checker_def_refined = model_checker_def[unfolded
    reachability_checker'.refine[OF UPPAAL_Reachability_Problem_precompiled'_axioms]
    Alw_ev_checker.refine[OF UPPAAL_Reachability_Problem_precompiled'_axioms]
    leadsto_checker.refine[OF UPPAAL_Reachability_Problem_precompiled'_axioms]
  ]

thm model_checker_def_refined

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
    then (\<forall>u\<^sub>0. (\<forall>c\<in>{1..m}. u\<^sub>0 c = 0) \<longrightarrow> \<not> Graph_Defs.deadlock
          (\<lambda>(l, u) (l', u').
              (case Prod_TA_Defs.prod_ta
                     (Equiv_TA_Defs.state_ta
                       (N p I P T prog bounds) max_steps) of
               (T, I) \<Rightarrow>
                 ((\<lambda>(l, g, a, r, l').
                      (l, map conv_ac g, a, r, l')) `
                  T,
                  map conv_ac \<circ> I)) \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>)
          ((UPPAAL_Reachability_Problem_precompiled_defs.init
             p,
            s\<^sub>0),
           u\<^sub>0)) \<longrightarrow>
      r = Some (
        \<forall> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<longrightarrow>
        conv (N p I P T prog bounds),(repeat 0 p, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula
      )
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
      \<forall> u\<^sub>0. (\<forall> c \<in> {1..m}. u\<^sub>0 c = 0) \<longrightarrow>
        A,(repeat 0 p, s\<^sub>0, u\<^sub>0) \<Turnstile>\<^sub>max_steps formula"
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

(*
export_code
  precond_mc Pure.type init_pred_check time_indep_check1 time_indep_check1 conjunction_check2
  checking SML_imp
*)

end (* Theory *)