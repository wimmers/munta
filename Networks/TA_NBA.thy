theory TA_NBA
  imports Transition_Systems_and_Automata.NBA TA.Timed_Automata
begin

locale TA_NBA_Product_Defs =
  fixes A :: "('a, 'c, 't, 'l) ta" and label :: "'l \<Rightarrow> 'p" and l\<^sub>0 :: 'l
    and B :: "('p, 's) nba"
begin

definition inv :: "'l \<times> 's \<Rightarrow> ('c, 't) cconstraint" where
  "inv \<equiv> \<lambda>(l, _). inv_of A l"

definition trans :: "('a, 'c, 't, 'l \<times> 's) transition set" where
  "trans \<equiv> {((l, q), g, a, r, (l', q')). (l, g, a, r, l') \<in> trans_of A \<and> q' \<in> succ B (label l') q}"

definition prod :: "('a, 'c, 't, 'l \<times> 's) ta" where
  "prod \<equiv> (trans, inv)"

definition inits where
  "inits \<equiv> {q. \<exists>q\<^sub>0 \<in> initial B. q \<in> succ B (label l\<^sub>0) q\<^sub>0}"

definition accept where
  "accept \<equiv> \<lambda>((l, q), u). accepting B q"

end


locale TA_NBA_Product =
  TA_NBA_Product_Defs where A = A and B = B
  for A :: "('a, 'c, 't :: time, 'l) ta" and B :: "('p, 's) nba" +
  assumes labels_alphabet: "range label \<subseteq> alphabet B"
begin

sublocale A: Graph_Defs where
  E = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" .

sublocale prod: Graph_Defs
  "\<lambda>(l, u) (l', u'). prod \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>" .

lemma prod_step'_iff:
  "prod \<turnstile>' \<langle>(l, q), u\<rangle> \<rightarrow> \<langle>(l', q'), u'\<rangle> \<longleftrightarrow> A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle> \<and> q' \<in> succ B (label l') q"
  by (auto
        intro!: step'.intros step_t.intros step_a.intros
        elim!: step'.cases step_t.cases step_a.cases
        simp: inv_of_def trans_of_def prod_def trans_def inv_def)

lemma prod_run_A_run:
  "A.run (smap (\<lambda>((l, q), u). (l, u)) xs)" (is "A.run ?xs1") if "prod.run xs"
proof -
  interpret Simulation
    where A = "\<lambda>(l, u) (l', u'). prod \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
      and B = "\<lambda>(l, u) (l', u'). A \<turnstile>' \<langle>l, u\<rangle> \<rightarrow> \<langle>l', u'\<rangle>"
    and sim = "\<lambda>((l, q), u) (l', u'). l = l' \<and> u = u'"
    by standard (auto simp: prod_step'_iff)
  obtain y ys where "xs = y ## ys"
    by (cases xs)
  obtain l q u where "y = ((l, q), u)"
    by (metis surj_pair)
  from simulation_run[OF that[unfolded \<open>xs = _\<close> \<open>y = _\<close>], of "(l, u)", simplified] obtain zs where
    "A.run ((l, u) ## zs)" "stream_all2 (\<lambda>((l, q), u) (l', u'). l = l' \<and> u = u') ys zs"
    by safe
  from this(2) have "?xs1 = (l, u) ## zs"
    unfolding \<open>xs = _\<close> \<open>y = _\<close>
    by simp (coinduction arbitrary: ys zs, auto 4 3 simp: stream_all2_SCons2)
  with \<open>A.run _\<close> show ?thesis
    by metis
qed

lemma prod_run_iff:
  fixes q\<^sub>0'
  assumes "q \<in> succ B (label l) q\<^sub>0'"
  shows
  "prod.run (((l, q), u) ## xs)
     \<longleftrightarrow> A.run (smap (\<lambda>((l, q), u). (l, u)) (((l, q), u) ## xs))
       \<and> run B (smap (\<lambda>((l, q), u). (label l, q)) (((l, q), u) ## xs)) q\<^sub>0'"
  (is "prod.run ?xs \<longleftrightarrow> A.run (smap ?p1 ?xs) \<and> run B (smap ?p2 ?xs) q\<^sub>0'")
proof -
  have *: "q' \<in> succ B (label l') q" if "prod \<turnstile>' \<langle>(l, q), u\<rangle> \<rightarrow> \<langle>(l', q'), u'\<rangle>" for l q u l' q' u'
    using that by (simp add: prod_step'_iff)
  have "run B (smap ?p2 ?xs) q\<^sub>0'" if "prod.run (((l, q), u) ## xs)"
    using that assms labels_alphabet
    by (coinduction arbitrary: xs l q u q\<^sub>0' rule: nba.run_coinduct)
       (simp split: prod.splits, erule prod.run.cases, auto dest!: * split: prod.splits)
  moreover have "prod.run xs"
    if "A.run (smap ?p1 xs)" "run B (smap ?p2 xs) q\<^sub>0'" for xs
    using that
    apply (coinduction arbitrary: xs q\<^sub>0')
    subgoal for xs q\<^sub>0'
      apply (cases xs)
      subgoal for _ ys
        by (cases ys) (auto simp: prod_step'_iff elim: A.run.cases split: prod.splits)
      done
    done
  ultimately show ?thesis
    using prod_run_A_run by metis
qed

lemma prod_Buechi_run_iff:
  "(\<exists>q \<in> inits. \<exists>xs. prod.run (((l\<^sub>0, q), u) ## xs) \<and> infs accept (((l\<^sub>0, q), u) ## xs))
  \<longleftrightarrow> (\<exists>xs. A.run ((l\<^sub>0, u) ## xs) \<and> label l\<^sub>0 ## smap (\<lambda>(l, u). label l) xs \<in> language B)"
  (is "?l \<longleftrightarrow> ?r")
proof -
  have ?l if ?r
  proof -
    from that obtain xs ys q\<^sub>0 q\<^sub>0' where run:
      "A.run ((l\<^sub>0, u) ## xs)"
      "q\<^sub>0 \<in> initial B"
      "infs (accepting B)
       (trace (smap (\<lambda>(l, u). label l) xs ||| ys) q\<^sub>0')"
      "run B (smap (\<lambda>(l, u). label l) xs ||| ys) q\<^sub>0'"
      "label l\<^sub>0 \<in> alphabet B" "q\<^sub>0' \<in> succ B (label l\<^sub>0) q\<^sub>0"
      unfolding language_def by safe (erule nba.run.cases, auto)
    let ?xs = "smap (\<lambda>((l, u), q). ((l, q), u)) (xs ||| ys)"
    have "smap (\<lambda>((l, q), u). (label l, q)) ?xs = smap (\<lambda>(l, u). label l) xs ||| ys"
      by (coinduction arbitrary: xs ys) (auto split: prod.splits)
    moreover have "smap (case_prod (\<lambda>(l, q). Pair l)) ?xs = xs"
      by (coinduction arbitrary: xs ys) auto
    ultimately have "prod.run (((l\<^sub>0, q\<^sub>0'), u) ## ?xs)"
      using run unfolding prod_run_iff[OF \<open>q\<^sub>0' \<in> _\<close>] by auto
    moreover have "infs accept (((l\<^sub>0, q\<^sub>0'), u) ## ?xs)"
    proof -
      have "stream_all2 (\<lambda>a b. snd b = a) ys (xs ||| ys)"
        by (coinduction arbitrary: xs ys) auto
      then show ?thesis
        using run(3) unfolding accept_def trace_alt_def by (auto elim: alw_ev_lockstep)
    qed
    ultimately show ?thesis
      using \<open>q\<^sub>0' \<in> _\<close> \<open>q\<^sub>0 \<in> _\<close> unfolding inits_def by blast
  qed
  moreover have ?r if ?l
  proof -
    let ?r = "smap (\<lambda>((l, q), u). q)"
    from that obtain q\<^sub>0' q\<^sub>0 xs where
      "q\<^sub>0 \<in> initial B" "q\<^sub>0' \<in> succ B (label l\<^sub>0) q\<^sub>0" "prod.run (((l\<^sub>0, q\<^sub>0'), u) ## xs)" "infs accept xs"
      unfolding inits_def by safe
    moreover have "smap (\<lambda>((l, q), u). (label l, q)) xs = (smap (\<lambda>(l, u). label l)
        (smap (\<lambda>((l, q), u). (l, u)) xs) ||| ?r xs)"
      by (coinduction arbitrary: xs) (auto split: prod.splits)
    ultimately show ?thesis
      by (subst (asm) prod_run_iff)
         (auto 4 4
          simp: holds.simps trace_alt_def accept_def 
          elim!: alw_ev_mono language[where r = "q\<^sub>0' ## ?r xs"])
  qed
  ultimately show ?thesis
    by blast
qed

end

end