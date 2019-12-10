theory TA_NBA
  imports Transition_Systems_and_Automata.NBA TA.Timed_Automata TA_Library.Temporal_Logics
    \<comment> \<open>"LTL_to_GBA.LTL_to_GBA"\<close>
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



locale TA_NBA_LTL_Product1 =
  TA_NBA_Product where A = A and B = B
  for A :: "('a, 'c, 't :: time, 'l) ta" and B :: "('p, 's) nba" +
  fixes \<phi> :: "('l \<Rightarrow> bool) ltlc"
  assumes B_\<phi>: "language B = smap label ` {xs. Graph_Defs.models_ltlc \<phi> xs}"
      and label_formula_compatible: "\<And>xs ys. smap label xs = smap label ys
    \<Longrightarrow> Graph_Defs.models_ltlc \<phi> xs \<longleftrightarrow> Graph_Defs.models_ltlc \<phi> ys"
begin

lemma smap_project:
  "smap (\<lambda>(l, u). label l) xs = smap label (smap fst xs)"
  by (coinduction arbitrary: xs) (auto split: prod.split)

theorem
  "(\<exists>q \<in> inits. \<exists>xs. prod.run (((l\<^sub>0, q), u) ## xs) \<and> infs accept (((l\<^sub>0, q), u) ## xs))
\<longleftrightarrow> (\<exists>xs. A.run ((l\<^sub>0, u) ## xs) \<and> Graph_Defs.models_ltlc \<phi> (l\<^sub>0 ## smap fst xs))"
  unfolding prod_Buechi_run_iff B_\<phi>
  apply safe
  subgoal for xs ys
    apply (intro exI conjI)
     apply assumption
    apply (subst label_formula_compatible)
     apply (auto simp add: smap_project)
    done
  apply (force simp: smap_project)
  done

end

locale TA_NBA_LTL_Product2 =
  TA_NBA_Product where A = A and B = B
  for A :: "('a, 'c, 't :: time, 'l) ta" and B :: "('p, 's) nba" +
  fixes \<phi> :: "('l \<Rightarrow> bool) ltlc" and \<psi> :: "('p \<Rightarrow> bool) ltlc"
  assumes B_\<phi>: "language B = {xs. Graph_Defs.models_ltlc \<psi> xs}"
      and label_formula_compatible:
      "\<And>xs. Graph_Defs.models_ltlc \<phi> xs \<longleftrightarrow> Graph_Defs.models_ltlc \<psi> (smap label xs)"
begin

lemma smap_project:
  "smap (\<lambda>(l, u). label l) xs = smap label (smap fst xs)"
  by (coinduction arbitrary: xs) (auto split: prod.split)

theorem
  "(\<exists>q \<in> inits. \<exists>xs. prod.run (((l\<^sub>0, q), u) ## xs) \<and> infs accept (((l\<^sub>0, q), u) ## xs))
\<longleftrightarrow> (\<exists>xs. A.run ((l\<^sub>0, u) ## xs) \<and> Graph_Defs.models_ltlc \<phi> (l\<^sub>0 ## smap fst xs))"
  unfolding prod_Buechi_run_iff B_\<phi> by (auto simp: label_formula_compatible smap_project)

end

context
  fixes \<phi> :: "'a ltlc" and f :: "'a \<Rightarrow> 'p" and interp :: "'a \<Rightarrow> ('l \<Rightarrow> bool)"
begin

lemma semantics_ltlc_map_prop:
  "(\<lambda>i. {a \<in> interp ` atoms_ltlc \<phi>. a (w i)}) \<Turnstile>\<^sub>c map_ltlc interp \<phi> \<longleftrightarrow>
   (\<lambda>i. {a \<in> atoms_ltlc \<phi>. interp a (w i)}) \<Turnstile>\<^sub>c \<phi>"
proof -
  have [simp]:
    "(\<lambda>i. {a. (a \<in> atoms_ltlc \<phi>1 \<or> a \<in> atoms_ltlc \<phi>2) \<and> interp a (w i)}) \<Turnstile>\<^sub>c \<phi>1
    \<longleftrightarrow> ((\<lambda>i. {a \<in> atoms_ltlc \<phi>1. interp a (w i)}) \<Turnstile>\<^sub>c \<phi>1)"
    "(\<lambda>i. {a. (a \<in> atoms_ltlc \<phi>1 \<or> a \<in> atoms_ltlc \<phi>2) \<and> interp a (w i)}) \<Turnstile>\<^sub>c \<phi>2
    \<longleftrightarrow> ((\<lambda>i. {a \<in> atoms_ltlc \<phi>2. interp a (w i)}) \<Turnstile>\<^sub>c \<phi>2)" for w \<phi>1 \<phi>2
    by (rule ltlc_eq_on; auto simp: pw_eq_on_def)+
  have [simp]:
    "(\<lambda>i. {a \<in> interp ` (atoms_ltlc \<phi>1 \<union> atoms_ltlc \<phi>2). a (w i)}) \<Turnstile>\<^sub>c map_ltlc interp \<phi>1
    \<longleftrightarrow> (\<lambda>i. {a \<in> interp ` atoms_ltlc \<phi>1. a (w i)}) \<Turnstile>\<^sub>c map_ltlc interp \<phi>1"
    "(\<lambda>i. {a \<in> interp ` (atoms_ltlc \<phi>1 \<union> atoms_ltlc \<phi>2). a (w i)}) \<Turnstile>\<^sub>c map_ltlc interp \<phi>2
    \<longleftrightarrow> (\<lambda>i. {a \<in> interp ` atoms_ltlc \<phi>2. a (w i)}) \<Turnstile>\<^sub>c map_ltlc interp \<phi>2" for w \<phi>1 \<phi>2
    by (rule ltlc_eq_on; auto simp: pw_eq_on_def ltlc.set_map)+
  show ?thesis
    by (induction \<phi> arbitrary: w) (simp_all add: suffix_def)
qed

lemma prop_ltlc_abstract:
  assumes f_inj: "inj_on f (atoms_ltlc \<phi>)"
  shows
  "w \<Turnstile>\<^sub>c' map_ltlc interp \<phi> \<longleftrightarrow>
  ((\<lambda>s. f ` {a \<in> atoms_ltlc \<phi>. interp a s}) o w) \<Turnstile>\<^sub>c map_ltlc f \<phi>" (is "?l \<longleftrightarrow> ?r")
proof -
  have "?l \<longleftrightarrow> (\<lambda>i. {a \<in> atoms_ltlc \<phi>. interp a (w i)}) \<Turnstile>\<^sub>c \<phi>"
    by (simp add: semantics_ltlc'_semantics_ltlc_atoms_iff ltlc.set_map semantics_ltlc_map_prop)
  also have "\<dots> \<longleftrightarrow> ?r"
    by (subst map_semantics_ltlc_aux[OF f_inj]) (auto simp: comp_def)
  finally show ?thesis .
qed

end


locale TA_NBA_LTL_Product =
  TA_NBA_Product where A = A and B = B
  for A :: "('a, 'c, 't :: time, 'l) ta" and B :: "('p set, 's) nba" +
  fixes \<phi> :: "'x ltlc" and interp :: "'x \<Rightarrow> ('l \<Rightarrow> bool)" and f :: "'x \<Rightarrow> 'p"
  assumes B_\<phi>: "to_omega ` language B = {w. w \<Turnstile>\<^sub>c map_ltlc f \<phi>}"
      and f_inj: "inj_on f (atoms_ltlc \<phi>)"
      and label: "label s = f ` {a \<in> atoms_ltlc \<phi>. interp a s}"
begin

lemma smap_project:
  "smap (\<lambda>(l, u). label l) xs = smap label (smap fst xs)"
  by (coinduction arbitrary: xs) (auto split: prod.split)

lemma B_\<phi>':
  "language B = {w. to_omega w \<Turnstile>\<^sub>c map_ltlc f \<phi>}"
  using B_\<phi> by auto (metis in_image(1) mem_Collect_eq to_stream_to_omega)

lemma comp_to_omega_is_smap:
  "g o to_omega xs = to_omega (smap g xs)"
  unfolding to_omega_def comp_def by auto

theorem prod_formula_run_iff:
  "(\<exists>q \<in> inits. \<exists>xs. prod.run (((l\<^sub>0, q), u) ## xs) \<and> infs accept (((l\<^sub>0, q), u) ## xs))
\<longleftrightarrow> (\<exists>xs. A.run ((l\<^sub>0, u) ## xs) \<and> Graph_Defs.models_ltlc (map_ltlc interp \<phi>) (l\<^sub>0 ## smap fst xs))"
  unfolding prod_Buechi_run_iff Graph_Defs.models_ltlc_def B_\<phi>'
  by (simp add: prop_ltlc_abstract[OF f_inj] smap_project label[symmetric] comp_to_omega_is_smap)

end





context
  fixes \<phi> :: "('l \<Rightarrow> bool) ltlc" and f :: "('l \<Rightarrow> bool) \<Rightarrow> 'p"
  assumes f_inj: "inj_on f (atoms_ltlc \<phi>)"
begin

lemma
  "w \<Turnstile>\<^sub>c' \<phi> \<longleftrightarrow> (\<lambda>i. (\<lambda>s. f ` {a \<in> atoms_ltlc \<phi>. a s}) (w i)) \<Turnstile>\<^sub>c map_ltlc f \<phi>"
  using f_inj
  apply (subst semantics_ltlc'_semantics_ltlc_atoms_iff)
  apply (subst map_semantics_ltlc_aux[where f = f])
     apply auto
  done

end


context
  fixes collision sent :: "'l \<Rightarrow> bool"
begin

private definition
  "edges = (\<lambda>s n.
    if n = 0 then
      if collision s \<and> sent s then {0}
      else if collision s \<and> \<not> sent s then {0}
      else if \<not> collision s then {1}
      else {}
    else if n = 1 then
      if collision s \<and> sent s then {0}
      else if \<not> collision s then {1}
      else if collision s \<and> \<not> sent s then {2}
      else {}
    else if n = 2 then
      if sent s then {0}
      else {2}
    else {}
   )"

lemma edges_determ:
  "\<exists>x \<in> {0,1,2}. edges s l = {x}" if "l \<in> {0,1,2}"
  using that unfolding edges_def by auto

definition
  "not_fg_collision_impl_g_not_sent = nba
    UNIV {0,1,2} edges (\<lambda>l. l = 0)"

definition
  "formula = not\<^sub>c (F\<^sub>c (G\<^sub>c (prop\<^sub>c(collision) implies\<^sub>c G\<^sub>c (not\<^sub>c(prop\<^sub>c(sent))))))"

schematic_goal
  "formula = TT ?x"
  unfolding formula_def
  oops

lemma
  "\<xi> \<Turnstile>\<^sub>c' formula = \<xi> \<Turnstile>\<^sub>c' G\<^sub>c (F\<^sub>c (prop\<^sub>c(collision) and\<^sub>c F\<^sub>c (prop\<^sub>c(sent))))"
  unfolding semantics_ltlc'_semantics_ltlc_atoms_iff
  unfolding formula_def
  by simp

lemma
  "language not_fg_collision_impl_g_not_sent =
    {xs. Graph_Defs.models_ltlc formula xs}
"
  unfolding Graph_Defs.models_ltlc_def
  apply auto
  oops

end





end