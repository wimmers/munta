theory Generalized_Network_Language
  imports Main
    Networks.State_Networks
    Uppaal_Networks.UPPAAL_State_Networks_Impl
    FinFun.FinFun
    Simple_Network_Language
begin

notation (input) TAG ("_ \<bbar> _" [40, 40] 41)

section \<open>Simple networks of automata with synchronization vectors and committed locations\<close>

text \<open>This is a generalization of the previous formalism with synchronization vectors in the style
of \<^emph>\<open>TChecker\<close>, see \<^url>\<open>https://github.com/fredher/tchecker/blob/master/doc/file-format.md\<close>.\<close>

\<comment> \<open>An action can have a communication purpose (synchronization) or be silent.\<close>
datatype 'a act = Com 'a | Sil 'a

text \<open>A single synchronization vector has the form \<open>sync:P1@a:P2@b:P3@c?:P4@d?\<close>
in TChecker's syntax, specifying that \<open>P1\<close> and \<open>P2\<close> \<^emph>\<open>need\<close> to synchronize on \<open>a\<close> and \<open>b\<close>,
respectively, while \<open>P3\<close> and \<open>P4\<close> \<^emph>\<open>will\<close> synchronize on \<open>c\<close> and \<open>d\<close> if they can
(\<^emph>\<open>weak\<close> synchronization constraint).
The order of processes in the synchronization specifies the order of updates.
Therefore we end up with the following type definition:\<close>
type_synonym 'a sync = "(nat \<times> 'a \<times> bool) list"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) nta = "'a sync set \<times> ('a act, 's, 'c, 't, 'x, 'v) sta list \<times> ('x \<rightharpoonup> 'v * 'v)"

context begin

qualified definition conv_t where "conv_t \<equiv> \<lambda> (l,b,g,a,f,r,l'). (l,b,conv_cc g,a,f,r,l')"

qualified definition conv_A where "conv_A \<equiv> \<lambda> (C, U, T, I). (C, U, conv_t ` T, conv_cc o I)"

definition conv where
  "conv \<equiv> \<lambda>(broadcast, automata, bounds). (broadcast, map conv_A automata, bounds)"

end

datatype 'b label = Del | Internal 'b | Sync "'b sync"

no_notation step_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
no_notation steps_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61, 61, 61,61,61] 61)
no_notation Simple_Network_Language.step_u ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)

inductive step_u ::
  "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval
  \<Rightarrow> 'a label \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
where
  step_t:
    "\<lbrakk>
      ''target invariant'' \<bar> \<forall>p < length N. u \<oplus> d \<turnstile> inv (N ! p) (L ! p);
      ''nonnegative''      \<bar> d \<ge> 0;
      ''urgent''           \<bar> (\<exists>p < length N. L ! p \<in> urgent (N ! p)) \<longrightarrow> d = 0;
      ''bounded''          \<bar> bounded B s
     \<rbrakk>
    \<Longrightarrow> (syncs, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L, s, u \<oplus> d\<rangle>" |
  step_int:
    "\<lbrakk>
      TRANS ''silent'' \<bar> (l, b, g, Sil a, f, r, l') \<in> trans (N ! p);
      ''committed'' \<bar> l \<in> committed (N ! p) \<or> (\<forall>p < length N. L ! p \<notin> committed (N ! p));
      ''bexp''      \<bar> check_bexp s b True;
      ''guard''     \<bar> u \<turnstile> g;
      ''target invariant'' \<bar> \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      ''loc''           \<bar> L!p = l;
      ''range''         \<bar> p < length L;
      ''new loc''       \<bar> L' = L[p := l'];
      ''new valuation'' \<bar> u' = [r\<rightarrow>0]u;
      ''is_upd''        \<bar> is_upd s f s';
      ''bounded''       \<bar> bounded B s'
    \<rbrakk>
    \<Longrightarrow> (syncs, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>" |
  step_sync:
    "\<lbrakk>
      ''sync'' \<bar> sync \<in> syncs;
      ''enabled'' \<bar> (\<forall>(p, a, b) \<in> set sync. b \<longrightarrow> p \<in> set ps);
      ''only syncs'' \<bar> (\<forall>p < length N. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps);
      ''actions'' \<bar> (\<forall>(p, a, _) \<in> set sync. as p = a);
      TRANS ''sync'' \<bar>
        (\<forall>p \<in> set ps. (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N ! p));
      ''committed'' \<bar> ((\<exists>p \<in> set ps. L ! p \<in> committed (N ! p))
      \<or> (\<forall>p < length N. L ! p \<notin> committed (N ! p)));
      ''bexp''    \<bar> \<forall>p \<in> set ps. check_bexp s (bs p) True;
      ''guard''   \<bar> \<forall>p \<in> set ps. u \<turnstile> gs p;
      ''maximal'' \<bar> \<forall>q < length N. q \<notin> set ps \<longrightarrow>
        (\<forall>a b g f r l'.
          (L!q, b, g, Com (as q), f, r, l') \<in> trans (N ! q) \<and> (q, a, False) \<in> set sync
          \<longrightarrow> \<not> check_bexp s b True \<or> \<not> u \<turnstile> g);
      ''target invariant'' \<bar> \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      SEL ''range''      \<bar> set ps \<subseteq> {0..<length N};
      SEL ''sublist'' \<bar> subseq ps (map fst sync);
      ''new loc'' \<bar> L' = fold (\<lambda>p L . L[p := ls' p]) ps L;
      ''new valuation'' \<bar> u' = [concat (map rs ps)\<rightarrow>0]u;
      ''upds''    \<bar> is_upds s (map fs ps) s';
      ''bounded'' \<bar> bounded B s'
    \<rbrakk>
    \<Longrightarrow> (syncs, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Sync sync\<^esub> \<langle>L', s', u'\<rangle>"
lemmas [intro?] = step_u.intros[unfolded TAG_def]
print_statement step_u.intros[unfolded TAG_def]
text \<open>Comments:
\<^item> Should there be an error transition + state if states run of bounds or updates are undefined?
Then one could run a reachability check for the error state.
\<^item> Should the state be total?
\<^item> Note that intermediate states are allowed to run out of bounds
\<^item> We do not explicitly enforce that the same process cannot appear multiple times in a sync
\<^item> We do not explicitly enforce that process and indices and actions names are valid in syncs
\<close>

definition steps_u ::
  "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval
  \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
where
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<equiv>
    (\<lambda> (L, s, u) (L', s', u'). \<exists>a. A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>)\<^sup>*\<^sup>* (L, s, u) (L', s', u')"

paragraph \<open>Misc\<close>

lemma clock_val_concat_iff:
  \<open>u \<turnstile> concat gs \<longleftrightarrow> (\<forall>g \<in> set gs. u \<turnstile> g)\<close>
  by (auto intro: guard_concat concat_guard)

lemma clock_val_append_iff:
  \<open>u \<turnstile> g1 @ g2 \<longleftrightarrow> u \<turnstile> g1 \<and> u \<turnstile> g2\<close>
proof -
  have "u \<turnstile> g1 @ g2 \<longleftrightarrow> u \<turnstile> concat [g1, g2]"
    by simp
  also have "... \<longleftrightarrow> u \<turnstile> g1 \<and> u \<turnstile> g2"
    unfolding clock_val_concat_iff by simp
  finally show ?thesis .
qed


subsection \<open>Product construction\<close>

locale Prod_TA_Defs =
  fixes A :: "('a, 's, 'c, 't, 'x, 'v :: linorder) nta"
begin

definition
  "syncs = fst A"

definition
  "N i = fst (snd A) ! i"

definition
  "bounds = snd (snd A)"

definition \<comment>\<open>Number of processes\<close>
  "n_ps = length (fst (snd A))"

definition states  :: "'s list set" where
  "states \<equiv> {L. length L = n_ps \<and>
    (\<forall> i. i < n_ps --> L ! i \<in> (\<Union> (l, e, g, a, r, u, l') \<in> (trans (N i)). {l, l'}))}"

definition
  "prod_inv \<equiv> \<lambda>(L, s). if L \<in> states then concat (map (\<lambda>i. inv (N i) (L ! i)) [0..<n_ps]) else []"

definition
  "trans_int =
    {((L, s), g, Internal a, r, (L', s')) | L s l b g f p a r l' L' s'.
      (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
      (l \<in> committed (N p) \<or> (\<forall>p < n_ps. L ! p \<notin> committed (N p))) \<and>
      L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and> check_bexp s b True \<and>
      L \<in> states \<and> bounded bounds s \<and> bounded bounds s'
    }"

definition trans_sync_tagged_def:
  "trans_sync =
    {((L, s), concat (map gs ps), Sync sync, concat (map rs ps), (L', s')) |
    sync L s L' s' bs gs as fs rs ls' ps.
      ''sync'' \<bbar> sync \<in> syncs \<and>
      ''enabled'' \<bbar> (\<forall>(p, a, b) \<in> set sync. b \<longrightarrow> p \<in> set ps) \<and>
      ''only syncs'' \<bbar> (\<forall>p < n_ps. p \<notin> fst ` set sync \<longrightarrow> p \<notin> set ps) \<and>
      ''actions'' \<bbar> (\<forall>(p, a, _) \<in> set sync. as p = a) \<and>
      TRANS ''sync'' \<bbar>
        (\<forall>p \<in> set ps. (L ! p, bs p, gs p, Com (as p), fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      ''committed'' \<bbar>
        ((\<exists>p \<in> set ps. L ! p \<in> committed (N p)) \<or> (\<forall>p < n_ps. L ! p \<notin> committed (N p))) \<and>
      ''maximal'' \<bbar> (\<forall>q < n_ps. q \<notin> set ps \<longrightarrow>
        \<not> (\<exists>b g a f r l'.
            (L!q, b, g, Com a, f, r, l') \<in> trans (N q) \<and> (q, a, False) \<in> set sync
          \<and> check_bexp s b True)) \<and>
      SEL ''range'' \<bbar> set ps \<subseteq> {0..<n_ps} \<and> SEL ''sublist'' \<bbar> subseq ps (map fst sync) \<and>
      ''bexp'' \<bbar> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
      ''new loc'' \<bbar> L' = fold (\<lambda>p L . L[p := ls' p]) ps L \<and>
      ''upds''    \<bbar> is_upds s (map fs ps) s' \<and>
      L \<in> states \<and> ''bounded'' \<bbar> bounded bounds s \<and> ''bounded'' \<bbar> bounded bounds s'
    }"

lemmas trans_sync_def = trans_sync_tagged_def[unfolded TAG_def]

definition
  "trans_prod = trans_int \<union> trans_sync"

definition
  "prod_ta = (trans_prod, prod_inv :: ('s list \<times> ('x \<Rightarrow> 'v option) \<Rightarrow> _))"

lemma inv_of_prod[simp]:
  "inv_of prod_ta = prod_inv"
  unfolding prod_ta_def inv_of_def by simp

lemma trans_of_prod[simp]:
  "trans_of prod_ta = trans_prod"
  unfolding prod_ta_def trans_of_def by simp

lemma A_split:
  \<open>A = (syncs, map N [0..<n_ps], bounds)\<close>
  unfolding syncs_def N_def bounds_def n_ps_def by (cases A) (simp add: List.map_nth)

lemma map_N_n_ps_simp:
  "map N [0..<n_ps] ! p = N p"
  unfolding N_def n_ps_def List.map_nth ..

lemma N_split_simp[simp]:
  assumes "A = (broadcast', N', B)"
  shows "N' ! i = N i"
  unfolding N_def unfolding assms by simp

lemma state_preservation_updI:
  assumes "l' \<in> (\<Union> (l, b, g, a, r, u, l') \<in> trans (N p). {l, l'})" "L \<in> states"
  shows "L[p := l'] \<in> states"
  using assms unfolding states_def by (fastforce simp: nth_list_update')

lemma state_preservation_fold_updI:
  assumes "\<forall>p \<in> set ps. ls' p \<in> (\<Union> (l, b, g, a, r, u, l') \<in> trans (N p). {l, l'})" "L \<in> states"
  shows "fold (\<lambda>p L. L[p := ls' p]) ps L \<in> states"
  using assms by (induction ps arbitrary: L) (auto intro: state_preservation_updI)

lemma state_set_states:
  "Simulation_Graphs_TA.state_set prod_ta \<subseteq> {(l, s). l \<in> states}"
  unfolding prod_ta_def state_set_def
  unfolding trans_of_def trans_prod_def
  unfolding trans_int_def trans_sync_def
  by (clarsimp, safe) (auto intro!: state_preservation_updI state_preservation_fold_updI)

lemma trans_prod_bounded_inv:
  \<open>bounded bounds s'\<close> if \<open>((L, s), g, a, r, (L', s')) \<in> trans_prod\<close>
  using that unfolding bounds_def trans_prod_def trans_int_def trans_sync_def
  by (auto simp: bounds_def)

lemma trans_prod_states_inv:
  \<open>L' \<in> states\<close> if \<open>((L, s), g, a, r, (L', s')) \<in> trans_prod\<close> \<open>L \<in> states\<close>
  using that
  unfolding bounds_def trans_prod_def trans_int_def trans_sync_def
  by (auto intro!: state_preservation_fold_updI state_preservation_updI)

end (* Prod TA Defs *)


locale Prod_TA_sem =
  Prod_TA_Defs A for A :: "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta"
begin

lemma prod_invI[intro]:
  \<open>u \<turnstile> prod_inv (L, s)\<close> if \<open>\<forall>p<n_ps. u \<turnstile> inv (N p) (L ! p)\<close>
  using that unfolding prod_inv_def by (auto intro!: guard_concat)

lemma prod_invD[dest]:
  \<open>\<forall>p<n_ps. u \<turnstile> inv (N p) (L ! p)\<close> if \<open>u \<turnstile> prod_inv (L, s)\<close> \<open>L \<in> states\<close>
  using that unfolding prod_inv_def by (auto elim: concat_guard)

lemma delay_sound:
  assumes "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>(L', s'), u'\<rangle>" "L \<in> states" "bounded bounds s"
          "\<forall>N \<in> set (fst (snd A)). urgent N = {}"
        shows "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
proof -
  from assms(4) have "l \<notin> urgent (N p)" if "p < n_ps" for p l
    using that unfolding N_def n_ps_def by auto
  then show ?thesis
    by (subst A_split) (use assms in \<open>cases, auto intro!: step_t simp: TAG_def\<close>)
qed

lemma action_sound:
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>" if "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>"
  using that
proof cases
  case prems: (1 g r)
  note [simp add] = map_N_n_ps_simp clock_val_append_iff clock_val_concat_iff
  from \<open>prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (L', s')\<close>[THEN state_setI2] have "L' \<in> states"
    using state_set_states that by fast
  from \<open>prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (L', s')\<close> show ?thesis
    unfolding trans_of_prod trans_prod_def
  proof safe
    assume "((L, s), g, a, r, L', s') \<in> trans_int"
    then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      unfolding trans_int_def
      apply clarsimp
      using prems \<open>L' \<in> _\<close>
      by (subst A_split) (intro step_int; simp add: TAG_def; elim prod_invD; assumption)
  next
    assume "((L, s), g, a, r, L', s') \<in> trans_sync"
    then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      using prems \<open>L' \<in> _\<close>
      unfolding trans_sync_def inv_of_prod
      apply clarsimp
      apply (subst A_split)
      apply standard
               apply (assumption | simp; elim prod_invD; assumption | simp; fast)+
      done
  qed
qed

lemma bounded_inv:
  \<open>bounded bounds s'\<close> if \<open>A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close>
  using that unfolding bounds_def by (cases; untag; simp)

lemma states_inv:
  \<open>L' \<in> states\<close> if \<open>A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close> \<open>L \<in> states\<close>
  using that unfolding bounds_def
proof cases
  case (step_t N d B broadcast)
  with \<open>L \<in> states\<close> show ?thesis
    by simp
next
  case prems[tagged, unfolded TAG_def]: (step_int l b g a f r l' N' p B syncs)
  from \<open>A = _\<close> have "l' \<in> (\<Union> (l, b, g, a, r, u, l') \<in> trans (N p). {l, l'})"
    usingT \<open>TRANS _\<close> by force
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI)
next
  case prems[tagged, unfolded TAG_def]: (step_sync sync syncs ps N' as bs gs fs rs ls' B)
  from \<open>A = _\<close> prems(6) have
    "\<forall> q \<in> set ps. ls' q \<in> (\<Union> (l, b, g, a, r, u, l') \<in> trans (N q). {l, l'})"
    usingT \<open>TRANS _\<close> by force
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI state_preservation_fold_updI)
qed

end (* Prod TA Defs on a time domain *)


locale Prod_TA =
  Prod_TA_sem A for A :: "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta" +
  assumes weak_synchronizations_unguarded:
    "\<forall>p < n_ps. \<forall>sync l b g a f r l'.
      sync \<in> syncs \<and> (l, b, g, Com a, f, r, l') \<in> trans (N p) \<and> (p, a, False) \<in> set sync \<longrightarrow> g = []"
begin

lemma action_complete:
  "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>"
  if "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>" "a \<noteq> Del" "L \<in> states" "bounded bounds s"
using that(1) proof cases
  case (step_t N d B broadcast)
  then show ?thesis
    using that(2) by auto
next
  case prems[tagged, unfolded TAG_def]: (step_int l b g a' f r l' N' p B syncs')
  have [simp]:
    "B = bounds" "syncs' = syncs" "length N' = n_ps"
    unfolding bounds_def syncs_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,Internal a',r\<^esup> (L', s')"
  proof -
    from prems \<open>L \<in> states\<close> \<open>bounded _ s\<close> have "((L, s),g,Internal a',r,(L', s')) \<in> trans_int"
      unfolding trans_int_def by simp (rule exI conjI HOL.refl | assumption | (simp; fail))+
    then show ?thesis
      unfolding prod_ta_def trans_of_def trans_prod_def by simp
  qed
  moreover have "u \<turnstile> g"
    usingT \<open>''guard''\<close> .
  moreover have "u' \<turnstile> inv_of prod_ta (L', s')"
    usingT \<open>''target invariant''\<close> by auto
  moreover have "u' = [r\<rightarrow>0]u"
    usingT \<open>''new valuation''\<close> .
  ultimately show ?thesis
    unfolding \<open>a = _\<close> ..
next
  case prems[tagged, unfolded TAG_def]: (step_sync sync syncs' ps N' as bs gs fs rs ls' B)
  have [simp]:
    "B = bounds" "syncs' = syncs" "length N' = n_ps"
    unfolding bounds_def syncs_def n_ps_def unfolding \<open>A = _\<close> by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding \<open>A = _\<close> by simp
  let ?r = "concat (map rs ps)" and ?g = "concat (map gs ps)"
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>?g,Sync sync,?r\<^esup> (L', s')"
  proof -
    have *: "\<not> u \<turnstile> g \<longleftrightarrow> False" if
      "p < n_ps" "(l, b, g, Com (as p), f, r, l') \<in> trans (N p)"
      "(p, a', False) \<in> set sync"
      for l b g a' f r l' p
    proof -
      from that have "as p = a'"
        usingT \<open>''actions''\<close> by auto
      with that weak_synchronizations_unguarded \<open>sync \<in> _\<close> show ?thesis
        by fastforce
    qed
    from prems \<open>L \<in> states\<close> \<open>bounded bounds s\<close> have "((L, s),?g,Sync sync,?r,(L', s')) \<in> trans_sync"
      unfolding trans_sync_def using * by clarsimp (intro exI conjI HOL.refl; fast)
   then show ?thesis
      unfolding prod_ta_def trans_of_def trans_prod_def by simp
  qed
  moreover have "u \<turnstile> ?g"
    usingT \<open>''guard''\<close> by (intro guard_concat) simp
  moreover have "u' \<turnstile> inv_of prod_ta (L', s')"
    usingT \<open>''target invariant''\<close> by auto
  moreover have "u' = [?r\<rightarrow>0]u"
    usingT \<open>''new valuation''\<close> .
  ultimately show ?thesis
    unfolding \<open>a = _\<close> ..
qed

lemma delay_complete:
  assumes "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  obtains d where "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>(L', s'), u'\<rangle>"
  using assms
proof cases
  case prems: (step_t N' d B broadcast)
  have [simp]:
    "length N' = n_ps"
    unfolding n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  from prems show ?thesis
  by (intro that[of d]; unfold \<open>u' = _\<close> \<open>L' = L\<close> \<open>s' = s\<close> TAG_def)
     (rule step_t.intros; (unfold inv_of_prod; rule prod_invI)?; simp)
qed

lemma step_iff:
  "(\<exists> a. A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>) \<longleftrightarrow> prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  if "bounded bounds s" "L \<in> states" "\<forall>N \<in> set (fst (snd A)). urgent N = {}"
  using that(1,2)
  apply (auto intro: action_sound delay_sound[OF _ _ _ that(3)])
  subgoal for a
    by (cases a; blast dest: action_complete elim: delay_complete)
  done

end (* Prod TA *)

end (* Theory *)