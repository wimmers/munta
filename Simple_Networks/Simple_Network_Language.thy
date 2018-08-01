theory Simple_Network_Language
  imports Main "../Networks/State_Networks" "../Uppaal_Networks/UPPAAL_State_Networks_Impl" "../library/Explorer" FinFun.FinFun
begin

section \<open>Simple networks of automata with broadcast channels and commited locations\<close>

datatype ('a, 'b) bexp =
  not "('a, 'b) bexp" | "and" "('a, 'b) bexp" "('a, 'b) bexp" | or "('a, 'b) bexp" "('a, 'b) bexp" | imply "('a, 'b) bexp" "('a, 'b) bexp" | \<comment> \<open>Boolean connectives\<close>
  eq 'a 'b | \<comment> \<open>Does var i equal x?\<close>
  le 'a 'b |
  lt 'a 'b |
  ge 'a 'b |
  gt 'a 'b

inductive check_bexp :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> bool \<Rightarrow> bool" where
  "check_bexp s (not e) (\<not> b)" if "check_bexp s e b" |
  "check_bexp s (and e1 e2) (a \<and> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (or e1 e2) (a \<or> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (imply e1 e2) (a \<longrightarrow> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (eq i x) (x = v)" if "s i = Some v" |
  "check_bexp s (le i x) (v \<le> x)" if "s i = Some v" |
  "check_bexp s (lt i x) (v < x)" if "s i = Some v" |
  "check_bexp s (ge i x) (v \<ge> x)" if "s i = Some v" |
  "check_bexp s (gt i x) (v > x)" if "s i = Some v"

datatype ('a, 'b) exp = if_then_else "('a, 'b) bexp" "('a, 'b) exp" "('a, 'b) exp" | const 'b | var 'a

inductive is_val where
  "is_val s (const c) c"
| "is_val s (var x)   v" if "s x = Some v"
| "is_val s (if_then_else b e1 e2) (if bv then v1 else v2)" if "is_val s e1 v1" "is_val s e2 v2" "check_bexp s b bv"

type_synonym
  ('c, 't, 's) invassn = "'s \<Rightarrow> ('c, 't) cconstraint"

type_synonym
  ('a, 'b) upd = "('a * ('a, 'b) exp) list"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) transition = "'s \<times> ('c, 't) cconstraint \<times> 'a \<times> ('x, 'v) upd \<times> 'c list \<times> 's"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) sta = "'s set \<times> ('a, 's, 'c, 't, 'x, 'v) transition set \<times> ('c, 't, 's) invassn"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) nta = "'a set \<times> ('a act, 's, 'c, 't, 'x, 'v) sta list \<times> ('x \<Rightarrow> 'v * 'v)"

datatype 'b label = Del | Internal 'b | Bin 'b | Broad 'b

definition bounded where
  "bounded bounds s \<equiv> \<forall>x \<in> dom s. fst (bounds x) < the (s x) \<and> the (s x) < snd (bounds x)"

definition is_upd where
  "is_upd s upds s' \<equiv> \<exists>xs. list_all2 (\<lambda> (l1, r1) (l2, r2). l1 = l2 \<and> is_val s r1 r2) upds xs \<and> s' = fold (\<lambda> (l, r) s. s(l := Some r)) xs s"

inductive is_upds where
  "is_upds s [] s" |
  "is_upds s (x # xs) s''" if "is_upd s x s'" "is_upds s' xs s''"

abbreviation commited :: "('a, 's, 'c, 't, 'x, 'v) sta \<Rightarrow> 's set" where
  "commited A \<equiv> fst A"

abbreviation trans :: "('a, 's, 'c, 't, 'x, 'v) sta \<Rightarrow> ('a, 's, 'c, 't, 'x, 'v) transition set" where
  "trans A \<equiv> fst (snd A)"

abbreviation inv :: "('a, 's, 'c, 't, 'x, 'v) sta \<Rightarrow> ('c, 't, 's) invassn" where
  "inv A \<equiv> snd (snd A)"

no_notation step_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
no_notation steps_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61, 61, 61,61,61] 61)

inductive step_u ::
  "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> 'a label
  \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
where
  step_t:
    "\<lbrakk>
      \<forall>p < length N. u \<oplus> d \<turnstile> inv (N ! p) (L ! p);
      d \<ge> 0;
      bounded B s
     \<rbrakk>
    \<Longrightarrow> (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L, s, u \<oplus> d\<rangle>" |
  step_int:
    "\<lbrakk>
      (l, g, Sil a, f, r, l') \<in> trans (N ! p);
      l \<in> commited (N ! p) \<or> (\<forall>p < length N. L ! p \<notin> commited (N ! p));
      u \<turnstile> g;
      \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      L!p = l; p < length L; L' = L[p := l']; u' = [r\<rightarrow>0]u; is_upd s f s';
      bounded B s'
    \<rbrakk>
    \<Longrightarrow> (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>" |
  step_bin:
    "\<lbrakk>
      (l1, g1, In a,  f1, r1, l1') \<in> trans (N ! p);
      (l2, g2, Out a, f2, r2, l2') \<in> trans (N ! q);
      l1 \<in> commited (N ! p) \<or> l2 \<in> commited (N ! q) \<or> (\<forall>p < length N. L ! p \<notin> commited (N ! p));
      u \<turnstile> g1; u \<turnstile> g2;
      \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      L!p = l1; L!q = l2; p < length L; q < length L; p \<noteq> q;
      L' = L[p := l1', q := l2']; u' = [r1@r2\<rightarrow>0]u; is_upd s f1 s'; is_upd s' f2 s'';
      bounded B s''
    \<rbrakk>
    \<Longrightarrow> (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Bin a\<^esub> \<langle>L', s'', u'\<rangle>" |
  step_broad:
    "\<lbrakk>
      a \<in> broadcast;
      (l, g, Out a, f, r, l') \<in> trans (N ! p);
      \<forall>p \<in> set ps. (ls p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N ! p);
      l \<in> commited (N ! p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N ! p)) \<or> (\<forall>p < length N. L ! p \<notin> commited (N ! p));
      u \<turnstile> g; \<forall>p \<in> set ps. u \<turnstile> gs p;
      \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      L!p = l;
      p < length L; set ps \<subseteq> {0..length N}; p \<notin> set ps;
      distinct ps; sorted ps;
      L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l']; u' = [r@concat (map rs ps)\<rightarrow>0]u; is_upd s f s'; is_upds s' (map fs ps) s'';
      bounded B s''
    \<rbrakk>
    \<Longrightarrow> (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Broad a\<^esub> \<langle>L', s'', u'\<rangle>"

text \<open>Comments:
\<^item> Should there be an error transition + state if states run of bounds or updates are undefined?
Then one could run a reachability check for the error state.
\<^item> Should the state be total?
\<^item> Note that intermediate states are allowed to run out of bounds
\<close>

definition steps_u ::
  "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval
  \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
where
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<equiv> (\<lambda> (L, s, u) (L', s', u'). \<exists>a. A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>)\<^sup>*\<^sup>* (L, s, u) (L', s', u')"

setup Explorer_Lib.switch_to_quotes

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
  "broadcast = fst A"

definition
  "N i = fst (snd A) ! i"

definition
  "bounds = snd (snd A)"

definition \<comment>\<open>Number of processes\<close>
  "n_ps = length (fst (snd A))"

definition states  :: \<open>'s list set\<close> where
  \<open>states \<equiv> {L. length L = n_ps \<and> (\<forall> i. i < n_ps --> L ! i \<in> UNION (trans (N i)) (\<lambda>(l, g, a, r, u, l'). {l, l'}))} \<close>

(* definition states  :: \<open>'s set\<close> where
  \<open>states \<equiv> \<Union>{UNION (trans (N i)) (\<lambda>(l, g, a, r, u, l'). {l, l'}) | i. i < n_ps} \<close> *)

definition
  "prod_inv \<equiv> \<lambda>(L, s). concat (map (\<lambda>i. inv (N i) (L ! i)) [0..<n_ps])"

definition
  "trans_int =
    {((L, s), g, Internal a, r, (L', s')) | L s l g f p a r l' L' s'.
      (l, g, Sil a, f, r, l') \<in> trans (N p) \<and>
      (l \<in> commited (N p) \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and>
      bounded bounds s' \<and> L \<in> states
    }"

definition
  "trans_bin =
    {((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) | L s L' s' s'' a p q l1 g1 f1 r1 l1' l2 g2 f2 r2 l2'.
      (l1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
      (l2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
      (l1 \<in> commited (N p) \<or> l2 \<in> commited (N q) \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
      L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and> bounded bounds s''
      \<and> L \<in> states
    }"

definition
  "trans_broad =
    {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
    L s L' s' s'' a p l g f r l' ls gs fs rs ls' ps.
      a \<in> broadcast  \<and>
      (l, g, Out a, f, r, l') \<in> trans (N p) \<and>
      (\<forall>p \<in> set ps. (ls p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      (l \<in> commited (N p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N p)) \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      L!p = l \<and>
      p < length L \<and> set ps \<subseteq> {0..n_ps} \<and> p \<notin> set ps \<and>
      distinct ps \<and> sorted ps \<and>
      L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and> is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
      bounded bounds s'' \<and> L \<in> states
    }"

definition
  "trans_prod = trans_int \<union> trans_bin \<union> trans_broad"

definition
  "prod_ta = (trans_prod, prod_inv :: ('s list \<times> ('x \<Rightarrow> 'v option) \<Rightarrow> _))"

lemma inv_of_prod[simp]:
  "inv_of prod_ta = prod_inv"
  unfolding prod_ta_def inv_of_def by simp

lemma trans_of_prod[simp]:
  "trans_of prod_ta = trans_prod"
  unfolding prod_ta_def trans_of_def by simp

lemma A_split:
  \<open>A = (broadcast, map N [0..<n_ps], bounds)\<close>
  unfolding broadcast_def N_def bounds_def n_ps_def by (cases A) (simp add: List.map_nth)

lemma map_N_n_ps_simp:
  "map N [0..<n_ps] ! p = N p"
  unfolding N_def n_ps_def List.map_nth ..

lemma N_split_simp[simp]:
  assumes "A = (broadcast', N', B)"
  shows "N' ! i = N i"
  unfolding N_def unfolding assms by simp

lemma state_preservation_updI:
  assumes "l' \<in> UNION (trans (N p)) (\<lambda>(l, g, a, r, u, l'). {l, l'})" "L \<in> states"
  shows "L[p := l'] \<in> states"
  using assms unfolding states_def by (fastforce simp: nth_list_update')

lemma state_preservation_fold_updI:
  assumes "\<forall> p \<in> set ps. ls' p \<in> UNION (trans (N p)) (\<lambda>(l, g, a, r, u, l'). {l, l'})" "L \<in> states"
  shows "fold (\<lambda>p L. L[p := ls' p]) ps L \<in> states"
  using assms by (induction ps arbitrary: L) (auto intro: state_preservation_updI)

end (* Prod TA Defs *)

locale Prod_TA=
  Prod_TA_Defs A for A :: "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta"
begin

lemma prod_invI[intro]:
  \<open>u \<turnstile> prod_inv (L, s)\<close> if \<open>\<forall>p<n_ps. u \<turnstile> Simple_Network_Language.inv (N p) (L ! p)\<close>
  using that unfolding prod_inv_def by (auto intro!: guard_concat)

lemma prod_invD[dest]:
  \<open>\<forall>p<n_ps. u \<turnstile> Simple_Network_Language.inv (N p) (L ! p)\<close> if \<open>u \<turnstile> prod_inv (L, s)\<close>
  using that unfolding prod_inv_def by (auto elim: concat_guard)

lemma action_complete:
  "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>"
  if "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>" "a \<noteq> Del" "L \<in> states"
using that(1) proof cases
  case (step_t N d B broadcast)
  then show ?thesis
    using that(2) by auto
next
  case prems: (step_int l g a' f r l' N' p B broadcast')
  have [simp]:
    "B = bounds" "broadcast' = broadcast" "length N' = n_ps"
    unfolding bounds_def broadcast_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,Internal a',r\<^esup> (L', s')"
  proof -
    from prems \<open>L \<in> states\<close> have "((L, s),g,Internal a',r,(L', s')) \<in> trans_int"
      unfolding trans_int_def
      by simp (rule exI conjI HOL.refl | assumption | (simp; fail))+
    then show ?thesis
      unfolding prod_ta_def trans_of_def trans_prod_def by simp
  qed
  moreover have "u \<turnstile> g"
    by (rule prems)
  moreover have "u' \<turnstile> inv_of prod_ta (L', s')"
    using prems(6) by auto
  moreover have "u' = [r\<rightarrow>0]u"
    by (rule prems)
  ultimately show ?thesis
    unfolding \<open>a = _\<close> ..
next
  case prems: (step_bin l1 g1 a' f1 r1 l1' N' p l2 g2 f2 r2 l2' q s'' B broadcast')
  have [simp]:
    "B = bounds" "broadcast' = broadcast" "length N' = n_ps"
    unfolding bounds_def broadcast_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g1 @ g2,Bin a',r1 @ r2\<^esup> (L', s')"
  proof -
    from prems \<open>L \<in> states\<close> have "((L, s),g1 @ g2,Bin a',r1 @ r2,(L', s')) \<in> trans_bin"
      unfolding trans_bin_def
      using [[simproc add: ex_reorder4]]
      by simp (rule exI conjI HOL.refl | assumption | fast)+
    then show ?thesis
      unfolding prod_ta_def trans_of_def trans_prod_def by simp
  qed
  moreover have "u \<turnstile> g1 @ g2"
    using \<open>u \<turnstile> g1\<close> \<open>u \<turnstile> g2\<close> by (rule guard_append)
  moreover have "u' \<turnstile> inv_of prod_ta (L', s')"
    using prems by auto
  moreover have "u' = [r1@r2\<rightarrow>0]u"
    by (rule prems)
  ultimately show ?thesis
    unfolding \<open>a = _\<close> ..
next
  case prems: (step_broad a' broadcast' l g f r l' N' p ps ls gs fs rs ls' s'' B)
  have [simp]:
    "B = bounds" "broadcast' = broadcast" "length N' = n_ps"
    unfolding bounds_def broadcast_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  let ?r = "r @ concat (map rs ps)" and ?g = "g @ concat (map gs ps)"
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>?g,Broad a',?r\<^esup> (L', s')"
  proof -
    from prems \<open>L \<in> states\<close> have "((L, s),?g,Broad a',?r,(L', s')) \<in> trans_broad"
      unfolding trans_broad_def by (auto intro!: exI)
    then show ?thesis
      unfolding prod_ta_def trans_of_def trans_prod_def by simp
  qed
  moreover have "u \<turnstile> ?g"
    using prems by (auto intro!: guard_append guard_concat)
  moreover have "u' \<turnstile> inv_of prod_ta (L', s')"
    using prems by auto
  moreover have "u' = [?r\<rightarrow>0]u"
    by (rule prems)
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
  by (intro that[of d]; unfold \<open>u' = _\<close> \<open>L' = L\<close> \<open>s' = s\<close>)
     (rule step_t.intros; (unfold inv_of_prod; rule prod_invI)?; simp)
qed

lemma delay_sound:
  assumes "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>(L', s'), u'\<rangle>" "bounded bounds s"
    shows "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  apply (subst A_split) using assms by cases (auto intro!: step_t)

lemma action_sound:
  "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>" if "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>"
using that
proof cases
  case prems: (1 g r)
  note [simp add] = map_N_n_ps_simp clock_val_append_iff clock_val_concat_iff
  from \<open>prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,a,r\<^esup> (L', s')\<close> show ?thesis
  unfolding trans_of_prod trans_prod_def
  proof safe
  assume "((L, s), g, a, r, L', s') \<in> trans_int"
  then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
    unfolding trans_int_def
    apply clarsimp
    using prems
    by (subst A_split) (intro step_int; simp; elim prod_invD; fail)+
next
  assume "((L, s), g, a, r, L', s') \<in> trans_bin"
  then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
  unfolding trans_bin_def
  using prems
    apply clarsimp
    apply (subst A_split, standard)
    apply (assumption | simp; elim prod_invD; fail)+
    done
next
  assume "((L, s), g, a, r, L', s') \<in> trans_broad"
  then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
  using prems
  unfolding trans_broad_def inv_of_prod
  apply clarsimp
  apply (subst A_split)
  apply standard
  apply (assumption | simp; elim prod_invD; fail)+
  done  
qed
qed

lemma step_iff:
  "(\<exists> a. A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>) \<longleftrightarrow> prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>" if "bounded bounds s" "L \<in> states"
  using that
  apply (auto intro: action_sound delay_sound)
  subgoal for a
    by (cases a; blast dest: action_complete elim: delay_complete)
  done

lemma bounded_inv:
  \<open>bounded bounds s'\<close> if \<open>A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close>
  using that unfolding bounds_def by cases simp+

lemma states_inv:
  \<open>L' \<in> states\<close> if \<open>A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>\<close> \<open>L \<in> states\<close>
  using that unfolding bounds_def
proof cases
  case (step_t N d B broadcast)
  with \<open>L \<in> states\<close> show ?thesis
    by simp
next
  case prems: (step_int l g a f r l' N' p B broadcast)
  from \<open>A = _\<close> prems(3) have "l' \<in> UNION (trans (N p)) (\<lambda>(l, g, a, r, u, l'). {l, l'})"
    by force
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI)
next
  case prems: (step_bin l1 g1 a f1 r1 l1' N' p l2 g2 f2 r2 l2' q s' B broadcast)
  from \<open>A = _\<close> prems(3, 4) have
    "l1' \<in> UNION (trans (N p)) (\<lambda>(l, g, a, r, u, l'). {l, l'})"
    "l2' \<in> UNION (trans (N q)) (\<lambda>(l, g, a, r, u, l'). {l, l'})"
    by force+
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI)
next
  case prems: (step_broad a broadcast l g f r l' N' p ps ls gs fs rs ls' s' B)
  from \<open>A = _\<close> prems(4, 5) have
    "l' \<in> UNION (trans (N p)) (\<lambda>(l, g, a, r, u, l'). {l, l'})"
    "\<forall> q \<in> set ps. ls' q \<in> UNION (trans (N q)) (\<lambda>(l, g, a, r, u, l'). {l, l'})"
    by force+
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI state_preservation_fold_updI)
qed

end (* Prod TA *)

end (* Theory *)