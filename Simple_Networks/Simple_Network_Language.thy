theory Simple_Network_Language
  imports Main
    "TA_Byte_Code.State_Networks"
    "TA_Byte_Code.UPPAAL_State_Networks_Impl"
    "../library/Explorer"
    FinFun.FinFun
begin

section \<open>Simple networks of automata with broadcast channels and commited locations\<close>

no_notation top_assn ("true")

datatype ('a, 'b) bexp =
  true |
  not "('a, 'b) bexp" |
  "and" "('a, 'b) bexp" "('a, 'b) bexp" |
  or "('a, 'b) bexp" "('a, 'b) bexp" |
  imply "('a, 'b) bexp" "('a, 'b) bexp" | \<comment> \<open>Boolean connectives\<close>
  eq "('a, 'b) exp" "('a, 'b) exp" |
  le "('a, 'b) exp" "('a, 'b) exp" |
  lt "('a, 'b) exp" "('a, 'b) exp" |
  ge "('a, 'b) exp" "('a, 'b) exp" |
  gt "('a, 'b) exp" "('a, 'b) exp"
and ('a, 'b) exp =
  const 'b | var 'a | if_then_else "('a, 'b) bexp" "('a, 'b) exp" "('a, 'b) exp" |
  binop "'b \<Rightarrow> 'b \<Rightarrow> 'b" "('a, 'b) exp" "('a, 'b) exp" | unop "'b \<Rightarrow> 'b" "('a, 'b) exp"

inductive check_bexp :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, 'b :: linorder) bexp \<Rightarrow> bool \<Rightarrow> bool" and is_val
  where
  "check_bexp s true True" |
  "check_bexp s (not e) (\<not> b)" if "check_bexp s e b" |
  "check_bexp s (and e1 e2) (a \<and> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (or e1 e2) (a \<or> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (imply e1 e2) (a \<longrightarrow> b)" if "check_bexp s e1 a" "check_bexp s e2 b" |
  "check_bexp s (eq a b) (x = v)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (le a b) (v \<le> x)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (lt a b) (v < x)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (ge a b) (v \<ge> x)" if "is_val s a v" "is_val s b x" |
  "check_bexp s (gt a b) (v > x)" if "is_val s a v" "is_val s b x" |
  "is_val s (const c) c" |
  "is_val s (var x)   v" if "s x = Some v" |
  "is_val s (if_then_else b e1 e2) (if bv then v1 else v2)"
  if "is_val s e1 v1" "is_val s e2 v2" "check_bexp s b bv" |
  "is_val s (binop f e1 e2) (f v1 v2)" if "is_val s e1 v1" "is_val s e2 v2" |
  "is_val s (unop f e) (f v)" if "is_val s e v"

type_synonym
  ('c, 't, 's) invassn = "'s \<Rightarrow> ('c, 't) cconstraint"

type_synonym
  ('a, 'b) upd = "('a * ('a, 'b) exp) list"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) transition =
  "'s \<times> ('x, 'v) bexp \<times> ('c, 't) cconstraint \<times> 'a \<times> ('x, 'v) upd \<times> 'c list \<times> 's"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) sta =
  "'s set \<times> ('a, 's, 'c, 't, 'x, 'v) transition set \<times> ('c, 't, 's) invassn"

type_synonym
  ('a, 's, 'c, 't, 'x, 'v) nta = "'a set \<times> ('a act, 's, 'c, 't, 'x, 'v) sta list \<times> ('x \<rightharpoonup> 'v * 'v)"

context begin

qualified definition conv_t where "conv_t \<equiv> \<lambda> (l,b,g,a,f,r,l'). (l,b,conv_cc g,a,f,r,l')"

qualified definition conv_A where "conv_A \<equiv> \<lambda> (C, T, I). (C, conv_t ` T, conv_cc o I)"

definition conv where
  "conv \<equiv> \<lambda>(broadcast, automata, bounds). (broadcast, map conv_A automata, bounds)"

end

datatype 'b label = Del | Internal 'b | Bin 'b | Broad 'b

definition bounded where
  "bounded bounds s \<equiv> dom s = dom bounds \<and>
    (\<forall>x \<in> dom s. fst (the (bounds x)) \<le> the (s x) \<and> the (s x) \<le> snd (the (bounds x)))"

definition is_upd where
  "is_upd s upds s' \<equiv> \<exists>xs. list_all2 (\<lambda> (l1, r1) (l2, r2). l1 = l2 \<and> is_val s r1 r2) upds xs
    \<and> s' = fold (\<lambda> (l, r) s. s(l := Some r)) xs s"

inductive is_upds where
  "is_upds s [] s" |
  "is_upds s (x # xs) s''" if "is_upd s x s'" "is_upds s' xs s''"

definition commited :: "('a, 's, 'c, 't, 'x, 'v) sta \<Rightarrow> 's set" where
  "commited A \<equiv> fst A"

definition trans :: "('a, 's, 'c, 't, 'x, 'v) sta \<Rightarrow> ('a, 's, 'c, 't, 'x, 'v) transition set"
  where
  "trans A \<equiv> fst (snd A)"

definition inv :: "('a, 's, 'c, 't, 'x, 'v) sta \<Rightarrow> ('c, 't, 's) invassn" where
  "inv A \<equiv> snd (snd A)"

no_notation step_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_, _, _\<rangle>" [61,61,61,61,61] 61)
no_notation steps_sn ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61, 61, 61,61,61] 61)

inductive step_u ::
  "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval
  \<Rightarrow> 'a label \<Rightarrow> 's list \<Rightarrow> ('x \<rightharpoonup> 'v) \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
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
      (l, b, g, Sil a, f, r, l') \<in> trans (N ! p);
      l \<in> commited (N ! p) \<or> (\<forall>p < length N. L ! p \<notin> commited (N ! p));
      check_bexp s b True;
      u \<turnstile> g;
      \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      L!p = l; p < length L; L' = L[p := l']; u' = [r\<rightarrow>0]u; is_upd s f s';
      bounded B s'
    \<rbrakk>
    \<Longrightarrow> (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Internal a\<^esub> \<langle>L', s', u'\<rangle>" |
  step_bin:
    "\<lbrakk>
      a \<notin> broadcast;
      (l1, b1, g1, In a,  f1, r1, l1') \<in> trans (N ! p);
      (l2, b2, g2, Out a, f2, r2, l2') \<in> trans (N ! q);
      l1 \<in> commited (N ! p) \<or> l2 \<in> commited (N ! q) \<or> (\<forall>p < length N. L ! p \<notin> commited (N ! p));
      check_bexp s b1 True; check_bexp s b2 True; u \<turnstile> g1; u \<turnstile> g2;
      \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      L!p = l1; L!q = l2; p < length L; q < length L; p \<noteq> q;
      L' = L[p := l1', q := l2']; u' = [r1@r2\<rightarrow>0]u; is_upd s f1 s'; is_upd s' f2 s'';
      bounded B s''
    \<rbrakk>
    \<Longrightarrow> (broadcast, N, B) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Bin a\<^esub> \<langle>L', s'', u'\<rangle>" |
  step_broad:
    "\<lbrakk>
      a \<in> broadcast;
      (l, b, g, Out a, f, r, l') \<in> trans (N ! p);
      \<forall>p \<in> set ps. (L ! p, bs p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N ! p);
      l \<in> commited (N ! p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N ! p))
      \<or> (\<forall>p < length N. L ! p \<notin> commited (N ! p));
      check_bexp s b True; \<forall>p \<in> set ps. check_bexp s (bs p) True; u \<turnstile> g; \<forall>p \<in> set ps. u \<turnstile> gs p;
      \<forall>q < length N. q \<notin> set ps \<and> p \<noteq> q
        \<longrightarrow> (\<forall>b g f r l'. (L!q, b, g, In a, f, r, l') \<in> trans (N ! q)
        \<longrightarrow> \<not> check_bexp s b True \<or> \<not> u \<turnstile> g);
      \<forall>p < length N. u' \<turnstile> inv (N ! p) (L' ! p);
      L!p = l;
      p < length L; set ps \<subseteq> {0..<length N}; p \<notin> set ps; distinct ps; sorted ps;
      L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'];
      u' = [r@concat (map rs ps)\<rightarrow>0]u;
      is_upd s f s'; is_upds s' (map fs ps) s'';
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
  "broadcast = fst A"

definition
  "N i = fst (snd A) ! i"

definition
  "bounds = snd (snd A)"

definition \<comment>\<open>Number of processes\<close>
  "n_ps = length (fst (snd A))"

definition states  :: "'s list set" where
  "states \<equiv> {L. length L = n_ps \<and>
    (\<forall> i. i < n_ps --> L ! i \<in> UNION (trans (N i)) (\<lambda>(l, e, g, a, r, u, l'). {l, l'}))}"

definition
  "prod_inv \<equiv> \<lambda>(L, s). if L \<in> states then concat (map (\<lambda>i. inv (N i) (L ! i)) [0..<n_ps]) else []"

definition
  "trans_int =
    {((L, s), g, Internal a, r, (L', s')) | L s l b g f p a r l' L' s'.
      (l, b, g, Sil a, f, r, l') \<in> trans (N p) \<and>
      (l \<in> commited (N p) \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      L!p = l \<and> p < length L \<and> L' = L[p := l'] \<and> is_upd s f s' \<and> check_bexp s b True \<and>
      L \<in> states \<and> bounded bounds s \<and> bounded bounds s'
    }"

definition
  "trans_bin =
    {((L, s), g1 @ g2, Bin a, r1 @ r2, (L', s'')) |
      L s L' s' s'' a p q l1 b1 g1 f1 r1 l1' l2 b2 g2 f2 r2 l2'.
      a \<notin> broadcast \<and>
      (l1, b1, g1, In a,  f1, r1, l1') \<in> trans (N p) \<and>
      (l2, b2, g2, Out a, f2, r2, l2') \<in> trans (N q) \<and>
      (l1 \<in> commited (N p) \<or> l2 \<in> commited (N q) \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      L!p = l1 \<and> L!q = l2 \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
      check_bexp s b1 True \<and> check_bexp s b2 True \<and>
      L' = L[p := l1', q := l2'] \<and> is_upd s f1 s' \<and> is_upd s' f2 s'' \<and>
      L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
    }"

definition
  "trans_broad =
    {((L, s), g @ concat (map gs ps), Broad a, r @ concat (map rs ps), (L', s'')) |
    L s L' s' s'' a p l b g f r l' bs gs fs rs ls' ps.
      a \<in> broadcast  \<and>
      (l, b, g, Out a, f, r, l') \<in> trans (N p) \<and>
      (\<forall>p \<in> set ps. (L ! p, bs p, gs p, In a, fs p, rs p, ls' p) \<in> trans (N p)) \<and>
      (l \<in> commited (N p) \<or> (\<exists>p \<in> set ps. L ! p \<in> commited (N p))
      \<or> (\<forall>p < n_ps. L ! p \<notin> commited (N p))) \<and>
      (\<forall>q < n_ps. q \<notin> set ps \<and> p \<noteq> q \<longrightarrow>
        \<not> (\<exists>b g f r l'. (L!q, b, g, In a, f, r, l') \<in> trans (N q) \<and> check_bexp s b True)) \<and>
      L!p = l \<and>
      p < length L \<and> set ps \<subseteq> {0..<n_ps} \<and> p \<notin> set ps \<and> distinct ps \<and> sorted ps \<and>
      check_bexp s b True \<and> (\<forall>p \<in> set ps. check_bexp s (bs p) True) \<and>
      L' = fold (\<lambda>p L . L[p := ls' p]) ps L[p := l'] \<and> is_upd s f s' \<and> is_upds s' (map fs ps) s'' \<and>
      L \<in> states \<and> bounded bounds s \<and> bounded bounds s''
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
  assumes "l' \<in> UNION (trans (N p)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})" "L \<in> states"
  shows "L[p := l'] \<in> states"
  using assms unfolding states_def by (fastforce simp: nth_list_update')

lemma state_preservation_fold_updI:
  assumes "\<forall>p \<in> set ps. ls' p \<in> UNION (trans (N p)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})" "L \<in> states"
  shows "fold (\<lambda>p L. L[p := ls' p]) ps L \<in> states"
  using assms by (induction ps arbitrary: L) (auto intro: state_preservation_updI)

lemma state_set_states:
  "Simulation_Graphs_TA.state_set prod_ta \<subseteq> {(l, s). l \<in> states}"
  unfolding prod_ta_def state_set_def
  unfolding trans_of_def trans_prod_def
  unfolding trans_int_def trans_bin_def trans_broad_def
  by auto (auto intro: state_preservation_updI state_preservation_fold_updI)

lemma trans_prod_bounded_inv:
  \<open>bounded bounds s'\<close> if \<open>((L, s), g, a, r, (L', s')) \<in> trans_prod\<close>
  using that unfolding bounds_def trans_prod_def trans_int_def trans_bin_def trans_broad_def
  by (auto simp: bounds_def)

lemma trans_prod_states_inv:
  \<open>L' \<in> states\<close> if \<open>((L, s), g, a, r, (L', s')) \<in> trans_prod\<close> \<open>L \<in> states\<close>
  using that
  unfolding bounds_def trans_prod_def trans_int_def trans_bin_def trans_broad_def
  apply clarsimp
  apply safe
         apply (force intro!: state_preservation_updI)
        apply (force intro!: state_preservation_updI)
       apply (force intro!: state_preservation_updI)
      apply (force intro!: state_preservation_updI)
     apply (force intro!: state_preservation_updI)
    apply (fastforce intro!: state_preservation_updI state_preservation_fold_updI)
  subgoal
    apply (rule state_preservation_updI)
    apply force
    apply (force intro!: state_preservation_fold_updI)
    done
  apply (fastforce intro!: state_preservation_updI state_preservation_fold_updI)
  done

end (* Prod TA Defs *)


locale Prod_TA_sem =
  Prod_TA_Defs A for A :: "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta"
begin

lemma prod_invI[intro]:
  \<open>u \<turnstile> prod_inv (L, s)\<close> if \<open>\<forall>p<n_ps. u \<turnstile> Simple_Network_Language.inv (N p) (L ! p)\<close>
  using that unfolding prod_inv_def by (auto intro!: guard_concat)

lemma prod_invD[dest]:
  \<open>\<forall>p<n_ps. u \<turnstile> Simple_Network_Language.inv (N p) (L ! p)\<close> if \<open>u \<turnstile> prod_inv (L, s)\<close> \<open>L \<in> states\<close>
  using that unfolding prod_inv_def by (auto elim: concat_guard)

lemma delay_sound:
  assumes "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>(L', s'), u'\<rangle>" "L \<in> states" "bounded bounds s"
    shows "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', s', u'\<rangle>"
  apply (subst A_split) using assms by cases (auto intro!: step_t)

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
      by (subst A_split) (intro step_int; simp; elim prod_invD; assumption)
  next
    assume "((L, s), g, a, r, L', s') \<in> trans_bin"
    then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      unfolding trans_bin_def
      using prems \<open>L' \<in> _\<close>
      apply clarsimp
      apply (subst A_split, standard)
                     apply (assumption | simp; elim prod_invD; assumption)+
      done
  next
    assume "((L, s), g, a, r, L', s') \<in> trans_broad"
    then show "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>"
      using prems \<open>L' \<in> _\<close>
      unfolding trans_broad_def inv_of_prod
      apply clarsimp
      apply (subst A_split)
      apply standard
                          apply (assumption | simp; elim prod_invD; assumption | fastforce)+
      done
  qed
qed

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
  case prems: (step_int l b g a f r l' N' p B broadcast)
  from \<open>A = _\<close> prems(3) have "l' \<in> UNION (trans (N p)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})"
    by force
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI)
next
  case prems: (step_bin broadcast a l1 b1 g1 f1 r1 l1' N' p l2 b2 g2 f2 r2 l2' q s' B)
  from \<open>A = _\<close> prems(4, 5) have
    "l1' \<in> UNION (trans (N p)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})"
    "l2' \<in> UNION (trans (N q)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})"
    by force+
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI)
next
  case prems: (step_broad a broadcast l b g f r l' N' p ps bs gs fs rs ls' s' B)
  from \<open>A = _\<close> prems(4, 5) have
    "l' \<in> UNION (trans (N p)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})"
    "\<forall> q \<in> set ps. ls' q \<in> UNION (trans (N q)) (\<lambda>(l, b, g, a, r, u, l'). {l, l'})"
    by force+
  with \<open>L \<in> states\<close> show ?thesis
    unfolding \<open>L' = _\<close> by (intro state_preservation_updI state_preservation_fold_updI)
qed

end (* Prod TA Defs on a time domain *)


locale Prod_TA =
  Prod_TA_sem A for A :: "('a, 's, 'c, 't :: time, 'x, 'v :: linorder) nta" +
  assumes broadcast_receivers_unguarded:
    "\<forall>p < n_ps. \<forall>l b g a f r l'. (l, b, g, In a, f, r, l') \<in> trans (N p) \<and> a \<in> broadcast \<longrightarrow> g = []"
begin

lemma action_complete:
  "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>(L', s'), u'\<rangle>"
  if "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>" "a \<noteq> Del" "L \<in> states" "bounded bounds s"
using that(1) proof cases
  case (step_t N d B broadcast)
  then show ?thesis
    using that(2) by auto
next
  case prems: (step_int l b g a' f r l' N' p B broadcast')
  have [simp]:
    "B = bounds" "broadcast' = broadcast" "length N' = n_ps"
    unfolding bounds_def broadcast_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g,Internal a',r\<^esup> (L', s')"
  proof -
    from prems \<open>L \<in> states\<close> \<open>bounded _ s\<close> have "((L, s),g,Internal a',r,(L', s')) \<in> trans_int"
      unfolding trans_int_def
      by simp (rule exI conjI HOL.refl | assumption | (simp; fail))+
    then show ?thesis
      unfolding prod_ta_def trans_of_def trans_prod_def by simp
  qed
  moreover have "u \<turnstile> g"
    by (rule prems)
  moreover have "u' \<turnstile> inv_of prod_ta (L', s')"
    using prems(7) by auto
  moreover have "u' = [r\<rightarrow>0]u"
    by (rule prems)
  ultimately show ?thesis
    unfolding \<open>a = _\<close> ..
next
  case prems: (step_bin a' broadcast' l1 b1 g1 f1 r1 l1' N' p l2 b2 g2 f2 r2 l2' q s'' B)
  have [simp]:
    "B = bounds" "broadcast' = broadcast" "length N' = n_ps"
    unfolding bounds_def broadcast_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>g1 @ g2,Bin a',r1 @ r2\<^esup> (L', s')"
  proof -
    from prems \<open>L \<in> states\<close> \<open>bounded bounds s\<close> have
      "((L, s),g1 @ g2,Bin a',r1 @ r2,(L', s')) \<in> trans_bin"
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
  case prems: (step_broad a' broadcast' l b g f r l' N' p ps bs gs fs rs ls' s'' B)
  have [simp]:
    "B = bounds" "broadcast' = broadcast" "length N' = n_ps"
    unfolding bounds_def broadcast_def n_ps_def unfolding prems(1) by simp+
  have [simp]:
    "N' ! i = N i" for i
    unfolding N_def unfolding prems(1) by simp
  let ?r = "r @ concat (map rs ps)" and ?g = "g @ concat (map gs ps)"
  have "prod_ta \<turnstile> (L, s) \<longrightarrow>\<^bsup>?g,Broad a',?r\<^esup> (L', s')"
  proof -
    have *: "\<not> u \<turnstile> g \<longleftrightarrow> False" if
      "p < n_ps" "(l, b, g, In a', f, r, l') \<in> Simple_Network_Language.trans (N p)"
      "a' \<in> broadcast"
      for l b g a' f r l' p
    proof -
      from that broadcast_receivers_unguarded have \<open>g = []\<close>
        by blast
      then show ?thesis
        by auto
    qed
    from prems \<open>L \<in> states\<close> \<open>bounded bounds s\<close> have "((L, s),?g,Broad a',?r,(L', s')) \<in> trans_broad"
      unfolding trans_broad_def
      by clarsimp
         (intro exI conjI HOL.refl; (rule HOL.refl | assumption | fastforce simp: *))
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

lemma step_iff:
  "(\<exists> a. A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', s', u'\<rangle>) \<longleftrightarrow> prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  if "bounded bounds s" "L \<in> states"
  using that
  apply (auto intro: action_sound delay_sound)
  subgoal for a
    by (cases a; blast dest: action_complete elim: delay_complete)
  done

end (* Prod TA *)

end (* Theory *)