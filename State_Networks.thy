theory State_Networks
  imports Networks Normalized_Zone_Semantics_Impl
    "~/Formalizations/Experiments/Reordering_Quantifiers"
begin

(* XXX Move *)
lemma finite_Collect_bounded_ex_7 [simp]:
  assumes "finite {(a,b,c,d,e,f,g) . P a b c d e f g}"
  shows
    "finite {x. \<exists>a b c d e f g. P a b c d e f g \<and> Q x a b c d e f g}
    \<longleftrightarrow> (\<forall> a b c d e f g. P a b c d e f g \<longrightarrow> finite {x. Q x a b c d e f g})"
  using assms finite_Collect_bounded_ex[OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f, g). Q x a b c d e f g"]
  by clarsimp (* force, simp *)

lemma finite_Collect_bounded_ex_9 [simp]:
  assumes "finite {(a,b,c,d,e,f,g,h,i) . P a b c d e f g h i}"
  shows
    "finite {x. \<exists>a b c d e f g h i. P a b c d e f g h i \<and> Q x a b c d e f g h i}
    \<longleftrightarrow> (\<forall> a b c d e f g h i. P a b c d e f g h i \<longrightarrow> finite {x. Q x a b c d e f g h i})"
  using assms finite_Collect_bounded_ex[OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e, f, g, h, i). Q x a b c d e f g h i"]
  by clarsimp (* force, simp *)

no_notation Ref.update ("_ := _" 62)

section \<open>Networks of Timed Automata with Shared State\<close>

subsection \<open>Syntax and Operational Semantics\<close>

text \<open>
  We extend Networks of Timed Automata with arbitrary shared (global) state.
  Syntactically, this extension is very simple.
  We can just use the free action label slot to annotate edges with a guard
  and an update function on discrete states.
  The slightly more clumsy part is adding invariants for discrete states
  by directly specifying an invariant annotating function.
\<close>

type_synonym
  ('a, 'c, 't, 's, 'st) snta =
  "('a, ('st \<Rightarrow> bool) \<times> ('st \<Rightarrow> 'st), 'c, 't, 's) nta \<times> ('s \<Rightarrow> 'st \<Rightarrow> bool) list"

text \<open>
  Semantic states now consist of three things:
  a list of process locations, the shared state, and a clock valuation.
  The semantic extension then is also obvious: we can take the same transitions
  as in the network without shared state, however we have to add state updates
  and checks for guards on the shared state.
  The updates on discrete state for synchronizing transitions are in the same order as in UPPAAL
  (output before input).
\<close>

inductive step_sn ::
  "('a, 'c, 't, 's, 'st) snta \<Rightarrow> 's list \<Rightarrow> 'st \<Rightarrow> ('c, ('t::time)) cval
  \<Rightarrow> 's list \<Rightarrow> 'st \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
  ("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow> \<langle>_, _, _\<rangle>" [61,61,61] 61)
where
  step_sn_t:
    "(N, I) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L, s, u \<oplus> d\<rangle>" if "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L, u \<oplus> d\<rangle>" "length N = length I" |
  step_sn_i:
    "(N, I) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    if "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Act (c, m)\<^esub> \<langle>L', u'\<rangle>" "c s" "\<forall> p < length I. (I ! p) (L' ! p) s'" "s' = m s"
       "length N = length I" |
  step_sn_s:
    "(N, I) \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    if "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Syn (ci, mi) (co, mo)\<^esub> \<langle>L', u'\<rangle>"
       "ci s" "co s" "\<forall> p < length I. (I ! p) (L' ! p) s'"
       "s' = mi (mo s)" "length N = length I"

inductive_cases[elim!]: "N \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"

inductive steps_sn ::
  "('a, 'c, 't, 's, 'st) snta \<Rightarrow> 's list \<Rightarrow> 'st \<Rightarrow> ('c, ('t::time)) cval
  \<Rightarrow> 's list \<Rightarrow> 'st \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile> \<langle>_, _, _\<rangle> \<rightarrow>* \<langle>_, _, _\<rangle>" [61, 61, 61,61,61] 61)
where
  refl: "N \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L, s, u\<rangle>" |
  step: "N \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle> \<Longrightarrow> N \<turnstile> \<langle>L', s', u'\<rangle> \<rightarrow> \<langle>L'', s'', u''\<rangle>
        \<Longrightarrow> N \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L'', s'', u''\<rangle>"

declare steps_sn.intros[intro]

lemma stepI2:
  "N \<turnstile> \<langle>l, s, u\<rangle> \<rightarrow>* \<langle>l'', s'', u''\<rangle>" if
  "N \<turnstile> \<langle>l', s', u'\<rangle> \<rightarrow>* \<langle>l'', s'', u''\<rangle>" "N \<turnstile> \<langle>l, s, u\<rangle> \<rightarrow> \<langle>l', s', u'\<rangle>"
  using that
  apply induction
   apply rule
    apply (rule refl)
   apply assumption
  apply simp
  by (rule; assumption)

subsection \<open>Product Automaton\<close>

(*
abbreviation state_set :: "('a, 'c, 'time, 's) transition set \<Rightarrow> 's set" where
  "state_set T \<equiv> fst ` T \<union> (snd o snd o snd o snd) ` T"
*)

locale Prod_TA_Defs =
  fixes A :: "('a, 'c, 't, 's, 'st) snta"
begin

  sublocale Product_TA_Defs "fst A" .

term product_ta

  abbreviation "N \<equiv> fst A"
  abbreviation "P \<equiv> snd A"
  abbreviation "T' \<equiv> trans_of product_ta"
  abbreviation "I' \<equiv> inv_of product_ta"

  definition "p \<equiv> length N"

  (* definition "states = {L. length L = length T \<and> (\<forall> p \<in> {..<length T}. L!p \<in> state_set (T!p))}" *)

  definition
    "prod_trans_i =
      {((L, s), g, a, r, (L', m s)) | L s g c a r m L'.
       (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) (m s))
       \<and> (L, g, (a, Act (c, m)), r, L') \<in> T' \<and> c s}"

  definition
    "prod_trans_s =
      {((L, s), g, a, r, (L', s')) | L s g ci co a r mi mo L' s'.
        ci s \<and> co s
        \<and> (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) s')
        \<and> (L, g, (a, Syn (ci, mi) (co, mo)), r, L') \<in> T'
        \<and> s' = mi (mo s)
      }"

  definition
    "prod_trans \<equiv> prod_trans_i \<union> prod_trans_s"

  definition
    "prod_invariant \<equiv> product_invariant o fst"

  definition prod_ta :: "('a, 'c, 't, 's list \<times> 'st) ta" where
    "prod_ta \<equiv> (prod_trans, prod_invariant)"

  lemma prod_ta_cases:
    assumes "prod_ta \<turnstile> L \<longrightarrow>\<^bsup>g,a,r\<^esup> L'"
    shows "(L, g, a, r, L') \<in> prod_trans_i \<or> (L, g, a, r, L') \<in> prod_trans_s"
    using assms unfolding prod_ta_def trans_of_def prod_trans_def by auto

  lemma inv_of_simp:
    "inv_of prod_ta (L, s) = I' L"
    unfolding inv_of_def prod_ta_def prod_invariant_def product_ta_def by simp

  lemma collect_clki_prod_invariant:
    "collect_clki prod_invariant = collect_clki product_invariant"
    unfolding prod_invariant_def collect_clki_def by simp

  (*
  lemma states_length:
    assumes "L \<in> states"
    shows "length L = length N"
    using assms unfolding states_def by auto
    *)

  lemma collect_clkt_prod_trans_subs:
    "collect_clkt prod_trans \<subseteq> collect_clkt T'"
    unfolding collect_clkt_def prod_trans_def prod_trans_i_def prod_trans_s_def by fastforce

  lemma collect_clkvt_prod_trans_subs:
    "collect_clkvt prod_trans \<subseteq> collect_clkvt T'"
    unfolding collect_clkvt_def prod_trans_def prod_trans_i_def prod_trans_s_def by fastforce

term N term P

lemma T_simp:
  "T ! q = trans_of (N ! q)" if "q < length N"
  using that by simp

lemma prod_state_set_subs:
  assumes "l \<in> state_set T'" "q < p"
  shows "l ! q \<in> state_set (trans_of (N ! q))"
  using assms
  apply (simp only: T_simp[symmetric] p_def)
  by (rule product_state_set_subs; simp add: product_ta_def trans_of_def)

context
  assumes finite_state:
    "\<forall> q < p. \<forall> l \<in> state_set (trans_of (N ! q)). finite {s. (P ! q) l s}"
      and finite_trans: "\<forall> A \<in> set N. finite (trans_of A)"
begin

lemma finite_state':
  "\<forall> q < p. \<forall> l \<in> state_set T'. finite {s. (P ! q) (l ! q) s}"
  using finite_state prod_state_set_subs by simp

lemma finite_state'':
  "finite {s. \<forall> q < p. (P ! q) (l ! q) s}" if \<open>p > 0\<close> \<open>l \<in> state_set T'\<close>
proof -
  from \<open>p > 0\<close> obtain q where "q < p" by auto
  with finite_state' \<open>l \<in> _\<close> have "finite {s. (P ! q) (l ! q) s}" by auto
  then show ?thesis by (rule rev_finite_subset) (auto intro: \<open>q < p\<close>)
qed

lemma prod_trans_i_alt_def:
  "prod_trans_i =
    {((L, s), g, a, r, (L', m s)) | L s g c a r m L'.
     (L, g, (a, Act (c, m)), r, L') \<in> T' \<and>
     (\<forall> q < p. (P ! q) (L ! q) s) \<and> (\<forall> q < p. (P ! q) (L' ! q) (m s))
     \<and> c s}"
  unfolding prod_trans_i_def by (safe; metis)

lemma finite_prod_trans:
  "finite prod_trans" if "p > 0"
  unfolding prod_trans_def prod_trans_i_alt_def prod_trans_s_def
  apply safe
  subgoal
    apply (tactic \<open>defer_ex_tac @{context} 1\<close>, simp only: conj_assoc)
    using [[simproc add: ex_reorder4]]
    apply simp
    apply (subst finite_Collect_bounded_ex_7)
    subgoal
      using [[simproc add: finite_Collect]] finite_trans_of_product[OF finite_trans]
      by (auto intro!: finite_imageI finite_vimageI simp: inj_on_def)
    apply safe
    (* When unfolding regular_def
    apply (tactic \<open>defer_ex_tac @{context} 1\<close>) (* XXX *)
    *)
    apply (subst finite_Collect_bounded_ex)
    by (auto intro: finite_state'' \<open>p > 0\<close>)
  subgoal
    apply (tactic \<open>defer_ex_tac @{context} 1\<close>, simp only: conj_assoc)
    apply (tactic \<open>rearrange_ex_fixed_5 @{context} 1\<close>)
    apply (use [[simproc add: ex_reorder4]] in simp)
    apply (subst finite_Collect_bounded_ex_9)
    subgoal
      using [[simproc add: finite_Collect]] finite_trans_of_product[OF finite_trans]
      by (auto intro!: finite_imageI finite_vimageI simp: inj_on_def)
    apply (tactic \<open>defer_ex_tac @{context} 1\<close>, simp only: conj_assoc)
    apply (tactic \<open>defer_ex_tac @{context} 1\<close>, simp only: conj_assoc)
    apply safe
    apply (subst finite_Collect_bounded_ex)
    by (auto intro: finite_state'' \<open>p > 0\<close>)
  done

thm finite_product_trans_i[OF finite_trans] finite_product_trans_s[OF finite_trans]

thm finite_trans_of_product[OF finite_trans]
thm finite_states

end (* End of context for finiteness of automaton *)

end (* End locale for product TA definition *)

locale Prod_TA_Defs' =
  Prod_TA_Defs A for A :: "('a, 'c, 't :: time, 's, 'st) snta"
begin

  sublocale Product_TA_Defs' "fst A".

  thm Networks.Product_TA_Defs'.product_invariantD product_invariantD

  term "step_sn A" term states

  lemma states_step:
    "L' \<in> states" if "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" "L \<in> states"
    using that states_step by cases auto

  lemma states_steps:
    "L' \<in> states" if "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" "L \<in> states"
    using that apply (induction A \<equiv> A _ _ _ _ _ _ rule: steps_sn.induct)
     apply assumption
    apply simp
    by (rule states_step)

  lemma inv_step:
    "\<forall>p<length P. (P ! p) (L' ! p) s'" if
    "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>" "\<forall>p<length P. (P ! p) (L ! p) s"
    using that by (cases) auto

  lemma inv_steps:
    "\<forall>p<length P. (P ! p) (L' ! p) s'" if
    "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>" "\<forall>p<length P. (P ! p) (L ! p) s"
    using that apply (induction A \<equiv> A _ _ _ _ _ _ rule: steps_sn.induct) by (auto intro: inv_step)

end

thm steps_altI

(* Network + valid start state *)
locale Prod_TA =
  Prod_TA_Defs A for A :: "('a, 'c, 't :: time, 's, 'st) snta" +
  fixes L :: "'s list"
  assumes states[intro]: "L \<in> Product_TA_Defs.states N"
  fixes s :: 'st
  assumes Len: "length N = length P"
      and inv: "\<forall>p<length P. (P ! p) (L ! p) s"
begin

  sublocale Product_TA N L by standard rule

  term product_ta

  lemma product_inv_prod[intro]:
    "u \<turnstile> inv_of prod_ta (l, s')" if "u \<turnstile> inv_of product_ta l"
    using that unfolding product_ta_def prod_ta_def prod_invariant_def inv_of_def by auto

  lemma A_simp[simp]:
    "N' = N" "P' = P" if "A = (N', P')"
    using that by auto

  lemma prod_complete:
    assumes step: "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle>"
    shows "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
  using step proof cases
    case (step_sn_t N d P)
    then show ?thesis
      apply -
      apply (frule A_simp)
      apply (drule A_simp(2))
      by (force elim!: product_delay_complete)
  next
    case prems: (step_sn_i N c m I)
    note [simp] = A_simp[OF prems(1)]
    from prems(6) have [simp]: "length P = p" by (simp add: p_def)
    from prems(2-) obtain a where "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, Act (c, m))\<^esub> \<langle>L', u'\<rangle>"
      by (auto elim!: product_int_complete)
    with prems(3-5) inv obtain g r where step:
        "((L, s), g, a, r, (L', s')) \<in> prod_trans_i"
        "u \<turnstile> g" "u' = [r\<rightarrow>0]u" "u' \<turnstile> inv_of product_ta L'"
      unfolding prod_trans_i_def by - (erule step_a.cases; auto)
    then have "((L, s), g, a, r, (L', s')) \<in> trans_of prod_ta"
      by (simp add: prod_trans_def trans_of_def prod_ta_def)
    then show ?thesis
      apply -
      apply (rule step_a)
      apply rule
      using step(2-) by force+
  next
    case prems: (step_sn_s N ci mi co mo I)
    note [simp] = A_simp[OF prems(1)]
    from prems(7) have [simp]: "length P = p" by (simp add: p_def)
    from prems(2-) obtain a where "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, Syn (ci, mi) (co, mo))\<^esub> \<langle>L', u'\<rangle>"
      by (auto elim!: product_sync_complete)
    with prems(3-6) inv obtain g r where step:
        "((L, s), g, a, r, (L', s')) \<in> prod_trans_s"
        "u \<turnstile> g" "u' = [r\<rightarrow>0]u" "u' \<turnstile> inv_of product_ta L'"
      unfolding prod_trans_s_def by - (erule step_a.cases; auto; blast)
        (* XXX Simproc for instantiations from equality? *)
    then have "((L, s), g, a, r, (L', s')) \<in> trans_of prod_ta"
      by (simp add: prod_trans_def trans_of_def prod_ta_def)
    then show ?thesis
      apply -
      apply (rule step_a)
      apply rule
      using step(2-) by force+
  qed

  lemma A_unfold:
    "A = (N, P)"
    by simp

  thm states_step

  lemma prod_sound':
    assumes step: "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
    shows "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow> \<langle>L', s', u'\<rangle> \<and> product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>
           \<and> (\<forall>p<length P. (P ! p) (L' ! p) s')"
    using assms proof cases
    case (step_t d)
    then show ?thesis
    proof cases
      case prems: 1
      then have "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>L', u'\<rangle>" unfolding inv_of_simp by fast
      with product_delay_sound[OF this] prems show ?thesis
        apply simp
        apply rule
        apply (subst A_unfold)
        apply (rule step_sn_t)
          apply (simp add: Len)+
        by (blast intro!: inv)+
    qed
  next
    case (step_a a)
    from Len have [simp]: "length P = p" by (simp add: p_def)
    from step_a show ?thesis
    proof cases
      case prems: (1 g r)
      from this(1) show ?thesis
        apply -
      proof (drule prod_ta_cases, erule disjE, goal_cases)
        case 1
        then obtain c m where *:
          "s' = m s" "\<forall>q<p. (P ! q) (L ! q) s"
          "\<forall>q<p. (P ! q) (L' ! q) (m s)" "product_ta \<turnstile> L \<longrightarrow>\<^bsup>g,(a, Act (c, m)),r\<^esup> L'" "c s"
          unfolding prod_trans_i_def by force
        with prems have "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, Act (c, m))\<^esub> \<langle>L', u'\<rangle>"
          unfolding inv_of_simp by - rule
        with product_action_sound[OF this] prems * show ?thesis
          apply (subst A_unfold)
          apply (rule conjI)
           apply (rule step_sn_i)
               apply (simp add: Len)+
          by blast
      next
        case 2
        then obtain ci co mi mo where *:
          "s' = mi (mo s)" "\<forall>q<p. (P ! q) (L ! q) s"
          "\<forall>q<p. (P ! q) (L' ! q) s'" "product_ta \<turnstile> L \<longrightarrow>\<^bsup>g,(a, Syn (ci, mi) (co, mo)),r\<^esup> L'"
          "ci s" "co s"
          unfolding prod_trans_s_def by auto
        with prems have "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, Syn (ci, mi) (co, mo))\<^esub> \<langle>L', u'\<rangle>"
          unfolding inv_of_simp by - rule
        with product_action_sound[OF this] prems * show ?thesis
          apply (subst A_unfold)
          apply (rule conjI)
           apply (rule step_sn_s)
                apply (simp add: Len)+
          by blast
      qed
    qed
  qed
  
  lemmas prod_sound = prod_sound'[THEN conjunct1]
  lemmas prod_inv_1 = prod_sound'[THEN conjunct2, THEN conjunct1]
  lemmas prod_inv_2 = prod_sound'[THEN conjunct2, THEN conjunct2]

  lemma states_prod_step[intro]:
    "L' \<in> states" if "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
    using that by (intro states_product_step prod_inv_1)

  lemma inv_prod_step[intro]:
    "\<forall>p<length P. (P ! p) (L' ! p) s'" if "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow> \<langle>(L', s'), u'\<rangle>"
    using that by (intro states_product_step prod_inv_2)

  lemma prod_steps_sound:
    assumes step: "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>"
    shows "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>"
    using step states inv
  proof (induction A \<equiv> prod_ta l \<equiv> "(L, s)" _ l' \<equiv> "(L', s')" _ arbitrary: L s rule: steps.induct)
    case (refl u)
    then show ?case by blast
  next
    case prems: (step u l' u' u'' L s)
    obtain L'' s'' where "l' = (L'', s'')" by force
    interpret interp: Prod_TA A L s by (standard; rule prems Len)
    from prems(3)[OF \<open>l' = _\<close>] prems(1,2,4-) have *: "A \<turnstile> \<langle>L'', s'', u'\<rangle> \<rightarrow>* \<langle>L', s', u''\<rangle>"
      unfolding \<open>l' = _\<close> using  interp.inv_prod_step by auto
    show ?case
      apply (rule stepI2)
      using * prems by (auto simp: \<open>l' = _\<close> intro: interp.prod_sound)
  qed

  lemma prod_steps_complete:
    "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle>" if "A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>"
    using that states inv proof (induction A \<equiv> A L _ _ _ _ _ rule: steps_sn.induct)
    case (refl L s u)
    then show ?case by blast
  next
    case prems: (step L s u L' s' u' L'' s'' u'')
    interpret interp: Prod_TA A L' s' apply standard
      using prems by - (assumption | rule Prod_TA_Defs'.states_steps Len Prod_TA_Defs'.inv_steps)+
    from prems show ?case by - (rule steps_altI, auto intro!: interp.prod_complete)
  qed

  lemma prod_correct:
    "prod_ta \<turnstile> \<langle>(L, s), u\<rangle> \<rightarrow>* \<langle>(L', s'), u'\<rangle> \<longleftrightarrow> A \<turnstile> \<langle>L, s, u\<rangle> \<rightarrow>* \<langle>L', s', u'\<rangle>"
    by (metis prod_steps_complete prod_steps_sound)

  end (* End context: network + valid start state *)

end (* End of theory *)