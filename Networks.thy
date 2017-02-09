theory Networks
  imports Timed_Automata Normalized_Zone_Semantics_Impl
    "~/Formalizations/Experiments/Reordering_Quantifiers"
begin

no_notation Ref.update ("_ := _" 62)

section \<open>Networks of Timed Automata\<close>

subsection \<open>Syntax and Operational Semantics\<close>

text \<open>Input, output and internal transitions\<close>

datatype 'a act = In 'a | Out 'a | Sil 'a

datatype 'b label = Del | Act 'b | Syn 'b 'b

type_synonym
  ('a, 'b, 'c, 't, 's) nta = "('a act * 'b, 'c, 't, 's) ta list"

inductive step_n ::
  "('a, 'b, 'c, 't, 's) nta \<Rightarrow> 's list \<Rightarrow> ('c, ('t::time)) cval \<Rightarrow> 'b label
  \<Rightarrow> 's list \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>N \<langle>_, _\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>_,_\<rangle>" [61,61,61,61,61,61] 61)
where
  step_n_t:
    "\<lbrakk>\<forall> p \<in> {..<length N}. N!p \<turnstile> \<langle>L!p, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>L!p, u \<oplus> d\<rangle>; d \<ge> 0\<rbrakk>
    \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L, u \<oplus> d\<rangle>" |
  step_n_i:
    "\<lbrakk>
      N!p \<turnstile> l \<longrightarrow>\<^bsup>g,(Sil a, b),r\<^esup> l'; u \<turnstile> g; \<forall> p \<in> {..<length N}. u' \<turnstile> inv_of (N!p) (L'!p);
      L!p = l; p < length L; L' = L[p := l']; u' = [r\<rightarrow>0]u
     \<rbrakk>
    \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Act b\<^esub> \<langle>L', u'\<rangle>" |
  step_n_s:
    "\<lbrakk>N!p \<turnstile> l1 \<longrightarrow>\<^bsup>g1,(In a, b1),r1\<^esup> l1'; N!q \<turnstile> l2 \<longrightarrow>\<^bsup>g2,(Out a, b2),r2\<^esup> l2'; u \<turnstile> g1; u \<turnstile> g2;
      \<forall> p \<in> {..<length N}. u' \<turnstile> inv_of (N!p) (L'!p);
      L!p = l1; L!q = l2; p < length L; q < length L; p \<noteq> q;
      L' = L[p := l1', q := l2']; u' = [(r1 @ r2)\<rightarrow>0]u
     \<rbrakk> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Syn b1 b2\<^esub> \<langle>L', u'\<rangle>"

inductive_cases[elim!]: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', u'\<rangle>"

inductive steps_n ::
  "('a, 'b, 'c, 't, 's) nta \<Rightarrow> 's list \<Rightarrow> ('c, ('t::time)) cval
  \<Rightarrow> 's list \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>N \<langle>_, _\<rangle> \<rightarrow>* \<langle>_,_\<rangle>" [61,61,61] 61)
where
  refl: "N \<turnstile>\<^sub>N \<langle>l, Z\<rangle> \<rightarrow>* \<langle>l, Z\<rangle>" |
  step: "N \<turnstile>\<^sub>N \<langle>l, Z\<rangle> \<rightarrow>* \<langle>l', Z'\<rangle> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>l', Z'\<rangle> \<rightarrow>\<^bsub>_\<^esub> \<langle>l'', Z''\<rangle>
        \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>l, Z\<rangle> \<rightarrow>* \<langle>l'', Z''\<rangle>"

declare steps_n.intros[intro]

lemma stepI2:
  "N \<turnstile>\<^sub>N \<langle>l, Z\<rangle> \<rightarrow>* \<langle>l'', Z''\<rangle>" if "N \<turnstile>\<^sub>N \<langle>l', Z'\<rangle> \<rightarrow>* \<langle>l'', Z''\<rangle>" "N \<turnstile>\<^sub>N \<langle>l, Z\<rangle> \<rightarrow>\<^bsub>b\<^esub> \<langle>l', Z'\<rangle>"
  using that
  apply induction
   apply rule
    apply (rule refl)
   apply assumption
  apply simp
  by (rule; assumption)

lemma step_n_t_I:
  "\<lbrakk>\<forall> p \<in> {..<length N}. u \<turnstile> inv_of (N!p) (L!p); \<forall> p \<in> {..<length N}. u \<oplus> d \<turnstile> inv_of (N!p) (L!p);
    d \<ge> 0
   \<rbrakk> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L, u \<oplus> d\<rangle>"
by (auto intro: step_n_t)

subsection \<open>Product Automaton\<close>

abbreviation state_set :: "('a, 'c, 'time, 's) transition set \<Rightarrow> 's set" where
  "state_set T \<equiv> fst ` T \<union> (snd o snd o snd o snd) ` T"

lemma guard_concat:
  assumes "\<forall> g \<in> set xs. u \<turnstile> g"
  shows "u \<turnstile> concat xs"
using assms by (induction xs) auto

lemma concat_guard:
  assumes "u \<turnstile> concat xs" "g \<in> set xs"
  shows "u \<turnstile> g"
using assms by (auto simp: list_all_iff)

lemma lists_of_len_finite:
  assumes "finite S"
  shows "finite {xs. set xs \<subseteq> S \<and> length xs = n}"
  using assms by (rule finite_lists_length_eq)

(* XXX Move? *)
lemma list_update_nth_split:
  assumes "j < length xs"
  shows "P (xs[i := x] ! j) = ((i = j \<longrightarrow> P x) \<and> (i \<noteq> j \<longrightarrow> P (xs ! j)))"
    using assms by (cases "i = j") auto

locale Product_TA_Defs =
  fixes N :: "('a, 'b, 'c, 't, 's) nta"
begin

  abbreviation "T \<equiv> map trans_of N"
  abbreviation "I \<equiv> map inv_of N"

  definition "states = {L. length L = length T \<and> (\<forall> p \<in> {..<length T}. L!p \<in> state_set (T!p))}"

  definition
    "product_trans_i =
      {(L,g,(a,Act b),r,L[p:=l']) | L p g a b r l'.
      L \<in> states \<and> (L!p, g, (Sil a, b), r, l') \<in> T!p \<and> p < length L}"

  definition
    "product_trans_s =
      {(L,g1 @ g2,(a,Syn b1 b2),r1 @ r2,L[p:=l1',q:=l2']) | L p q g1 g2 a b1 b2 r1 r2 l1' l2'.
        L \<in> states \<and> (L!p, g1, (In a, b1), r1, l1') \<in> T!p \<and> (L!q, g2, (Out a, b2), r2, l2') \<in> T!q
        \<and> p < length L \<and> q < length L \<and> p \<noteq> q
      }"

  definition
    "product_trans \<equiv> product_trans_i \<union> product_trans_s"

lemma *:
  "length T = length N"
  by simp

lemma product_state_set_subs:
  assumes "q < length N" "l \<in> state_set product_trans"
  shows "l ! q \<in> state_set (T ! q)"
  using assms
  unfolding product_trans_def product_trans_i_def product_trans_s_def states_def
  apply safe
     apply (auto; fail)
    apply (auto; fail)
  apply simp
   apply (subst list_update_nth_split; force) (* XXX Slow *)
  apply simp
  apply (subst list_update_nth_split)
   apply simp
  apply safe
   apply (subst (asm) (2) list_update_nth_split; force)
  apply (subst list_update_nth_split)
   apply simp
  by (subst (asm) (2) list_update_nth_split; force)  (* XXX Slow *)

  definition
    "product_invariant L \<equiv>
    concat (map (\<lambda> p. if p < length I then (I!p) (L!p) else []) [0..<length L])"

  definition product_ta :: "('a \<times> 'b label, 'c, 't, 's list) ta" where
    "product_ta \<equiv> (product_trans, product_invariant)"

  lemma collect_clki_product_invariant:
    "collect_clki product_invariant = \<Union> (collect_clki ` set I)"
    unfolding collect_clki_def product_invariant_def
    apply (simp add: image_Union)
    apply safe
    subgoal
      unfolding collect_clock_pairs_def by fastforce
    apply clarsimp
    subgoal premises prems for a b aa ba x
    proof -
      let ?L = "map (\<lambda> _. x) [0..<length N]"
      let ?x = "collect_clock_pairs
        (concat
        (map (\<lambda>p. if p < length N then (I ! p) (?L ! p) else [])
        [0..<length ?L]))"
      show ?thesis
        apply (rule exI[where x = ?x])
        apply rule
         apply (rule exI; rule HOL.refl)
        apply simp
        using prems unfolding collect_clock_pairs_def by (fastforce dest: aux)
    qed
    done

  lemma states_length:
    assumes "L \<in> states"
    shows "length L = length N"
    using assms unfolding states_def by auto

  lemma collect_clock_pairs_append_cases:
    assumes "x \<in> collect_clock_pairs (g1 @ g2)"
    shows "x \<in> collect_clock_pairs g1 \<or> x \<in> collect_clock_pairs g2"
      using assms unfolding collect_clock_pairs_def by auto

  lemma collect_clkt_product_trans_subs:
    "collect_clkt product_trans \<subseteq> \<Union> (collect_clkt ` set T)"
    unfolding collect_clkt_def product_trans_def product_trans_i_def product_trans_s_def
    by (fastforce dest: collect_clock_pairs_append_cases states_length)

  lemma collect_clkvt_product_trans_subs:
    "collect_clkvt product_trans \<subseteq> \<Union> (collect_clkvt ` set T)"
    unfolding collect_clkvt_def product_trans_def product_trans_i_def product_trans_s_def
    by (fastforce dest: states_length)

  (* XXX No conditional split *)
  lemma statesI_aux:
    fixes L
    assumes L: "L \<in> states"
    assumes
      "p < length T"
      "(l, g, a, r, l') \<in> T ! p"
    shows "(L[p := l]) \<in> states"
    unfolding states_def apply clarsimp
    apply rule
    using L apply (simp add: states_def)
    apply rule
    apply (subst list_update_nth_split)
    using assms apply (auto simp: states_def)
    by blast

  lemma product_trans_s_alt_def:
    "product_trans_s =
      {(L, g, (a, Syn b1 b2), r, L') | L g a b1 b2 r L'. \<exists> p q g1 g2 r1 r2 l1' l2'.
      L \<in> states \<and> p < length L \<and> q < length L \<and> p \<noteq> q \<and>
      g = g1 @ g2 \<and> r = r1 @ r2 \<and> L' = L[p:=l1', q:=l2']
        \<and> (L!p, g1, (In a, b1), r1, l1') \<in> T!p \<and> (L!q, g2, (Out a, b2), r2, l2') \<in> T!q
      }"
    unfolding product_trans_s_def by (safe; metis)

  context
    assumes states_not_empty: "states \<noteq> {}"
    assumes trans_complete:
      "\<forall> p < length T. \<forall> t1 \<in> T ! p. case t1 of (l1, g1, (In a, b1), r1, l1')
      \<Rightarrow> \<exists> q < length T. p \<noteq> q \<and> (\<exists> l2 g2 b2 r2 l2'. (l2, g2, (Out a, b2), r2, l2') \<in> T ! q) |
      (l1, g1, (Out a, b1), r1, l1')
      \<Rightarrow> \<exists> q < length T. p \<noteq> q \<and> (\<exists> l2 g2 b2 r2 l2'. (l2, g2, (In a, b2), r2, l2') \<in> T ! q) | _ \<Rightarrow> True"
  begin

  lemma collect_clkt_product_trans_sups:
    "collect_clkt product_trans \<supseteq> \<Union> (collect_clkt ` set T)"
  proof
    fix x assume "x \<in> \<Union> (collect_clkt ` set T)"
    then obtain trans l1 g1 a' b1 r1 l1' where x:
      "trans \<in> set T" "(l1, g1, (a', b1), r1, l1') \<in> trans" "x \<in> collect_clock_pairs g1"
      unfolding collect_clkt_def by force
    then obtain p where p:
        "p < length T" "T ! p = trans"
      by (auto dest!: aux)
    from states_not_empty obtain L where L: "L \<in> states" by auto
    have "length T = length L" by (auto simp: states_length[OF \<open>L \<in> states\<close>])
    show "x \<in> collect_clkt product_trans"
    proof (cases a')
      case a': (In a)
      with x p trans_complete obtain q l2 g2 b2 r2 l2' where trans2:
        "q < length T" "(l2, g2, (Out a, b2), r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      have "L[p := l1, q := l2] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      moreover note t = calculation
      have "(?L, g1 @ g2, (a, Syn b1 b2), r1 @ r2, ?L[p := l1', q := l2']) \<in> product_trans_s"
        unfolding product_trans_s_alt_def
        apply clarsimp
        using t p(1) x(1,2) trans2 unfolding p(2)[symmetric] a' \<open>length T = length L\<close>
        by metis
      moreover have "x \<in> collect_clock_pairs (g1 @ g2)"
        using x(3) by (auto simp: collect_clock_pairs_def)
      ultimately show ?thesis unfolding collect_clkt_def product_trans_def by force
    next
      case a': (Out a)
      with x p trans_complete obtain q l2 g2 b2 r2 l2' where trans2:
        "q < length T" "(l2, g2, (In a, b2), r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      have "L[q := l2, p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      moreover note t = calculation
      have "(?L, g2 @ g1, (a, Syn b2 b1), r2 @ r1, ?L[q := l2', p := l1']) \<in> product_trans_s"
        unfolding product_trans_s_alt_def
        apply clarsimp
        using t p(1) x(1,2) trans2 unfolding p(2)[symmetric] a' \<open>length T = length L\<close>
        by metis
      moreover have "x \<in> collect_clock_pairs (g2 @ g1)"
        using x(3) by (auto simp: collect_clock_pairs_def)
      ultimately show ?thesis unfolding collect_clkt_def product_trans_def by force
    next
      case a': (Sil a)
      have "L[p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1"
        using \<open>p < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g1, (a, Act b1), r1, ?L[p := l1']) \<in> product_trans_i"
        using x p unfolding product_trans_i_def a' by (force simp: states_length[OF \<open>L \<in> states\<close>])
      with x(3) show ?thesis unfolding collect_clkt_def product_trans_def by force
    qed
  qed

  lemma collect_clkvt_product_trans_sups:
    "collect_clkvt product_trans \<supseteq> \<Union> (collect_clkvt ` set T)"
  proof
    fix x assume "x \<in> \<Union> (collect_clkvt ` set T)"
    then obtain trans l1 g1 a' b1 r1 l1' where x:
      "trans \<in> set T" "(l1, g1, (a', b1), r1, l1') \<in> trans" "x \<in> set r1"
      unfolding collect_clkvt_def by force
    then obtain p where p:
        "p < length T" "T ! p = trans"
      by (auto dest!: aux)
    from states_not_empty obtain L where L: "L \<in> states" by auto
    show "x \<in> collect_clkvt product_trans"
    proof (cases a')
      case a': (In a)
      with x p trans_complete obtain q l2 g2 b2 r2 l2' where trans2:
        "q < length T" "(l2, g2, (Out a, b2), r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      moreover have "L[p := l1, q := l2] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have
        "(?L, g1 @ g2, (a, Syn b1 b2), r1 @ r2, ?L[p := l1', q := l2']) \<in> product_trans_s"
        using p(1) x trans2 unfolding p(2)[symmetric] a' product_trans_s_def
        by (fastforce simp: states_length[OF \<open>L \<in> states\<close>])
      with x(3) show ?thesis unfolding collect_clkvt_def product_trans_def by force
    next
      case a': (Out a)
      with x p trans_complete obtain q l2 g2 b2 r2 l2' where trans2:
        "q < length T" "(l2, g2, (In a, b2), r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      moreover have "L[q := l2, p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g2 @ g1, (a, Syn b2 b1), r2 @ r1, ?L[q := l2', p := l1']) \<in> product_trans_s"
        using p(1) x trans2 unfolding p(2)[symmetric] a' product_trans_s_def
        apply (simp add: states_length[OF \<open>L \<in> states\<close>] del: ex_simps)
        apply (tactic \<open>rearrange_ex_tac @{context} 1\<close>)
        apply simp
        apply (rule exI, rule conjI, assumption)
        apply (simp only: ex_simps[symmetric])
        apply (tactic \<open>rearrange_ex_tac @{context} 1\<close>)
        apply simp
        by (fastforce simp: states_length[OF \<open>L \<in> states\<close>])
          (* fastforce can solve this on its own but not very quickly *)
      with x(3) show ?thesis unfolding collect_clkvt_def product_trans_def by force
    next
      case a': (Sil a)
      have "L[p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1"
        using \<open>p < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g1, (a, Act b1), r1, ?L[p := l1']) \<in> product_trans_i"
        using x p unfolding product_trans_i_def a' by (force simp: states_length[OF \<open>L \<in> states\<close>])
      with x(3) show ?thesis unfolding collect_clkvt_def product_trans_def by force
    qed
  qed

  lemma collect_clkt_product_trans:
    "collect_clkt product_trans = \<Union> (collect_clkt ` set T)"
    using collect_clkt_product_trans_sups collect_clkt_product_trans_subs by simp

  lemma collect_clkvt_product_trans:
    "collect_clkvt product_trans = \<Union> (collect_clkvt ` set T)"
  using collect_clkvt_product_trans_sups collect_clkvt_product_trans_subs by simp

  end (* End of context for syntactic 1-to-1 correspondence for transitions *)

  context
    assumes finite_trans: "\<forall> A \<in> set N. finite (trans_of A)"
  begin

  lemma finite_states:
    "finite states"
  proof -
    have "states \<subseteq> {L.
        set L \<subseteq>
          (\<Union> {fst ` trans_of (N ! p) | p. p < length N} \<union> \<Union> {(snd \<circ> snd \<circ> snd \<circ> snd) ` trans_of (N ! p) | p. p < length N})
          \<and> length L = length N}"
      unfolding states_def
      apply clarsimp
      apply (drule aux)
      apply safe
      subgoal for _ _ i
        by (erule ballE[where x = i]) auto
      done
    moreover have "finite \<dots>" using finite_trans by - (rule finite_lists_length_eq; auto)
    ultimately show ?thesis by (rule finite_subset)
  qed

  lemma finite_product_trans_i:
    "finite product_trans_i"
  proof -
    let ?N = "\<Union> (trans_of ` set N)"
    let ?S = "{(L, p, g, (a, Act b), r, l')|L p g a b r l'.
      L \<in> states \<and> (L ! p, g, (Sil a, b), r, l') \<in> map trans_of N ! p \<and> p < length L}"
    let ?R = "{(L, p, g, (a, Act b), r, l')|L p g a b r l'.
      L \<in> states \<and> p < length L \<and> (g, (Sil a, b), r, l') \<in> snd ` ?N}"
    have "?S \<subseteq> ?R" by (fastforce simp: states_length dest: nth_mem)
    moreover have "finite ?R" using finite_states [[simproc add: finite_Collect]]
      apply simp
      apply rule
      apply rule
       apply (rule finite_subset[where B = "{(p, L). p < length L \<and> L \<in> states}"])
        apply force
      using states_length
        (* XXX Perfect situation for a finiteness cong *)
       apply -
       apply (rule finite_subset[where B = "{(p, L). p < length N \<and> L \<in> states}"]; fastforce)
      using finite_trans
      apply -
      apply auto[]
      apply (rule finite_vimageI)
       apply (auto; fail)
      unfolding inj_on_def
      by (auto; fail)
    ultimately have "finite ?S" by (rule finite_subset)
    moreover have "product_trans_i = (\<lambda> (L, p, g, a, r, l'). (L, g, a, r, L[p := l'])) ` ?S"
      unfolding product_trans_i_def apply (rule; rule)
       apply simp
       apply safe[]
       apply (fastforce simp: image_Collect)
      by force
    ultimately show ?thesis by auto
  qed

lemma
  assumes A: "finite A"
  shows "finite {(a,b,c) | a b c. a \<in> A \<and> b < (n :: nat) \<and> P c}"
  using assms [[simproc add: finite_Collect]] apply simp
  oops

lemma
  assumes A: "finite A"
  shows "finite {(d, c, a, b) | a b c d. d < n \<and> P c \<and> (a, b) \<in> A}"
  using assms
  using [[simproc add: finite_Collect]] apply simp
  oops

  thm Finite_Set.finite_Collect_bounded_ex

lemma
  assumes A: "finite A"
  shows "finite {t. \<exists> a c. a \<in> A \<and> P c \<and> t = (a,c)}"
  using [[simp_trace]] apply simp
  oops


  (*
  lemma finite_product_trans_s:
    "finite product_trans_s"
  proof -
    let ?N = "\<Union> (trans_of ` set N)"
    (* XXX Possible intro weakening for finiteness method *)
    have "(g1, In a, r1, l1') \<in> snd ` ?N" if
      "(L ! p, g1, In a, r1, l1') \<in> map trans_of N ! p" "p < length L" "L \<in> states"
      for L p g1 a r1 l1'
      using that by (auto simp: states_length dest: nth_mem)
    let ?S = "{(L, p, q, g1, g2, a, r1, r2, l1', l2')|L p q g1 g2 a r1 r2 l1' l2'.
      L \<in> states \<and> (L ! p, g1, In a, r1, l1') \<in> map trans_of N ! p \<and>
        (L ! q, g2, Out a, r2, l2') \<in> map trans_of N ! q \<and> p < length L \<and> q < length L}"
    have S_alt_def: "?S = {t. \<exists> L p q g1 g2 a r1 r2 l1' l2'.
      L \<in> states \<and> (L ! p, g1, In a, r1, l1') \<in> map trans_of N ! p \<and>
        (L ! q, g2, Out a, r2, l2') \<in> map trans_of N ! q \<and> p < length L \<and> q < length L
        \<and> t = (L, p, q, g1, g2, a, r1, r2, l1', l2')}" by auto
    have "finite ?S"
      unfolding S_alt_def using finite_states
      supply [[simproc add: ex_reorder]]
      apply simp
      apply clarsimp
      apply (simp only: ex_simps[symmetric])
      oops
      supply [[simproc del: ex_reorder]]
      apply simp

    define F1 where "F1 \<equiv> {(g1, a, r1, l1') | g1 a r1 l1'. (g1, In a, r1, l1') \<in> snd ` ?N}"
    have fin1: "finite F1" unfolding F1_def using finite_trans
      using [[simproc add: finite_Collect]] by (auto simp: inj_on_def intro: finite_vimageI)
    define F2 where "F2 \<equiv> {(g1, a, r1, l1') | g1 a r1 l1'. (g1, Out a, r1, l1') \<in> snd ` ?N}"
    have fin2: "finite F2" unfolding F2_def using finite_trans
      using [[simproc add: finite_Collect]] by (auto simp: inj_on_def intro: finite_vimageI)
    define R where "R \<equiv> {(L, p, q, g1, g2, a, r1, r2, l1', l2')|L p q g1 g2 a r1 r2 l1' l2'.
      L \<in> states \<and> p < length L \<and> q < length L \<and> (g1, a, r1, l1') \<in> F1 \<and> (g2, a, r2, l2') \<in> F2}"

    have R_alt_def: "R = {t. \<exists> L p q g1 a r1 l1' g2 r2 l2'.
      L \<in> states \<and> p < length L \<and> q < length L
      \<and> (g1, a, r1, l1') \<in> F1 \<and> (g2, a, r2, l2') \<in> F2
      \<and> t = (L, p, q, g1, g2, a, r1, r2, l1', l2')
      }"
      unfolding R_def by auto
    have "?S \<subseteq> R" by (fastforce simp: R_alt_def F1_def F2_def states_length dest: nth_mem)
    moreover have "finite R"
      unfolding R_alt_def
      using fin1 fin2 finite_states
      using [[simproc add: finite_Collect]]
      by (auto simp: inj_on_def intro: finite_vimageI intro!: finite_imageI)
    ultimately have "finite ?S" by (rule finite_subset)
    moreover have
      "product_trans_s
      \<subseteq> (\<lambda> (L, p, q, g1, g2, a, r1, r2, l1', l2'). (L, g1 @ g2, a, r1 @ r2, L[p := l1', q := l2'])) ` ?S"
      unfolding product_trans_s_def apply (rule)
       apply simp
       apply safe[]
      subgoal for a aa ab ac b L p q g1 g2 ad r1 r2 l1' l2'
        apply (rule image_eqI[where x = "(L, p, q, g1, g2, ad, r1, r2, l1', l2')"])
        by auto
      done
    ultimately show ?thesis by (auto intro: finite_subset)
  qed
*)

  lemma finite_Collect_bounded_ex_5' [simp]:
  assumes "finite {(a,b,c,d,e) . P a b c d e}"
  shows
    "finite {x. \<exists>a b c d e. P a b c d e \<and> Q x a b c d e}
    \<longleftrightarrow> (\<forall> a b c d e. P a b c d e \<longrightarrow> finite {x. Q x a b c d e})"
  using assms finite_Collect_bounded_ex[OF assms, where Q = "\<lambda> x. \<lambda> (a, b, c, d, e). Q x a b c d e"]
  by clarsimp (* force, simp *)

  lemma finite_product_trans_s:
    "finite product_trans_s"
  proof -
    let ?N = "\<Union> (trans_of ` set N)"
    (* XXX Possible intro weakening for finiteness method *)
    have "(g1, (In a, b), r1, l1') \<in> snd ` ?N" if
      "(L ! p, g1, (In a, b), r1, l1') \<in> map trans_of N ! p" "p < length L" "L \<in> states"
      for L p g1 a b r1 l1'
      using that by (auto simp: states_length dest: nth_mem)
    let ?S = "{(L, p, q, g1, g2, (a, Syn b1 b2), r1, r2, l1', l2')|L p q g1 g2 a b1 b2 r1 r2 l1' l2'.
      L \<in> states \<and> (L ! p, g1, (In a, b1), r1, l1') \<in> map trans_of N ! p \<and>
        (L ! q, g2, (Out a, b2), r2, l2') \<in> map trans_of N ! q \<and> p < length L \<and> q < length L}"
    define F1 where "F1 \<equiv> {(g1, a, b, r1, l1') | g1 a b r1 l1'. (g1, (In a, b), r1, l1') \<in> snd ` ?N}"
    have fin1: "finite F1" unfolding F1_def using finite_trans
      using [[simproc add: finite_Collect]] by (force simp: inj_on_def intro: finite_vimageI)
    define F2 where "F2 \<equiv> {(g1, a, b, r1, l1') | g1 a b r1 l1'. (g1, (Out a, b), r1, l1') \<in> snd ` ?N}"
    have fin2: "finite F2" unfolding F2_def using finite_trans
      using [[simproc add: finite_Collect]] by (force simp: inj_on_def intro: finite_vimageI)
    define R where "R \<equiv> {(L, p, q, g1, g2, (a, Syn b1 b2), r1, r2, l1', l2')|L p q g1 g2 a b1 b2 r1 r2 l1' l2'.
      L \<in> states \<and> p < length L \<and> q < length L \<and> (g1, a, b1, r1, l1') \<in> F1 \<and> (g2, a, b2, r2, l2') \<in> F2}"

    (* XXX Term for demonstrating miniscoping imperfections *)
    term "finite
        {t. \<exists>g1 a b1 b2 r1 l1'.
               (g1, a, b1, r1, l1') \<in> F1 \<and>
               (\<exists>g2 r2 l2'.
                   (g2, a, b2, r2, l2') \<in> F2 \<and>
                   t = (L, p, q, g1, g2, (a, Syn b1 b2), r1, r2, l1', l2'))}"

    have R_alt_def: "R = {t. \<exists> L p q g1 a b1 r1 l1' g2 b2 r2 l2'.
      L \<in> states \<and> p < length L \<and> q < length L
      \<and> (g1, a, b1, r1, l1') \<in> F1 \<and> (g2, a, b2, r2, l2') \<in> F2
      \<and> t = (L, p, q, g1, g2, (a, Syn b1 b2), r1, r2, l1', l2')
      }"
      unfolding R_def by auto
    have "?S \<subseteq> R" by (fastforce simp: R_alt_def F1_def F2_def states_length dest: nth_mem)
    moreover have "finite R"
      unfolding R_alt_def
      using fin1 fin2 finite_states
      apply simp (* XXX For illustration purposes *)
      using [[simproc add: finite_Collect]]
      by (auto simp: inj_on_def intro: finite_vimageI intro!: finite_imageI)
    ultimately have "finite ?S" by (rule finite_subset)
    moreover have
      "product_trans_s
      \<subseteq> (\<lambda> (L, p, q, g1, g2, a, r1, r2, l1', l2'). (L, g1 @ g2, a, r1 @ r2, L[p := l1', q := l2'])) ` ?S"
      unfolding product_trans_s_def by (simp add: image_Collect) blast
    ultimately show ?thesis by (auto intro: finite_subset)
  qed

  lemma finite_trans_of_product:
    shows "finite (trans_of product_ta)"
    using finite_product_trans_s finite_product_trans_i
    unfolding product_ta_def trans_of_def product_trans_def
    by auto

  end (* End of context for finiteness of trans *)

  lemma inv_of_product[simp]:
      "inv_of product_ta = product_invariant"
    unfolding product_ta_def inv_of_def by simp

  (* XXX Move? *)
  lemma concat_map_if_aux:
    assumes "(m :: nat) \<ge> n"
    shows "concat (map (\<lambda> i. if i < n then f i else []) [0..<m])
         = concat (map (\<lambda> i. if i < n then f i else []) [0..<n])"
    using assms by (induction rule: dec_induct) auto

  lemma finite_invariant_of_product[folded inv_of_product]:
    assumes "\<forall> A \<in> set N. finite (range (inv_of A))"
    shows "finite (range product_invariant)"
  proof -
    let ?N = "\<Union> (range ` inv_of ` set N)"
    let ?X = "{I. set I \<subseteq> ?N \<and> length I \<le> length N}"
    have "[] \<in> ?X" by auto
    have "finite ?N"
      using assms
      by auto
    then have "finite ?X" by (rule finite_lists_length_le)
    moreover have "range product_invariant \<subseteq> concat ` ?X"
    proof
      fix x assume "x \<in> range product_invariant"
      then obtain L where L:
            "x = concat
                       (map (\<lambda>p. if p < length (map inv_of N)
                                  then (map inv_of N ! p) (L ! p) else [])
                         [0..<length L])"
        unfolding product_invariant_def by auto
      show "x \<in> concat ` ?X"
      proof (cases "length L \<le> length N")
        case True
        then show ?thesis using L by (fastforce dest: nth_mem)
      next
        case False
        then have "x = concat
                       (map (\<lambda>p. if p < length (map inv_of N)
                                  then (map inv_of N ! p) (L ! p) else [])
                         [0..<length N])"
          using L by (auto intro: concat_map_if_aux)
        then show ?thesis by (fastforce dest: nth_mem)
      qed
    qed
    ultimately show ?thesis by - (drule finite_subset; auto)
  qed

end (* End locale for product TA definition *)

locale Product_TA_Defs' =
  Product_TA_Defs N for N :: "('a, 'b, 'c, 't :: time, 's) nta"
begin

  lemma product_invariantD:
    assumes "u \<turnstile> product_invariant L" "p < length N" "length L = length N"
    shows "u \<turnstile> inv_of (N ! p) (L!p)"
  using assms unfolding product_invariant_def by (force intro: concat_guard)

  lemma states_step:
    "L' \<in> states" if "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', u'\<rangle>" "L \<in> states"
    using that unfolding states_def apply safe
        apply simp
       apply simp
      apply force
     apply (subst list_update_nth_split)
      apply simp
     apply rule
      apply clarsimp
    subgoal premises prems for p g a r l'
      using prems(3-6) by force
     apply clarsimp
     apply (auto; fail)
    apply (subst list_update_nth_split)
     apply (simp; fail)
    apply safe
     apply simp
    subgoal premises prems
      using prems(3-7) by force
    apply (subst list_update_nth_split)
     apply simp
    apply safe
     apply simp
    subgoal premises prems
      using prems(3-6) by force
    by auto

  lemma states_steps:
    "L' \<in> states" if "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>" "L \<in> states"
    using that apply (induction N \<equiv> N _ _ _ _ rule: steps_n.induct)
     apply assumption
    apply simp
    by (rule states_step; assumption)

end

lemma steps_altI:
  "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>* \<langle>l'', Z''\<rangle>" if
  "A \<turnstile> \<langle>l, Z\<rangle> \<rightarrow>* \<langle>l', Z'\<rangle>" "A \<turnstile> \<langle>l', Z'\<rangle> \<rightarrow> \<langle>l'', Z''\<rangle>"
  using that by (induction; blast)

(* Network + valid start state *)
locale Product_TA =
  Product_TA_Defs' N for N :: "('a, 'b, 'c, 't :: time, 's) nta" +
  fixes L :: "'s list"
  assumes states[intro]: "L \<in> states"
begin

  lemma
    len[simp]: "length L = length N"
  using states unfolding states_def by auto

  lemma product_delay_complete:
    assumes step: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', u'\<rangle>"
    obtains d where "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>L', u'\<rangle>"
  using step proof cases
    case prems: (step_n_t d)
    from prems have *:
      "\<forall>p\<in>{..<length N}. u \<oplus> d \<turnstile> inv_of (N ! p) (L ! p)"
    by auto
    from prems * show ?thesis
    by (fastforce simp add: product_ta_def inv_of_def product_invariant_def[abs_def]
                  intro!: guard_concat that
       )
  qed

  lemma product_int_complete:
    assumes step: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Act b\<^esub> \<langle>L', u'\<rangle>"
    obtains a where "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, Act b)\<^esub> \<langle>L', u'\<rangle>"
    using step proof cases
    case prems: (step_n_i p l g a r l')
    from prems show ?thesis
      apply -
      apply (rule that)
      apply (rule step_a.intros[where g = g and r = r])
      by (fastforce
          simp: product_trans_def product_trans_i_def product_invariant_def product_ta_def
          trans_of_def inv_of_def
          intro: guard_concat
          )+
  qed

  lemma product_sync_complete:
    assumes step: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Syn b1 b2\<^esub> \<langle>L', u'\<rangle>"
    obtains a where "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, Syn b1 b2)\<^esub> \<langle>L', u'\<rangle>"
    using step proof cases
    case prems: (step_n_s p l1 g1 a r1 l1' q l2 g2 r2 l2')
    from prems show ?thesis
      apply -
      apply (rule that)
      apply (rule step_a.intros[where g = "g1 @ g2" and a = "(a, Syn b1 b2)" and r = "r1 @ r2"])
      subgoal premises prems
        apply
          (auto simp add:
            product_trans_def product_trans_s_def product_invariant_def product_ta_def
            trans_of_def inv_of_def
            )
        apply (erule allE[where x = p])
        using \<open>p < _\<close> apply simp
        apply (erule allE[where x = q])
        using prems by (fastforce simp: trans_of_def)
      by (fastforce simp: product_invariant_def product_ta_def inv_of_def intro: guard_concat)+
  qed

  lemma product_complete:
    assumes step: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>b\<^esub> \<langle>L', u'\<rangle>"
    shows "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    using step
    by (cases b) (rule product_delay_complete product_int_complete product_sync_complete, simp, blast)+

  lemma product_ta_cases:
    assumes "product_ta \<turnstile> L \<longrightarrow>\<^bsup>g,a,r\<^esup> L'"
    shows "(L, g, a, r, L') \<in> product_trans_i \<or> (L, g, a, r, L') \<in> product_trans_s"
  using assms unfolding product_ta_def trans_of_def product_trans_def by auto

  lemma product_delay_sound:
    assumes step: "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>L', u'\<rangle>"
    shows "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>Del\<^esub> \<langle>L', u'\<rangle>"
  using assms by cases (force intro!: step_n_t product_invariantD len)

  lemma product_action_sound:
    assumes step: "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>\<^bsub>(a, b)\<^esub> \<langle>L', u'\<rangle>"
    shows "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>b\<^esub> \<langle>L', u'\<rangle>"
    using assms
    apply cases
    apply simp
    apply (drule product_ta_cases)
    apply (erule disjE)
    unfolding product_trans_i_def product_trans_s_def
     apply (clarsimp; auto intro!: product_invariantD step_n_i; fail)
    by (clarsimp; auto intro!: product_invariantD step_n_s)

  lemma product_sound:
    assumes step: "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    obtains a where "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>\<^bsub>a\<^esub> \<langle>L', u'\<rangle>"
    using step by cases (force dest!: product_action_sound product_delay_sound)+

  lemma states_product_step[intro]:
    "L' \<in> states" if "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    by (auto intro: product_sound that elim!: states_step)

  lemma product_steps_sound:
    "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>" if "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>"
    using that states proof (induction A \<equiv> product_ta _ _ _ _ rule: steps.induct)
    case (refl l u)
    then show ?case by blast
  next
    case prems: (step l u l' u' l'' u'')
    interpret interp: Product_TA N l by standard (rule prems)
    from prems have *: "N \<turnstile>\<^sub>N \<langle>l', u'\<rangle> \<rightarrow>* \<langle>l'',u''\<rangle>" by auto
    from prems show ?case by - (erule interp.product_sound, rule stepI2, rule *)
  qed

  lemma product_steps_complete:
    "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>" if "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>"
    using that states proof (induction N \<equiv> N _ _ _ _ rule: steps_n.induct)
    case (refl l Z)
    then show ?case by blast
  next
    case prems: (step l Z l' Z' _ l'' Z'')
    interpret interp: Product_TA N l' by standard (blast intro: prems states_steps)
    from prems show ?case by - (assumption | rule steps_altI interp.product_complete)+
  qed

  lemma product_correct:
    "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle> \<longleftrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow>* \<langle>L', u'\<rangle>"
    by (metis product_steps_complete product_steps_sound)

  end (* End context: network + valid start state *)

end (* End of theory *)