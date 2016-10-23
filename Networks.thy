theory Networks
  imports Timed_Automata Normalized_Zone_Semantics_Impl
begin

no_notation Ref.update ("_ := _" 62)

section \<open>Networks of Timed Automata\<close>

subsection \<open>Syntax and Operational Semantics\<close>

text \<open>Input, output and internal transitions\<close>

datatype 'a act = In 'a | Out 'a | Sil 'a

type_synonym
  ('a, 'c, 't, 's) nta = "('a act, 'c, 't, 's) ta list"

inductive step_n ::
  "('a, 'c, 't, 's) nta \<Rightarrow> 's list \<Rightarrow> ('c, ('t::time)) cval
  \<Rightarrow> 's list \<Rightarrow> ('c, 't) cval \<Rightarrow> bool"
("_ \<turnstile>\<^sub>N \<langle>_, _\<rangle> \<rightarrow> \<langle>_,_\<rangle>" [61,61,61] 61)
where
  step_n_t:
    "\<lbrakk>\<forall> p \<in> {..<length N}. N!p \<turnstile> \<langle>L!p, u\<rangle> \<rightarrow>\<^bsup>d\<^esup> \<langle>L!p, u \<oplus> d\<rangle>; d \<ge> 0\<rbrakk>
    \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L, u \<oplus> d\<rangle>" |
  step_n_i:
    "\<lbrakk>
      N!p \<turnstile> l \<longrightarrow>\<^bsup>g,Sil a,r\<^esup> l'; u \<turnstile> g; \<forall> p \<in> {..<length N}. u' \<turnstile> inv_of (N!p) (L'!p);
      L!p = l; p < length L; L' = L[p := l']; u' = [r\<rightarrow>0]u
     \<rbrakk>
    \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>" |
  step_n_s:
    "\<lbrakk>N!p \<turnstile> l1 \<longrightarrow>\<^bsup>g1,In a,r1\<^esup> l1'; N!q \<turnstile> l2 \<longrightarrow>\<^bsup>g2,Out a,r2\<^esup> l2'; u \<turnstile> g1; u \<turnstile> g2;
      \<forall> p \<in> {..<length N}. u' \<turnstile> inv_of (N!p) (L'!p);
      L!p = l1; L!q = l2; p < length L; q < length L; p \<noteq> q;
      L' = L[p := l1', q := l2']; u' = [(r1 @ r2)\<rightarrow>0]u
     \<rbrakk> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"

inductive_cases[elim!]: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"

lemma step_n_t_I:
  "\<lbrakk>\<forall> p \<in> {..<length N}. u \<turnstile> inv_of (N!p) (L!p); \<forall> p \<in> {..<length N}. u \<oplus> d \<turnstile> inv_of (N!p) (L!p);
    d \<ge> 0
   \<rbrakk> \<Longrightarrow> N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L, u \<oplus> d\<rangle>"
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

locale Product_TA_Defs =
  fixes N :: "('a, 'c, 't, 's) nta"
begin

  abbreviation "T \<equiv> map trans_of N"
  abbreviation "I \<equiv> map inv_of N"

  definition "states = {L. length L = length T \<and> (\<forall> p \<in> {..<length T}. L!p \<in> state_set (T!p))}"

  definition
    "product_trans_i =
      {(L,g,a,r,L[p:=l']) | L p g a r l'. L \<in> states \<and> (L!p, g, Sil a, r, l') \<in> T!p \<and> p < length L}"

  definition
    "product_trans_s =
      {(L,g1 @ g2,a,r1 @ r2,L[p:=l1',q:=l2']) | L p q g1 g2 a r1 r2 l1' l2'.
        L \<in> states \<and> (L!p, g1, In a, r1, l1') \<in> T!p \<and> (L!q, g2, Out a, r2, l2') \<in> T!q
        \<and> p < length L \<and> q < length L \<and> p \<noteq> q
      }"

  definition
    "product_trans \<equiv> product_trans_i \<union> product_trans_s"

  definition
    "product_invariant L \<equiv> concat (map (\<lambda> p. if p < length I then (I!p) (L!p) else []) [0..<length L])"

  definition product_ta :: "('a, 'c, 't, 's list) ta" where
    "product_ta \<equiv> (product_trans, product_invariant)"

  lemma collect_clki_product_invariant:
    "collect_clki product_invariant = \<Union> (collect_clki ` set I)"
  unfolding collect_clki_def product_invariant_def
  apply (simp add: image_Union)
  apply auto
  subgoal
    unfolding collect_clock_pairs_def by fastforce
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
       apply (rule exI[where x = ?L])
       apply simp
      apply simp
      using prems
      apply -
      apply (drule aux)
      unfolding collect_clock_pairs_def
      apply auto
      by fastforce
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

  (* XXX Clean *)
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
    subgoal for p'
      apply (cases "p' = p")
      using assms L by (auto simp: states_def)
    done

  context
    assumes states_not_empty: "states \<noteq> {}"
    assumes trans_complete:
      "\<forall> p < length T. \<forall> t1 \<in> T ! p. case t1 of (l1, g1, In a, r1, l1')
      \<Rightarrow> \<exists> q < length T. p \<noteq> q \<and> (\<exists> l2 g2 r2 l2'. (l2, g2, Out a, r2, l2') \<in> T ! q) |
      (l1, g1, Out a, r1, l1')
      \<Rightarrow> \<exists> q < length T. p \<noteq> q \<and> (\<exists> l2 g2 r2 l2'. (l2, g2, In a, r2, l2') \<in> T ! q) | _ \<Rightarrow> True"
  begin

  lemma collect_clkt_product_trans_sups:
    "collect_clkt product_trans \<supseteq> \<Union> (collect_clkt ` set T)"
  proof
    fix x assume "x \<in> \<Union> (collect_clkt ` set T)"
    then obtain trans l1 g1 a' r1 l1' where x:
      "trans \<in> set T" "(l1, g1, a', r1, l1') \<in> trans" "x \<in> collect_clock_pairs g1"
      unfolding collect_clkt_def by force
    then obtain p where p:
        "p < length T" "T ! p = trans"
      by (auto dest!: aux)
    from states_not_empty obtain L where L: "L \<in> states" by auto
    show "x \<in> collect_clkt product_trans"
    proof (cases a')
      case a': (In a)
      with x p trans_complete obtain q l2 g2 r2 l2' where trans2:
        "q < length T" "(l2, g2, Out a, r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      moreover have *: "x \<in> collect_clock_pairs (g1 @ g2)" using x(3) by (auto simp: collect_clock_pairs_def)
      moreover have "L[p := l1, q := l2] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g1 @ g2, a, r1 @ r2, ?L[p := l1', q := l2']) \<in> product_trans_s"
        using p(1) x(1,2) trans2 unfolding p(2)[symmetric] a' product_trans_s_def
        by (fastforce simp: states_length[OF \<open>L \<in> states\<close>])
      with * show ?thesis unfolding collect_clkt_def product_trans_def by force
      (*
        apply clarsimp
        apply (rule exI[where x = "collect_clock_pairs (g1 @ g2)"])
        apply rule
         apply (rule exI[where x = "L[p := l1, q := l2]"])
         apply (rule exI[where x = "g1 @ g2"])
         apply rule
          apply simp
         apply (rule exI[where x = a])
         apply (rule exI[where x = "r1 @ r2"])
         apply (rule exI[where x = "L[p := l1, q := l2, p := l1', q := l2']"])
         apply simp
        unfolding states_length[OF \<open>L \<in> states\<close>]
        using fanc unfolding p(2)[symmetric]
         apply -
         apply (rule disjI2)
        by (fastforce simp: a')+
        *)
    next
      case a': (Out a)
      with x p trans_complete obtain q l2 g2 r2 l2' where trans2:
        "q < length T" "(l2, g2, In a, r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      moreover have *: "x \<in> collect_clock_pairs (g2 @ g1)" using x(3) by (auto simp: collect_clock_pairs_def)
      moreover have "L[q := l2, p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g2 @ g1, a, r2 @ r1, ?L[q := l2', p := l1']) \<in> product_trans_s"
        using p(1) x(1,2) trans2 unfolding p(2)[symmetric] a' product_trans_s_def
        by (fastforce simp: states_length[OF \<open>L \<in> states\<close>])
      with * show ?thesis unfolding collect_clkt_def product_trans_def by force
    next
      case a': (Sil a)
      have "L[p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1"
        using \<open>p < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g1, a, r1, ?L[p := l1']) \<in> product_trans_i"
        using x p unfolding product_trans_i_def a' by (force simp: states_length[OF \<open>L \<in> states\<close>])
      with x(3) show ?thesis unfolding collect_clkt_def product_trans_def by force
    qed
  qed

  lemma collect_clkvt_product_trans_sups:
    "collect_clkvt product_trans \<supseteq> \<Union> (collect_clkvt ` set T)"
  proof
    fix x assume "x \<in> \<Union> (collect_clkvt ` set T)"
    then obtain trans l1 g1 a' r1 l1' where x:
      "trans \<in> set T" "(l1, g1, a', r1, l1') \<in> trans" "x \<in> set r1"
      unfolding collect_clkvt_def by force
    then obtain p where p:
        "p < length T" "T ! p = trans"
      by (auto dest!: aux)
    from states_not_empty obtain L where L: "L \<in> states" by auto
    show "x \<in> collect_clkvt product_trans"
    proof (cases a')
      case a': (In a)
      with x p trans_complete obtain q l2 g2 r2 l2' where trans2:
        "q < length T" "(l2, g2, Out a, r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      moreover have "L[p := l1, q := l2] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g1 @ g2, a, r1 @ r2, ?L[p := l1', q := l2']) \<in> product_trans_s"
        using p(1) x trans2 unfolding p(2)[symmetric] a' product_trans_s_def
        by (fastforce simp: states_length[OF \<open>L \<in> states\<close>])
      with x(3) show ?thesis unfolding collect_clkvt_def product_trans_def by force
    next
      case a': (Out a)
      with x p trans_complete obtain q l2 g2 r2 l2' where trans2:
        "q < length T" "(l2, g2, In a, r2, l2') \<in> T ! q" "p \<noteq> q"
        by atomize_elim fastforce
      moreover have "L[q := l2, p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) trans2 unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1" "?L ! q = l2"
        using \<open>p \<noteq> q\<close> \<open>p < length T\<close> \<open>q < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g2 @ g1, a, r2 @ r1, ?L[q := l2', p := l1']) \<in> product_trans_s"
        using p(1) x trans2 unfolding p(2)[symmetric] a' product_trans_s_def
        by (fastforce simp: states_length[OF \<open>L \<in> states\<close>])
      with x(3) show ?thesis unfolding collect_clkvt_def product_trans_def by force
    next
      case a': (Sil a)
      have "L[p := l1] \<in> states" (is "?L \<in> _")
        using L p(1) x(1,2) unfolding p(2)[symmetric] by (auto intro!: statesI_aux)
      moreover have "?L ! p = l1"
        using \<open>p < length T\<close> \<open>L \<in> states\<close> by (auto dest: states_length)
      ultimately have "(?L, g1, a, r1, ?L[p := l1']) \<in> product_trans_i"
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
    let ?S = "{(L, p, g, a, r, l')|L p g a r l'.
      L \<in> states \<and> (L ! p, g, Sil a, r, l') \<in> map trans_of N ! p \<and> p < length L}"
    let ?R = "{(L, p, g, a, r, l')|L p g a r l'.
      L \<in> states \<and> p < length L \<and> (g, Sil a, r, l') \<in> snd ` ?N}"
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
      subgoal for a aa ab ac b L p g ad r l'
        apply (rule image_eqI[where x = "(L, p, g, ad, r, l')"])
        by auto
      by force
    ultimately show ?thesis by auto
  qed

  lemma finite_product_trans_s:
    "finite product_trans_s"
  proof -
    let ?N = "\<Union> (trans_of ` set N)"
    let ?S = "{(L, p, q, g1, g2, a, r1, r2, l1', l2')|L p q g1 g2 a r1 r2 l1' l2'.
      L \<in> states \<and> (L ! p, g1, In a, r1, l1') \<in> map trans_of N ! p \<and>
        (L ! q, g2, Out a, r2, l2') \<in> map trans_of N ! q \<and> p < length L \<and> q < length L}"
    (*
    let ?R = "{(L, p, q, g1, a, r1, l1', g2, b, r2, l2')|L p q g1 a r1 l1' g2 b r2 l2'.
      L \<in> states \<and> p < length L \<and> q < length L \<and> (g1, In a, r1, l1') \<in> snd ` ?N \<and> (g2, Out b, r2, l2') \<in> snd ` ?N}"
     have "finite ?R" using finite_states
      using [[simproc add: finite_Collect]]
      apply simp
    *)
    let ?R = "{(L, p, q, g1, g2, a, r1, r2, l1', l2')|L p q g1 g2 a r1 r2 l1' l2'.
      L \<in> states \<and> p < length L \<and> q < length L \<and> (g1, In a, r1, l1') \<in> snd ` ?N \<and> (g2, Out a, r2, l2') \<in> snd ` ?N}"
    have "?S \<subseteq> ?R" by (fastforce simp: states_length dest: nth_mem)
    moreover have "finite ?R" using finite_states
      using [[simproc add: finite_Collect]]
      apply -
      apply simp
      sorry
    (*
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
      by (auto; fail) *)
    ultimately have "finite ?S" by (rule finite_subset)
    moreover have "product_trans_s \<subseteq> (\<lambda> (L, p, q, g1, g2, a, r1, r2, l1', l2'). (L, g1 @ g2, a, r1 @ r2, L[p := l1', q := l2'])) ` ?S"
      unfolding product_trans_s_def apply (rule)
       apply simp
       apply safe[]
      subgoal for a aa ab ac b L p q g1 g2 ad r1 r2 l1' l2'
        apply (rule image_eqI[where x = "(L, p, q, g1, g2, ad, r1, r2, l1', l2')"])
        by auto
      done
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
  Product_TA_Defs N for N :: "('a, 'c, 't :: time, 's) nta"
begin

  lemma product_invariantD:
    assumes "u \<turnstile> product_invariant L" "p < length N" "length L = length N"
    shows "u \<turnstile> inv_of (N ! p) (L!p)"
  using assms unfolding product_invariant_def by (force intro: concat_guard)

end

(* Network + valid start state *)
locale Product_TA =
  Product_TA_Defs' N for N :: "('a, 'c, 't :: time, 's) nta" +
  fixes L :: "'s list"
  assumes len[simp]: "length L = length N"
      and states[intro]: "L \<in> states"
begin

  lemma product_complete:
    assumes step: "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    shows "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
  using step proof cases
    case prems: (step_n_t d)
    from prems(3) have *:
      "\<forall>p\<in>{..<length N}. u \<turnstile> inv_of (N ! p) (L ! p)"
      "\<forall>p\<in>{..<length N}. u \<oplus> d \<turnstile> inv_of (N ! p) (L ! p)"
    by auto
    from prems(1,2,4) * show ?thesis
    by (fastforce simp add: product_ta_def inv_of_def product_invariant_def[abs_def]
                  intro!: guard_concat
       )
  next
    case prems: (step_n_i p l g a r l')
    from prems show ?thesis
     apply -
     apply (rule step_a; rule step_a.intros[where g = g and r = r and a = a])
    by (fastforce
        simp: product_trans_def product_trans_i_def product_invariant_def product_ta_def
              trans_of_def inv_of_def
        intro: guard_concat
       )+
  next
    case prems: (step_n_s p l1 g1 a r1 l1' q l2 g2 r2 l2')
    from prems show ?thesis
     apply -
     apply (rule step_a; rule step_a.intros[where g = "g1 @ g2" and a = a and r = "r1 @ r2"])
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

  lemma product_ta_cases:
    assumes "product_ta \<turnstile> L \<longrightarrow>\<^bsup>g,a,r\<^esup> L'"
    shows "(L, g, a, r, L') \<in> product_trans_i \<or> (L, g, a, r, L') \<in> product_trans_s"
  using assms unfolding product_ta_def trans_of_def product_trans_def by auto

  lemma product_sound:
    assumes step: "product_ta \<turnstile> \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
    shows "N \<turnstile>\<^sub>N \<langle>L, u\<rangle> \<rightarrow> \<langle>L', u'\<rangle>"
  using assms proof cases
    case (step_t d)
    then show ?thesis by (auto intro!: step_n_t product_invariantD len)
  next
    case (step_a a)
    then show ?thesis
     apply cases
     apply simp
     apply (drule product_ta_cases)
     apply (erule disjE)
     unfolding product_trans_i_def product_trans_s_def
      apply (auto intro: product_invariantD intro!: step_n_i; fail)
    by (auto intro: product_invariantD intro!: step_n_s)
  qed

  end (* End context: network + valid start state *)

end (* End of theory *)